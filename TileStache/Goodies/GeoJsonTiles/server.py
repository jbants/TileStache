''' Provider that returns PostGIS vector tiles in GeoJSON or MVT format.

VecTiles is intended for rendering, and returns tiles with contents simplified,
precision reduced and often clipped. The MVT format in particular is designed
for use in Mapnik with the VecTiles Datasource, which can read binary MVT tiles.

For a more general implementation, try the Vector provider:
    http://tilestache.org/doc/#vector-provider
'''
from math import pi

try:
    from urllib.parse import urljoin, urlparse
except ImportError:
    # Python 2
    from urlparse import urljoin, urlparse
try:
    from urllib.request import urlopen
except ImportError:
    # Python 2
    from urllib import urlopen
from os.path import exists

try:
    from psycopg2.extras import RealDictCursor
    from psycopg2 import connect
    from psycopg2.extensions import TransactionRollbackError

except ImportError as err:
    # Still possible to build the documentation without psycopg2

    def connect(*args, **kwargs):
        raise err

import json
from functools import partial
import pyproj
from json import loads as json_loads
from shapely.geometry import shape
from shapely.ops import transform
from osgeo import ogr, osr

from . import mvt, geojson, topojson, pbf
from ...Geography import SphericalMercator, getProjectionByName
from ...Core import KnownUnknown
from ModestMaps.Core import Point

tolerances = [6378137 * 2 * pi / (2 ** (zoom + 8)) for zoom in range(20)]


class Provider:
    ''' VecTiles provider for PostGIS data sources.

        Parameters:

          dbinfo:
            Required dictionary of Postgres connection parameters. Should
            include some combination of 'host', 'user', 'password', and 'database'.

          queries:
            Required list of Postgres queries, one for each zoom level. The
            last query in the list is repeated for higher zoom levels, and null
            queries indicate an empty response.

            Query must use "__geometry__" for a column name, and must be in
            spherical mercator (900913) projection. A query may include an
            "__id__" column, which will be used as a feature ID in GeoJSON
            instead of a dynamically-generated hash of the geometry. A query
            can additionally be a file name or URL, interpreted relative to
            the location of the TileStache config file.

            If the query contains the token "!bbox!", it will be replaced with
            a constant bounding box geomtry like this:
            "ST_SetSRID(ST_MakeBox2D(ST_MakePoint(x, y), ST_MakePoint(x, y)), <srid>)"

            This behavior is modeled on Mapnik's similar bbox token feature:
            https://github.com/mapnik/mapnik/wiki/PostGIS#bbox-token

          clip:
            Optional boolean flag determines whether geometries are clipped to
            tile boundaries or returned in full. Default true: clip geometries.

          padding:
            Optional number of pixels for applying a padding in the !bbox! token.
            Useful if you want some buffer (common areas) between the tiles.
            Default 0.

          srid:
            Optional numeric SRID used by PostGIS for spherical mercator.
            Default 900913.

          simplify:
            Optional floating point number of pixels to simplify all geometries.
            Useful for creating double resolution (retina) tiles set to 0.5, or
            set to 0.0 to prevent any simplification. Default 1.0.

          simplify_until:
            Optional integer specifying a zoom level where no more geometry
            simplification should occur. Default 16.

        Sample configuration, for a layer with no results at zooms 0-9, basic
        selection of lines with names and highway tags for zoom 10, a remote
        URL containing a query for zoom 11, and a local file for zooms 12+:

          "provider":
          {
            "class": "TileStache.Goodies.VecTiles:Provider",
            "kwargs":
            {
              "dbinfo":
              {
                "host": "localhost",
                "user": "gis",
                "password": "gis",
                "database": "gis"
              },
              "queries":
              [
                null, null, null, null, null,
                null, null, null, null, null,
                "SELECT way AS __geometry__, highway, name FROM planet_osm_line -- zoom 10+ ",
                "http://example.com/query-z11.pgsql",
                "query-z12-plus.pgsql"
              ]
            }
          }

        The queries field has an alternate dictionary-like syntax which maps
        zoom levels to their associated query.  Zoom levels for which there is
        no query may be omitted and are assumed null.  This is equivalent to
        the queries defined above:

              "queries": {
                "10": "SELECT way AS __geometry__, highway, name FROM planet_osm_line -- zoom 10+ ",
                "11": "http://example.com/query-z11.pgsql",
                "12": "query-z12-plus.pgsql"
              }

        Note that JSON requires keys to be strings, therefore the zoom levels
        must be enclosed in quotes.
    '''

    def __init__(self, layer, dbinfo, queries, clip=True, srid=900913, simplify=1.0, simplify_until=16, padding=0):
        '''
        '''
        self.layer = layer

        keys = 'host', 'user', 'password', 'database', 'port', 'dbname'
        self.dbinfo = dict([(k, v) for (k, v) in dbinfo.items() if k in keys])

        self.clip = bool(clip)
        self.srid = int(srid)
        self.simplify = float(simplify)
        self.simplify_until = int(simplify_until)
        self.padding = int(padding)
        self.columns = {}

        # Each type creates an iterator yielding tuples of:
        # (zoom level (int), query (string))
        if isinstance(queries, dict):
            # Add 1 to include space for zoom level 0
            n_zooms = max(int(z) for z in queries) + 1
            queryiter = ((int(z), q) for z, q in queries.iteritems())
        else:  # specified as array
            n_zooms = len(queries)
            queryiter = enumerate(queries)

        # For the dict case, unspecified zoom levels are assumed to be null.
        self.queries = [None] * n_zooms
        for z, query in queryiter:
            if query is None:
                continue

            #
            # might be a file or URL?
            #
            url = urljoin(layer.config.dirpath, query)
            scheme, h, path, p, q, f = urlparse(url)

            if scheme in ('file', '') and exists(path):
                query = open(path).read()

            elif scheme == 'http' and ' ' not in url:
                query = urlopen(url).read()

            self.queries[z] = query

    def renderTile(self, width, height, srs, coord):
        ''' Render a single tile, return a Response instance.
        '''
        try:
            query = self.queries[coord.zoom]
        except IndexError:
            query = self.queries[-1]

        ll = self.layer.projection.coordinateProj(coord.down())
        ur = self.layer.projection.coordinateProj(coord.right())
        bounds = ll.x, ll.y, ur.x, ur.y

        if not query:
            return EmptyResponse(bounds)

        if query not in self.columns:
            self.columns[query] = query_columns(self.dbinfo, self.srid, query, bounds)

        if not self.columns[query]:
            return EmptyResponse(bounds)

        tolerance = self.simplify * tolerances[coord.zoom] if coord.zoom < self.simplify_until else None

        return Response(self.dbinfo, self.srid, query, self.columns[query], bounds, tolerance, coord.zoom, self.clip,
                        coord, self.layer.name(), self.padding)

    def getTypeByExtension(self, extension):
        ''' Get mime-type and format by file extension, one of "mvt", "json", "topojson" or "pbf".
        '''
        if extension.lower() == 'mvt':
            return 'application/octet-stream+mvt', 'MVT'

        elif extension.lower() == 'json':
            return 'application/json', 'JSON'

        elif extension.lower() == 'topojson':
            return 'application/json', 'TopoJSON'

        elif extension.lower() == 'pbf':
            return 'application/x-protobuf', 'PBF'

        else:
            raise ValueError(extension)


class MultiProvider:
    ''' VecTiles provider to gather PostGIS tiles into a single multi-response.

        Returns a MultiResponse object for GeoJSON or TopoJSON requests.

        names:
          List of names of vector-generating layers from elsewhere in config.

        Sample configuration, for a layer with combined data from water
        and land areas, both assumed to be vector-returning layers:

          "provider":
          {
            "class": "TileStache.Goodies.VecTiles:MultiProvider",
            "kwargs":
            {
              "names": ["water-areas", "land-areas"]
            }
          }
    '''

    def __init__(self, layer, names):
        self.layer = layer
        self.names = names

    def renderTile(self, width, height, srs, coord):
        ''' Render a single tile, return a Response instance.
        '''
        return MultiResponse(self.layer.config, self.names, coord)

    def getTypeByExtension(self, extension):
        ''' Get mime-type and format by file extension, "json", "topojson" or "pbf" only.
        '''
        if extension.lower() == 'json':
            return 'application/json', 'JSON'

        elif extension.lower() == 'topojson':
            return 'application/json', 'TopoJSON'

        elif extension.lower() == 'pbf':
            return 'application/x-protobuf', 'PBF'

        else:
            raise ValueError(extension)


class GeoJsonProvider:
    """
     VecTiles provider for GeoJSON data sources.
    """

    def __init__(self, layer, driver, parameters, clipped, verbose, projected, spacing, properties, precision,
                 id_property, skip_empty_fields=False):
        self.layer      = layer
        self.driver     = driver
        self.clipped    = clipped
        self.verbose    = verbose
        self.projected  = projected
        self.spacing    = spacing
        self.parameters = parameters
        self.properties = properties
        self.precision  = precision
        self.id_property = id_property
        self.skip_empty_fields = skip_empty_fields

    @staticmethod
    def prepareKeywordArgs(config_dict):
        """ Convert configured parameters to keyword args for __init__().
        """
        kwargs = dict()

        kwargs['driver'] = config_dict['driver']
        kwargs['parameters'] = config_dict['parameters']
        kwargs['id_property'] = config_dict.get('id_property', None)
        kwargs['properties'] = config_dict.get('properties', None)
        kwargs['projected'] = bool(config_dict.get('projected', False))
        kwargs['verbose'] = bool(config_dict.get('verbose', False))
        kwargs['precision'] = int(config_dict.get('precision', 6))
        kwargs['skip_empty_fields'] = bool(config_dict.get('skip_empty_fields', False))

        if 'spacing' in config_dict:
            kwargs['spacing'] = float(config_dict.get('spacing', 0.0))
        else:
            kwargs['spacing'] = None

        if config_dict.get('clipped', None) == 'padded':
            kwargs['clipped'] = 'padded'
        else:
            kwargs['clipped'] = bool(config_dict.get('clipped', True))

        return kwargs

    def renderTile(self, width, height, srs, coord):
        ''' Render a single tile, return a Response instance.
        '''

        ll = self.layer.projection.coordinateProj(coord.down())
        ur = self.layer.projection.coordinateProj(coord.right())
        bounds = ll.x, ll.y, ur.x, ur.y

        layer, ds = _open_layer(self.driver, self.parameters, self.layer.config.dirpath)
        features = _get_features(coord, self.properties, self.layer.projection, layer, self.clipped, self.projected,
                                 self.spacing, self.id_property, self.skip_empty_fields)
        response = {'type': 'FeatureCollection', 'features': features}

        if self.projected:
            sref = osr.SpatialReference()
            sref.ImportFromProj4(self.layer.projection.srs)
            response['crs'] = {'wkt': sref.ExportToWkt()}

            if srs == getProjectionByName('spherical mercator').srs:
                response['crs']['wkid'] = 102113
        else:
            response['crs'] = {'srid': 4326, 'wkid': 4326}

        return GeoJsonResponse(response, self.verbose, coord, bounds, self.precision, self.layer.name())

    def getTypeByExtension(self, extension):
        ''' Get mime-type and format by file extension, one of "mvt", "json", "topojson" or "pbf".
        '''
        if extension.lower() == 'mvt':
            return 'application/octet-stream+mvt', 'MVT'

        elif extension.lower() == 'json':
            return 'application/json', 'JSON'

        elif extension.lower() == 'topojson':
            return 'application/json', 'TopoJSON'

        elif extension.lower() == 'pbf':
            return 'application/x-protobuf', 'PBF'

        else:
            raise ValueError(extension)


class GeoJsonResponse:
    '''
    '''

    def __init__(self, content, verbose, coord, bounds, precision=6, layer_name=''):
        ''' Create a new response object from a geojson file.

            bounds argument is a 4-tuple with (xmin, ymin, xmax, ymax).
        '''
        self.content = content
        self.verbose = verbose
        self.precision = precision
        self.coord = coord
        self.bounds = bounds
        self.layer_name = layer_name

    def save(self, out, format):
        '''
        '''

        feature_collection =self.content['features']

        features = []

        for index, feature in enumerate(feature_collection):
            shapely_geom = shape(feature['geometry'])

            project = partial(
                pyproj.transform,
                pyproj.Proj(init='epsg:4326'),  # source coordinate system
                pyproj.Proj(init='epsg:3857'))  # destination coordinate system

            shapely_geom_web_mercator = transform(project, shapely_geom)
            
            prop = feature['properties']
            wkb = shapely_geom_web_mercator
            fid = index

            features.append((wkb, prop, fid))

        if format == 'MVT':
            mvt.encode(out, features)

        elif format == 'JSON':
            geojson.encode(out, features, self.zoom, self.clip)

        elif format == 'TopoJSON':
            ll = SphericalMercator().projLocation(Point(*self.bounds[0:2]))
            ur = SphericalMercator().projLocation(Point(*self.bounds[2:4]))
            topojson.encode(out, features, (ll.lon, ll.lat, ur.lon, ur.lat), self.clip)

        elif format == 'PBF':
            pbf.encode(
                out, features, self.bounds, layer_name=self.layer_name)

        else:
            raise ValueError(format)


class EmptyResponse:
    ''' Simple empty response renders valid MVT, GeoJSON, TopoJSON or PBF with no features.
    '''

    def __init__(self, bounds):
        self.bounds = bounds

    def save(self, out, format):
        '''
        '''
        if format == 'MVT':
            mvt.encode(out, [])

        elif format == 'JSON':
            geojson.encode(out, [], 0, False)

        elif format == 'TopoJSON':
            ll = SphericalMercator().projLocation(Point(*self.bounds[0:2]))
            ur = SphericalMercator().projLocation(Point(*self.bounds[2:4]))
            topojson.encode(out, [], (ll.lon, ll.lat, ur.lon, ur.lat), False)

        elif format == 'PBF':
            pbf.encode(out, [], self.bounds, None)

        else:
            raise ValueError(format)


def get_features(dbinfo, query, n_try=1):
    features = []

    with Connection(dbinfo) as db:
        try:
            db.execute(query)
        except TransactionRollbackError:
            if n_try >= 5:
                raise
            else:
                return get_features(dbinfo, query, n_try=n_try + 1)
        for row in db.fetchall():
            assert '__geometry__' in row, 'Missing __geometry__ in feature result'
            assert '__id__' in row, 'Missing __id__ in feature result'

            wkb = bytes(row.pop('__geometry__'))
            id = row.pop('__id__')

            props = dict((k, v) for k, v in row.items() if v is not None)

            features.append((wkb, props, id))

    return features


def _sref_4326():
    """
    """
    sref = osr.SpatialReference()
    proj = getProjectionByName('WGS84')
    sref.ImportFromProj4(proj.srs)

    return sref


def _append_with_delim(s, delim, data, key):
    if key in data:
        return s + delim + str(data[key])
    else:
        return s


def _open_layer(driver_name, parameters, dirpath):
    """ Open a layer, return it and its datasource.

        Dirpath comes from configuration, and is used to locate files.
    """
    #
    # Set up the driver
    #
    okay_drivers = {'geojson': 'GeoJSON'}

    if driver_name.lower() not in okay_drivers:
        raise KnownUnknown('Got a driver type Vector doesn\'t understand: "%s". Need one of %s.' % (
            driver_name, ', '.join(okay_drivers.keys())))

    driver_name = okay_drivers[driver_name.lower()]
    driver = ogr.GetDriverByName(str(driver_name))

    #
    # Set up the datasource
    #

    if driver_name in ('GeoJSON',):
        if 'file' not in parameters:
            raise KnownUnknown('Need a "file" parameter')

        source_name = parameters['file']

    datasource = driver.Open(str(source_name))

    if datasource is None:
        raise KnownUnknown('Couldn\'t open datasource %s' % source_name)

    #
    # Set up the layer
    #
    layer = datasource.GetLayer(0)

    #
    # Return the layer and the datasource.
    #
    # Technically, the datasource is no longer needed
    # but layer segfaults when it falls out of scope.
    #
    return layer, datasource


def _get_features(coord, properties, projection, layer, clipped, projected, spacing, id_property,
                  skip_empty_fields=False):
    """ Return a list of features in an OGR layer with properties in GeoJSON form.

        Optionally clip features to coordinate bounding box, and optionally
        limit returned features to only those separated by number of pixels
        given as spacing.
    """
    #
    # Prepare output spatial reference - always WGS84.
    #
    if projected:
        output_sref = osr.SpatialReference()
        output_sref.ImportFromProj4(projection.srs)
    else:
        output_sref = _sref_4326()

    #
    # Load layer information
    #
    definition = layer.GetLayerDefn()
    layer_sref = layer.GetSpatialRef()
    if layer_sref == None:
        layer_sref = _sref_4326()

    #
    # Spatially filter the layer
    #
    bbox = _tile_perimeter_geom(coord, projection, clipped == 'padded')
    bbox.TransformTo(layer_sref)
    layer.SetSpatialFilter(bbox)

    features = []
    mask = None

    if spacing is not None:
        buffer = spacing * _tile_perimeter_width(coord, projection) / 256.

    for feature in layer:
        geometry = feature.geometry().Clone()

        if not geometry.Intersect(bbox):
            continue

        if mask and geometry.Intersect(mask):
            continue

        if clipped:
            geometry = geometry.Intersection(bbox)

        if geometry is None:
            # may indicate a TopologyException
            continue

        # mask out subsequent features if spacing is defined
        if mask and buffer:
            mask = geometry.Buffer(buffer, 2).Union(mask)
        elif spacing is not None:
            mask = geometry.Buffer(buffer, 2)

        geometry.AssignSpatialReference(layer_sref)
        geometry.TransformTo(output_sref)

        geom = json_loads(geometry.ExportToJson())
        prop = _feature_properties(feature, definition, properties, skip_empty_fields)

        geojson_feature = {'type': 'Feature', 'properties': prop, 'geometry': geom}
        if id_property != None and id_property in prop:
            geojson_feature['id'] = prop[id_property]
        features.append(geojson_feature)

    return features


def _tile_perimeter(coord, projection, padded):
    """ Get a tile's outer edge for a coordinate and a projection.

        Returns a list of 17 (x, y) coordinates corresponding to a clockwise
        circumambulation of a tile boundary in a given projection. Projection
        is like those found in TileStache.Geography, used for tile output.

        If padded argument is True, pad bbox by 5% on all sides.
    """
    if padded:
        ul = projection.coordinateProj(coord.left(0.05).up(0.05))
        lr = projection.coordinateProj(coord.down(1.05).right(1.05))
    else:
        ul = projection.coordinateProj(coord)
        lr = projection.coordinateProj(coord.right().down())

    xmin, ymin, xmax, ymax = ul.x, ul.y, lr.x, lr.y
    xspan, yspan = xmax - xmin, ymax - ymin

    perimeter = [
        (xmin, ymin),
        (xmin + 1 * xspan / 4, ymin),
        (xmin + 2 * xspan / 4, ymin),
        (xmin + 3 * xspan / 4, ymin),
        (xmax, ymin),
        (xmax, ymin + 1 * yspan / 4),
        (xmax, ymin + 2 * yspan / 4),
        (xmax, ymin + 3 * yspan / 4),
        (xmax, ymax),
        (xmax - 1 * xspan / 4, ymax),
        (xmax - 2 * xspan / 4, ymax),
        (xmax - 3 * xspan / 4, ymax),
        (xmin, ymax),
        (xmin, ymax - 1 * yspan / 4),
        (xmin, ymax - 2 * yspan / 4),
        (xmin, ymax - 3 * yspan / 4),
        (xmin, ymin)
    ]

    return perimeter


def _tile_perimeter_width(coord, projection):
    """ Get the width in projected coordinates of the coordinate tile polygon.

        Uses _tile_perimeter().
    """
    perimeter = _tile_perimeter(coord, projection, False)
    return perimeter[8][0] - perimeter[0][0]


def _tile_perimeter_geom(coord, projection, padded):
    """ Get an OGR Geometry object for a coordinate tile polygon.

        Uses _tile_perimeter().
    """
    perimeter = _tile_perimeter(coord, projection, padded)
    wkt = 'POLYGON((%s))' % ', '.join(['%.7f %.7f' % xy for xy in perimeter])
    geom = ogr.CreateGeometryFromWkt(wkt)

    ref = osr.SpatialReference()
    ref.ImportFromProj4(projection.srs)
    geom.AssignSpatialReference(ref)

    return geom


def _feature_properties(feature, layer_definition, whitelist=None, skip_empty_fields=False):
    """ Returns a dictionary of feature properties for a feature in a layer.

        Third argument is an optional list or dictionary of properties to
        whitelist by case-sensitive name - leave it None to include everything.
        A dictionary will cause property names to be re-mapped.

        OGR property types:
        OFTInteger (0), OFTIntegerList (1), OFTReal (2), OFTRealList (3),
        OFTString (4), OFTStringList (5), OFTWideString (6), OFTWideStringList (7),
        OFTBinary (8), OFTDate (9), OFTTime (10), OFTDateTime (11).

        Extra OGR types for GDAL 2.x:
        OFTInteger64 (12), OFTInteger64List (13)
    """
    properties = {}
    okay_types = [ogr.OFTInteger, ogr.OFTReal, ogr.OFTString,
                  ogr.OFTWideString, ogr.OFTDate, ogr.OFTTime, ogr.OFTDateTime]
    if hasattr(ogr, 'OFTInteger64'):
        okay_types.extend([ogr.OFTInteger64, ogr.OFTInteger64List])

    for index in range(layer_definition.GetFieldCount()):
        field_definition = layer_definition.GetFieldDefn(index)
        field_type = field_definition.GetType()

        name = field_definition.GetNameRef()

        if type(whitelist) in (list, dict) and name not in whitelist:
            continue

        if field_type not in okay_types:
            try:
                name = [oft for oft in dir(ogr) if oft.startswith('OFT') and getattr(ogr, oft) == field_type][0]
            except IndexError:
                raise KnownUnknown("Found an OGR field type I've never even seen: %d" % field_type)
            else:
                raise KnownUnknown("Found an OGR field type I don't know what to do with: ogr.%s" % name)

        if not skip_empty_fields or feature.IsFieldSet(name):
            property = type(whitelist) is dict and whitelist[name] or name
            properties[property] = feature.GetField(name)

    return properties