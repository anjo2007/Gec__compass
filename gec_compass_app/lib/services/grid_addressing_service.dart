import 'dart:math';
import 'package:latlong2/latlong.dart';

class GridAddressingService {
  // GEC Thrissur SW Anchor Point (Origin for campus grid reference)
  static const double swLat = 10.5500;
  static const double swLng = 76.2150;
  static const double gridCellSizeMeters = 10.0;

  // GEC Thrissur Campus Geodesic Bounding Box (Lat/Lng)
  static const double campusMinLat = 10.5480;
  static const double campusMaxLat = 10.5620;
  static const double campusMinLng = 76.2150;
  static const double campusMaxLng = 76.2360;

  /// Computes high-precision point-to-point distance in meters (Haversine/Geodesic)
  static double computeDistanceMeters(LatLng p1, LatLng p2) {
    const double r = 6371000.0; // Earth radius in meters
    final double dLat = _toRadians(p2.latitude - p1.latitude);
    final double dLng = _toRadians(p2.longitude - p1.longitude);

    final double a = sin(dLat / 2) * sin(dLat / 2) +
        cos(_toRadians(p1.latitude)) *
            cos(_toRadians(p2.latitude)) *
            sin(dLng / 2) *
            sin(dLng / 2);

    final double c = 2 * atan2(sqrt(a), sqrt(1 - a));
    return r * c;
  }

  /// Checks if a position is within the physical GEC Thrissur campus grid envelope
  static bool isInsideCampusGrid(LatLng point) {
    return point.latitude >= campusMinLat &&
        point.latitude <= campusMaxLat &&
        point.longitude >= swLng &&
        point.longitude <= campusMaxLng;
  }

  /// Generates a standard campus grid address string (e.g., GEC-E074-N052)
  static String getCampusGridAddress(LatLng point) {
    final double latDist = computeDistanceMeters(LatLng(swLat, point.longitude), point);
    final double lngDist = computeDistanceMeters(LatLng(point.latitude, swLng), point);

    final int eastingIndex = (lngDist / gridCellSizeMeters).floor();
    final int northingIndex = (latDist / gridCellSizeMeters).floor();

    return "GEC-E${eastingIndex.toString().padLeft(3, '0')}-N${northingIndex.toString().padLeft(3, '0')}";
  }

  /// Generates a high-precision campus grid address string (e.g., GEC-E074.452-N052.819)
  /// Supporting customizable decimal places (default: 3 decimals = ~1 centimeter resolution).
  static String getPrecisionGridAddress(LatLng point, {int decimals = 3}) {
    final double latDist = computeDistanceMeters(LatLng(swLat, point.longitude), point);
    final double lngDist = computeDistanceMeters(LatLng(point.latitude, swLng), point);

    final double eVal = lngDist / gridCellSizeMeters;
    final double nVal = latDist / gridCellSizeMeters;

    final int padWidth = 4 + decimals;
    return "GEC-E${eVal.toStringAsFixed(decimals).padLeft(padWidth, '0')}-N${nVal.toStringAsFixed(decimals).padLeft(padWidth, '0')}";
  }

  /// Snaps a floating coordinate to the nearest geodesic grid quantization step
  /// to eliminate GPS/PDR micro-jitter while preserving true trajectory geometry.
  static LatLng snapToCampusGrid(LatLng point, {double resolutionMeters = 1.0}) {
    final double latDist = computeDistanceMeters(LatLng(swLat, point.longitude), point);
    final double lngDist = computeDistanceMeters(LatLng(point.latitude, swLng), point);

    final double snappedLatDist = (latDist / resolutionMeters).round() * resolutionMeters;
    final double snappedLngDist = (lngDist / resolutionMeters).round() * resolutionMeters;

    const double r = 6371000.0;
    final double dLat = snappedLatDist / r;
    final double targetLat = swLat + (dLat * 180.0 / pi);

    final double dLng = snappedLngDist / (r * cos(_toRadians(targetLat)));
    final double targetLng = swLng + (dLng * 180.0 / pi);

    return LatLng(targetLat, targetLng);
  }

  /// Decodes a custom campus grid address string (e.g., GEC-E074-N052, E074-N052, E74 N52, or GEC-E074.4-N052.8) back into LatLng.
  static LatLng? getLatLngFromGridAddress(String address) {
    final clean = address.trim().toUpperCase();
    final regex = RegExp(r'^(?:GEC[\s\-_]*)?E(\d+(?:\.\d+)?)[,\s\-_]+N(\d+(?:\.\d+)?)$|^(?:GEC[\s\-_]*)?E(\d+(?:\.\d+)?)-N(\d+(?:\.\d+)?)$');
    final match = regex.firstMatch(clean);
    if (match == null) return null;

    final String eStr = match.group(1) ?? match.group(3)!;
    final String nStr = match.group(2) ?? match.group(4)!;

    final double? parsedE = double.tryParse(eStr);
    final double? parsedN = double.tryParse(nStr);
    if (parsedE == null || parsedN == null) return null;

    // If an integer grid cell (no decimal point) is passed, center the point inside the 10m grid cell (+0.5 * cell size)
    // for optimal geodesic accuracy. If sub-meter precision decimals are passed, decode directly.
    final bool isIntegerE = !eStr.contains('.');
    final bool isIntegerN = !nStr.contains('.');

    final double effectiveE = isIntegerE ? (parsedE + 0.5) : parsedE;
    final double effectiveN = isIntegerN ? (parsedN + 0.5) : parsedN;

    final double lngDist = effectiveE * gridCellSizeMeters;
    final double latDist = effectiveN * gridCellSizeMeters;

    const double r = 6371000.0;

    // Reverse Geodesic projection
    final double dLat = latDist / r;
    final double targetLat = swLat + (dLat * 180.0 / pi);

    final double dLng = lngDist / (r * cos(_toRadians(targetLat)));
    final double targetLng = swLng + (dLng * 180.0 / pi);

    return LatLng(targetLat, targetLng);
  }

  /// Calculates geodesic azimuth/bearing in degrees (0..360) from p1 to p2
  static double calculateGridBearing(LatLng p1, LatLng p2) {
    final double lat1 = _toRadians(p1.latitude);
    final double lat2 = _toRadians(p2.latitude);
    final double dLng = _toRadians(p2.longitude - p1.longitude);

    final double y = sin(dLng) * cos(lat2);
    final double x = cos(lat1) * sin(lat2) - sin(lat1) * cos(lat2) * cos(dLng);
    return (atan2(y, x) * 180.0 / pi + 360.0) % 360.0;
  }

  static double _toRadians(double degree) => degree * pi / 180.0;
}
