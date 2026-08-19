import 'dart:async';
import 'dart:convert';
import 'dart:math';
import 'dart:ui';
import 'package:flutter/foundation.dart' show kIsWeb, defaultTargetPlatform, TargetPlatform;
import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:flutter_map/flutter_map.dart';
import 'package:latlong2/latlong.dart' hide Path;
import 'package:geolocator/geolocator.dart';
import 'package:permission_handler/permission_handler.dart' as ph;
import 'package:flutter_tts/flutter_tts.dart';
import 'package:image_picker/image_picker.dart';
import 'package:shared_preferences/shared_preferences.dart';
import '../models/building.dart';
import '../services/data_service.dart';
import '../services/pdr_service.dart';
import '../services/routing_service.dart';
import 'package:url_launcher/url_launcher.dart';
import 'package:share_plus/share_plus.dart';
import 'vps_camera_screen.dart';
import 'floor_mapping_screen.dart';
import '../services/place_detection_service.dart';
import '../widgets/gradient_loading_indicator.dart';
import '../widgets/embedded_feedback_modal.dart';
import '../widgets/top_message_overlay.dart';
import '../services/app_update_service.dart';
import '../widgets/update_available_dialog.dart';
import '../services/grid_addressing_service.dart';
import '../services/vps_sensor_fusion.dart';
import '../services/vps_relocalization_service.dart';

class TelemetryData {
  final double heading;
  final double accelX;
  final double accelY;
  final double accelZ;
  final double accelMag;
  final List<double> magHistory;
  final double altitude;

  TelemetryData({
    required this.heading,
    required this.accelX,
    required this.accelY,
    required this.accelZ,
    required this.accelMag,
    required this.magHistory,
    required this.altitude,
  });
}

class MapScreen extends StatefulWidget {
  const MapScreen({super.key});

  @override
  State<MapScreen> createState() => _MapScreenState();
}

class _MapScreenState extends State<MapScreen> with TickerProviderStateMixin, WidgetsBindingObserver {
  final MapController _mapController = MapController();
  final DataService _dataService = DataService();
  final PDRService _pdrService = PDRService();
  final RoutingService _routingService = RoutingService();

  double _currentZoom = 16.8;
  int _lastRouteClosestIndex = -1;
  late final ValueNotifier<TelemetryData> _telemetryNotifier;

  // Position ValueNotifier — updates user marker without full tree rebuild
  final ValueNotifier<LatLng?> _positionNotifier = ValueNotifier<LatLng?>(null);

  // Cached ThemeData — only rebuild when _appThemeMode changes
  ThemeData? _cachedThemeData;
  String? _lastThemeMode;

  // GEC Thrissur Campus Area Polygon coordinates
  static final List<LatLng> _campusBoundaryPoints = const [
    LatLng(10.555174, 76.218047),
    LatLng(10.555191, 76.217339),
    LatLng(10.554421, 76.217256),
    LatLng(10.554058, 76.217226),
    LatLng(10.553941, 76.217245),
    LatLng(10.553887, 76.217383),
    LatLng(10.553583, 76.217485),
    LatLng(10.553401, 76.217647),
    LatLng(10.553274, 76.21784),
    LatLng(10.553275, 76.217871),
    LatLng(10.552951, 76.21792),
    LatLng(10.552497, 76.217961),
    LatLng(10.552091, 76.217788),
    LatLng(10.551881, 76.218506),
    LatLng(10.551949, 76.218854),
    LatLng(10.552033, 76.219593),
    LatLng(10.552077, 76.220085),
    LatLng(10.552517, 76.220098),
    LatLng(10.55242, 76.221061),
    LatLng(10.552171, 76.221633),
    LatLng(10.552175, 76.22273),
    LatLng(10.552268, 76.22275),
    LatLng(10.55185, 76.222995),
    LatLng(10.551997, 76.224052),
    LatLng(10.552144, 76.224192),
    LatLng(10.552566, 76.226476),
    LatLng(10.555253, 76.226397),
    LatLng(10.555145, 76.22593),
    LatLng(10.55507, 76.225428),
    LatLng(10.555048, 76.224737),
    LatLng(10.555066, 76.223833),
    LatLng(10.555096, 76.220112),
    LatLng(10.555174, 76.218047),
  ];

  List<Building> _buildings = [];
  Timer? _cloudSyncTimer;
  Building? _selectedBuilding;
  bool _isNavigating = false;
  bool _staircaseCompleted = false;
  int? _stepsAtStairsZoneEnter;
  bool _startStaircaseCompleted = false;
  int? _stepsAtStartStairsZoneEnter;
  int _stepCount = 0;
  final ValueNotifier<int> _stepCountNotifier = ValueNotifier<int>(0);
  // Ring buffer for PDR trail — avoids sublist() allocations
  final List<LatLng> _pdrTrail = List<LatLng>.filled(500, const LatLng(0, 0), growable: true);
  int _pdrTrailIndex = 0;
  int _pdrTrailLength = 0;
  int _userCurrentFloor = 0;
  List<LatLng> _originalRoutingPath = [];
  int _lastClosestRouteIndex = 0;

  // Dijkstra route path coordinates and turn-by-turn instructions
  final ValueNotifier<List<LatLng>> _routingPathNotifier = ValueNotifier<List<LatLng>>([]);
  List<LatLng> get _routingPath => _routingPathNotifier.value;
  set _routingPath(List<LatLng> val) => _routingPathNotifier.value = val;
  List<LatLng> _startAccessPath = [];
  List<LatLng> _endAccessPath = [];
  List<String> _routeInstructions = [];
  List<int> _routeInstructionIndices = [];
  int _currentInstructionIndex = 0;
  String _navMode = 'walking';
  // Circular buffer for speed history — avoids removeAt(0) GC pressure
  final List<double> _speedHistory = List<double>.filled(8, 0.0);
  int _speedHistoryIndex = 0;
  int _speedHistoryLength = 0;
  bool _isAutoRecentering = true;
  bool _isRecalculating = false;

  bool _audioNavigationEnabled = true;
  bool _hasAnnouncedArrival = false;
  String _lastAnnouncedInstruction = "";
  bool _hasAnnouncedAdvanceWarning = false;
  bool _hasAnnouncedTurnNow = false;
  String? _activeGateClosureNotice;

  String _extractShortTurnAction(String text) {
    final t = text.toLowerCase();
    if (t.contains('sharp right')) return 'Sharp Right';
    if (t.contains('sharp left')) return 'Sharp Left';
    if (t.contains('slight right')) return 'Slight Right';
    if (t.contains('slight left')) return 'Slight Left';
    if (t.contains('turn right') || t.contains('right')) return 'Turn Right';
    if (t.contains('turn left') || t.contains('left')) return 'Turn Left';
    if (t.contains('gate')) return 'Pass Gate';
    if (t.contains('arrive')) return 'Arrive at Destination';
    return text;
  }

  // Category filter state
  final List<String> _categories = ['All', 'Departments', 'Workshops', 'Hostels', 'Cafes/ATMs', 'Rooms/Labs', 'Washrooms'];
  String _selectedCategory = 'All';

  // _currentPosition is the authoritative position; _positionNotifier mirrors it for UI
  LatLng? _currentPosition;
  LatLng? _rawDeviceGpsPosition;
  LatLng? _sharedGridLocation;
  StreamSubscription<Position>? _gpsSubscription;
  bool _isLoading = false;
  String? _loadError;
  bool _locationDenied = false;
  bool _locationDeniedForever = false;
  bool _locationServiceDisabled = false;

  // Onboarding Carousel state
  bool _showOnboarding = false;
  final PageController _onboardingPageController = PageController();
  int _onboardingPageIndex = 0;

  // Pulsing animation for selected markers
  late AnimationController _pulseController;
  // Gradient animation controller for search bar before input
  late AnimationController _searchGradientController;

  // Map Type ('satellite', 'light', 'ambient')
  String _mapType = 'ambient';
  // App Theme Mode ('light', 'ambient')
  String _appThemeMode = 'light';
  bool _showLayerSelector = false;

  // Telemetry dashboard states
  bool _showSensorDashboard = false;
  double _telemetryHeading = 0.0;
  double _compassOffset = 0.0;
  // Circular buffer for magnetometer history (avoids removeAt(0) GC pressure)
  final List<double> _magHistory = List.filled(15, 0.0);
  int _magHistoryIndex = 0;
  double _currentAltitude = 0.0;

  // App Update Service
  final AppUpdateService _appUpdateService = AppUpdateService();

  Future<void> _checkAppUpdate() async {
    // Only check for APK updates on native Android/mobile app, skip for Web app
    if (kIsWeb) return;

    try {
      final updateInfo = await _appUpdateService.checkForUpdate();
      if (updateInfo != null && mounted) {
        UpdateAvailableDialog.show(context, updateInfo);
      }
    } catch (e) {
      debugPrint("Update check error: $e");
    }
  }

  // GEC Thrissur Center
  final LatLng _campusCenter = const LatLng(10.5531427, 76.2215317);

  // Dynamic color getters for Theme System
  Color get _bgOverlayColor {
    if (_appThemeMode == 'light') return Colors.white.withValues(alpha: 0.92);
    return const Color(0xFF0F1E36).withValues(alpha: 0.85); // Tinted blue-violet glass
  }

  Color get _cardBgColor {
    if (_appThemeMode == 'light') return Colors.white;
    return const Color(0xFF1E294B); // Tinted navy card
  }

  Color get _scaffoldBgColor {
    if (_appThemeMode == 'light') return const Color(0xFFF8FAFC);
    return const Color(0xFF0B0F19);
  }

  Color get _textColor {
    if (_appThemeMode == 'light') return const Color(0xFF0F172A);
    return Colors.white;
  }

  Color get _subTextColor {
    if (_appThemeMode == 'light') return const Color(0xFF64748B);
    return Colors.white.withValues(alpha: 0.65);
  }

  Color get _borderColor {
    if (_appThemeMode == 'light') return const Color(0xFFE2E8F0);
    return Colors.white.withValues(alpha: 0.14);
  }

  @override
  void initState() {
    super.initState();
    WidgetsBinding.instance.addObserver(this);
    
    _pulseController = AnimationController(
      vsync: this,
      duration: const Duration(seconds: 2),
    )..repeat();

    _searchGradientController = AnimationController(
      vsync: this,
      duration: const Duration(seconds: 4),
    )..repeat();

    _telemetryNotifier = ValueNotifier<TelemetryData>(
      TelemetryData(
        heading: 0.0,
        accelX: 0.0,
        accelY: 0.0,
        accelZ: 0.0,
        accelMag: 0.0,
        magHistory: List.filled(15, 0.0),
        altitude: 0.0,
      ),
    );

    _initData();

    // Defer non-critical startup work to after first frame
    WidgetsBinding.instance.addPostFrameCallback((_) {
      _checkAppUpdate();
    });

    _pdrService.onPositionUpdated = (LatLng newPosition) {
      if (!mounted) return;
      _rawDeviceGpsPosition = newPosition;
      LatLng displayPos = newPosition;

      if (_isNavigating && _routingPath.length >= 2) {
        displayPos = RoutingService.snapToNearestSegment(newPosition, _routingPath, maxDistanceMeters: 15.0);
      }
      _currentPosition = displayPos;

      // Ring buffer write — only record trail if moved > 0.3m
      if (_pdrTrailLength == 0 || _routingService.distance(_pdrTrail[(_pdrTrailIndex - 1) % 500], displayPos) > 0.3) {
        _pdrTrail[_pdrTrailIndex % 500] = displayPos;
        _pdrTrailIndex++;
        if (_pdrTrailLength < 500) _pdrTrailLength++;
      }
      if (_isNavigating) {
        _updateActiveRoutePath(newPosition);
      }

      // Update position via ValueNotifier — only rebuilds user marker widget, not entire tree
      _positionNotifier.value = _currentPosition;

      if (_isAutoRecentering) {
        final double moveDist = _routingService.distance(_mapController.camera.center, displayPos);
        if (moveDist > 0.2) {
          _mapController.move(displayPos, _mapController.camera.zoom);
        }
      }
    };

    _pdrService.onStepDetected = (int count) {
      if (!mounted) return;
      _stepCount = count; // Keep field updated for staircase zone logic
      _stepCountNotifier.value = count; // UI updates via ValueNotifier, no setState
    };

    _pdrService.onRawCompassUpdated = (double heading) {
      if (!mounted) return;
      final current = _telemetryNotifier.value;
      _telemetryHeading = (heading + _compassOffset + 360) % 360;
      _telemetryNotifier.value = TelemetryData(
        heading: _telemetryHeading,
        accelX: current.accelX,
        accelY: current.accelY,
        accelZ: current.accelZ,
        accelMag: current.accelMag,
        magHistory: current.magHistory,
        altitude: _currentAltitude,
      );
    };

    _pdrService.onRawAccelUpdated = (double x, double y, double z, double magnitude) {
      if (!mounted) return;
      
      // Circular buffer write — O(1) instead of O(n) removeAt(0)
      _magHistory[_magHistoryIndex % 15] = magnitude;
      _magHistoryIndex++;

      _telemetryNotifier.value = TelemetryData(
        heading: _telemetryHeading,
        accelX: x,
        accelY: y,
        accelZ: z,
        accelMag: magnitude,
        magHistory: _magHistory, // share the list ref; TelemetryData is read-only
        altitude: _currentAltitude,
      );
    };
  }

  @override
  void dispose() {
    WidgetsBinding.instance.removeObserver(this);
    _gpsSubscription?.cancel();
    _serviceStatusSub?.cancel();
    _cloudSyncTimer?.cancel();
    _pulseController.dispose();
    _searchGradientController.dispose();
    _pdrService.stopPDR();
    _onboardingPageController.dispose();
    _positionNotifier.dispose();
    _telemetryNotifier.dispose();
    _mapController.dispose();
    super.dispose();
  }

  Future<void> _initData() async {
    // Safety fallback timer to guarantee splash screen dismiss within 400ms
    Future.delayed(const Duration(milliseconds: 400), () {
      if (mounted && _isLoading) {
        setState(() {
          _isLoading = false;
        });
      }
    });

    try {
      // 1. Fast parallel initialization for instant UI rendering
      final results = await Future.wait([
        _dataService.loadBuildings(
          syncCloudAsync: true,
          onCloudSynced: (syncedBuildings) {
            if (mounted) {
              setState(() {
                _buildings = syncedBuildings;
                _cachedFilteredBuildings = null;
                _lastBuildingCount = -1;
              });
            }
          },
        ).timeout(const Duration(seconds: 2), onTimeout: () => <Building>[]),
        _checkOnboarding().timeout(const Duration(milliseconds: 300), onTimeout: () {}),
      ]);

      final buildings = (results[0] as List<Building>?) ?? <Building>[];

      if (!mounted) return;
      // Instant UI unblock (< 50ms)
      setState(() {
        _buildings = buildings;
        _cachedFilteredBuildings = null;
        _lastBuildingCount = -1;
        _isLoading = false;
      });

      // 2. Non-blocking asynchronous location check in background
      _initLocationInBackground();

      // Ensure campus road network from assets/campus_roads.json is loaded as default
      rootBundle.loadString('assets/campus_roads.json').then((jsonString) {
        _routingService.loadCampusRoadsFromJsonString(jsonString);
      }).catchError((e) {
        debugPrint("Campus roads json pre-load note: $e");
      });

      // Floor detection deferred to background — not on critical path
      PlaceDetectionService().init().then((_) {
        PlaceDetectionService().detectCurrentFloor().then((detectedFloor) {
          if (detectedFloor != null && mounted) {
            ScaffoldMessenger.of(context).showSnackBar(
              SnackBar(
                content: Text("Auto-detected Location: ${detectedFloor.floorName}"),
                backgroundColor: const Color(0xFF10B981),
                behavior: SnackBarBehavior.floating,
              ),
            );
          }
        }).catchError((_) {});
      }).catchError((_) {});

      WidgetsBinding.instance.addPostFrameCallback((_) {
        _handleStartupDeepLink();
      });

      // Periodic cloud sync every 10 seconds — ensures pins added/deleted on
      // other devices are reflected quickly without requiring a full app restart.
      _cloudSyncTimer = Timer.periodic(const Duration(seconds: 10), (_) {
        if (!mounted) return;
        _dataService.fetchCloudBuildings().then((synced) {
          if (mounted && synced.isNotEmpty) {
            setState(() {
              _buildings = synced;
              _cachedFilteredBuildings = null;
              _lastBuildingCount = -1;
            });
          }
        }).catchError((e) {
          debugPrint('Periodic cloud sync error: $e');
        });
      });
    } catch (e) {
      debugPrint("Error initializing map data: $e");
      if (mounted) {
        setState(() {
          _loadError = null;
          _isLoading = false;
        });
      }
    }
  }

  Future<void> _initLocationInBackground() async {
    LatLng? userPos;
    try {
      bool serviceEnabled = await Geolocator.isLocationServiceEnabled().timeout(const Duration(seconds: 2), onTimeout: () => false);
      if (!serviceEnabled) {
        if (mounted) setState(() => _locationServiceDisabled = true);
      } else {
        LocationPermission permission = await Geolocator.checkPermission().timeout(const Duration(seconds: 2), onTimeout: () => LocationPermission.denied);
        if (permission == LocationPermission.denied) {
          permission = await Geolocator.requestPermission().timeout(const Duration(seconds: 4), onTimeout: () => LocationPermission.denied);
        }
        if (permission == LocationPermission.deniedForever) {
          if (mounted) setState(() => _locationDeniedForever = true);
        } else if (permission == LocationPermission.denied) {
          if (mounted) setState(() => _locationDenied = true);
        } else if (permission == LocationPermission.always ||
            permission == LocationPermission.whileInUse) {
          if (mounted) {
            setState(() {
              _locationDenied = false;
              _locationDeniedForever = false;
              _locationServiceDisabled = false;
            });
          }
          final lastPos = await Geolocator.getLastKnownPosition().timeout(const Duration(seconds: 2), onTimeout: () => null);
          if (lastPos != null) {
            userPos = LatLng(lastPos.latitude, lastPos.longitude);
          }
        }
      }
    } catch (e) {
      debugPrint("Last known location check note: $e");
    }

    if (userPos != null && mounted) {
      _rawDeviceGpsPosition = userPos;
      _currentPosition = userPos;
      _positionNotifier.value = userPos;
      _pdrService.startPDR(userPos);
      if (_isAutoRecentering) {
        _mapController.move(userPos, _mapController.camera.zoom);
      }
    }

    _startGPSListening();
    _updateCurrentGPSLocationAsync();
  }

  Future<void> _updateCurrentGPSLocationAsync() async {
    try {
      final pos = await Geolocator.getCurrentPosition(
        locationSettings: const LocationSettings(
          accuracy: LocationAccuracy.bestForNavigation,
          timeLimit: Duration(seconds: 5),
        ),
      );
      if (mounted) {
        final newPos = LatLng(pos.latitude, pos.longitude);
        _rawDeviceGpsPosition = newPos;
        _currentPosition = newPos;
        _positionNotifier.value = newPos;
        if (!_pdrService.isActive) {
          _pdrService.startPDR(newPos);
        }
        _pdrService.updateGPSPosition(newPos, pos.accuracy, pos.speed, pos.heading);
        if (_isAutoRecentering) {
          _mapController.move(newPos, _mapController.camera.zoom);
        }
      }
    } catch (e) {
      debugPrint("Async GPS location update note: $e");
    }
  }

  Future<void> _recenterOnUserLocation() async {
    setState(() {
      _isAutoRecentering = true;
    });

    // 1. Immediately pan/zoom to existing location if already known for instant UI response
    final existingPos = _pdrService.currentPosition ?? _currentPosition ?? _rawDeviceGpsPosition ?? _positionNotifier.value;
    if (existingPos != null && mounted) {
      final targetZoom = _mapController.camera.zoom < 18.0 ? 18.0 : _mapController.camera.zoom;
      _mapController.move(existingPos, targetZoom);
    }

    // 2. Validate and handle location service & permissions
    try {
      bool serviceEnabled = await Geolocator.isLocationServiceEnabled();
      if (!serviceEnabled) {
        if (mounted) {
          setState(() => _locationServiceDisabled = true);
          TopMessageOverlay.showLocationAlert(
            context,
            onOpenSettings: Geolocator.openLocationSettings,
            onReload: _retryLocationPermission,
          );
        }
        return;
      }

      LocationPermission permission = await Geolocator.checkPermission();
      if (permission == LocationPermission.denied) {
        permission = await Geolocator.requestPermission();
      }
      if (permission == LocationPermission.deniedForever) {
        if (mounted) {
          setState(() => _locationDeniedForever = true);
          _retryLocationPermission();
        }
        return;
      }
      if (permission == LocationPermission.denied) {
        if (mounted) {
          setState(() => _locationDenied = true);
          ScaffoldMessenger.of(context).showSnackBar(
            const SnackBar(
              content: Text("Location permission is needed to show your position."),
              backgroundColor: Colors.orangeAccent,
              behavior: SnackBarBehavior.floating,
            ),
          );
        }
        return;
      }

      // Ensure active GPS subscription is running
      _startGPSListening();

      // 3. If no existing position was known, try instant last known position
      if (existingPos == null) {
        final lastKnown = await Geolocator.getLastKnownPosition();
        if (lastKnown != null && mounted) {
          final lastKnownPos = LatLng(lastKnown.latitude, lastKnown.longitude);
          _rawDeviceGpsPosition = lastKnownPos;
          _currentPosition = lastKnownPos;
          _positionNotifier.value = lastKnownPos;
          if (!_pdrService.isActive) {
            _pdrService.startPDR(lastKnownPos);
          }
          final targetZoom = _mapController.camera.zoom < 18.0 ? 18.0 : _mapController.camera.zoom;
          _mapController.move(lastKnownPos, targetZoom);
        }
      }

      // 4. Acquire fresh GPS fix with fallback
      Position? freshPos;
      try {
        freshPos = await Geolocator.getCurrentPosition(
          locationSettings: const LocationSettings(
            accuracy: LocationAccuracy.bestForNavigation,
            timeLimit: Duration(seconds: 6),
          ),
        );
      } catch (_) {
        // Fallback for indoor or weak satellite lock
        try {
          freshPos = await Geolocator.getCurrentPosition(
            locationSettings: const LocationSettings(
              accuracy: LocationAccuracy.high,
              timeLimit: Duration(seconds: 4),
            ),
          );
        } catch (_) {}
      }

      if (freshPos != null && mounted) {
        final newPos = LatLng(freshPos.latitude, freshPos.longitude);
        _rawDeviceGpsPosition = newPos;
        _currentPosition = newPos;
        _positionNotifier.value = newPos;
        if (!_pdrService.isActive) {
          _pdrService.startPDR(newPos);
        }
        _pdrService.updateGPSPosition(newPos, freshPos.accuracy, freshPos.speed, freshPos.heading);
        final targetZoom = _mapController.camera.zoom < 18.0 ? 18.0 : _mapController.camera.zoom;
        _mapController.move(newPos, targetZoom);
      } else if (existingPos == null && mounted) {
        final currentKnown = _pdrService.currentPosition ?? _currentPosition ?? _rawDeviceGpsPosition;
        if (currentKnown != null) {
          _mapController.move(currentKnown, 18.0);
        } else {
          ScaffoldMessenger.of(context).showSnackBar(
            const SnackBar(
              content: Text("Acquiring GPS location... Please ensure location is enabled and you have clear sky visibility."),
              backgroundColor: Colors.blueAccent,
              behavior: SnackBarBehavior.floating,
              duration: Duration(seconds: 3),
            ),
          );
        }
      }
    } catch (e) {
      debugPrint("Recenter on location error: $e");
      final fallbackPos = _pdrService.currentPosition ?? _currentPosition ?? _rawDeviceGpsPosition;
      if (fallbackPos != null && mounted) {
        _mapController.move(fallbackPos, 18.0);
      }
    }
  }

  @override
  void didChangeAppLifecycleState(AppLifecycleState state) {
    if (state == AppLifecycleState.resumed) {
      _checkLocationPermissionOnResume();
    }
  }

  Future<void> _checkLocationPermissionOnResume() async {
    try {
      bool serviceEnabled = await Geolocator.isLocationServiceEnabled();
      LocationPermission permission = await Geolocator.checkPermission();

      if (!mounted) return;

      if (!serviceEnabled) {
        setState(() {
          _locationServiceDisabled = true;
          _locationDenied = false;
          _locationDeniedForever = false;
        });
      } else if (permission == LocationPermission.always || permission == LocationPermission.whileInUse) {
        setState(() {
          _locationServiceDisabled = false;
          _locationDenied = false;
          _locationDeniedForever = false;
        });
        _updateCurrentGPSLocationAsync();
        _startGPSListening();
      } else if (permission == LocationPermission.deniedForever) {
        setState(() {
          _locationServiceDisabled = false;
          _locationDeniedForever = true;
          _locationDenied = false;
        });
      } else if (permission == LocationPermission.denied) {
        setState(() {
          _locationServiceDisabled = false;
          _locationDeniedForever = false;
          _locationDenied = true;
        });
      }
    } catch (e) {
      debugPrint("Error checking location permission on resume: $e");
    }
  }

  Future<void> _retryLocationPermission() async {
    // 1. Check current status first before opening settings or requesting
    try {
      bool serviceEnabled = await Geolocator.isLocationServiceEnabled();
      LocationPermission currentPerm = await Geolocator.checkPermission();

      if (serviceEnabled && (currentPerm == LocationPermission.always || currentPerm == LocationPermission.whileInUse)) {
        if (mounted) {
          setState(() {
            _locationServiceDisabled = false;
            _locationDenied = false;
            _locationDeniedForever = false;
          });
        }
        _updateCurrentGPSLocationAsync();
        _startGPSListening();
        return;
      }
    } catch (_) {}

    // 2. Web Browser Guidance
    if (kIsWeb) {
      if (mounted) {
        showDialog(
          context: context,
          builder: (ctx) => AlertDialog(
            backgroundColor: _cardBgColor,
            shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(18)),
            title: Row(
              children: [
                const Icon(Icons.info_outline, color: Color(0xFF2563EB)),
                const SizedBox(width: 10),
                Text("Enable Location on Web", style: TextStyle(color: _textColor, fontSize: 16, fontWeight: FontWeight.bold)),
              ],
            ),
            content: Text(
              "Browser location access is currently blocked.\n\n"
              "To enable location:\n"
              "1. Click the lock icon (🔒) or tune icon near the website URL in your address bar.\n"
              "2. Set 'Location' to 'Allow'.\n"
              "3. Refresh the webpage.",
              style: TextStyle(color: _subTextColor, fontSize: 13.5, height: 1.4),
            ),
            actions: [
              TextButton(
                onPressed: () => Navigator.of(ctx).pop(),
                child: const Text("Got It", style: TextStyle(fontWeight: FontWeight.bold, color: Color(0xFF2563EB))),
              ),
            ],
          ),
        );
      }
      return;
    }

    // 3. Native App Handling (Android / iOS)
    if (_locationServiceDisabled) {
      bool opened = false;
      try {
        opened = await Geolocator.openLocationSettings();
      } catch (e) {
        debugPrint("Geolocator.openLocationSettings error: $e");
      }
      if (!opened) {
        try {
          await ph.openAppSettings();
        } catch (_) {}
      }
    } else if (_locationDeniedForever) {
      bool opened = false;
      try {
        opened = await ph.openAppSettings();
      } catch (e) {
        debugPrint("permission_handler openAppSettings failed: $e");
      }
      if (!opened) {
        try {
          opened = await Geolocator.openAppSettings();
        } catch (e) {
          debugPrint("Geolocator openAppSettings failed: $e");
        }
      }
      if (!opened) {
        try {
          await Geolocator.openLocationSettings();
        } catch (_) {}
      }
    } else {
      // Re-request permission prompt
      try {
        final permission = await Geolocator.requestPermission();
        if (permission == LocationPermission.always || permission == LocationPermission.whileInUse) {
          if (mounted) {
            setState(() {
              _locationDenied = false;
              _locationDeniedForever = false;
              _locationServiceDisabled = false;
            });
          }
          _updateCurrentGPSLocationAsync();
          _startGPSListening();
        } else if (permission == LocationPermission.deniedForever) {
          if (mounted) setState(() => _locationDeniedForever = true);
        } else if (permission == LocationPermission.denied) {
          if (mounted) setState(() => _locationDenied = true);
        }
      } catch (e) {
        debugPrint("Retry location error: $e");
      }
    }
  }

  StreamSubscription<ServiceStatus>? _serviceStatusSub;

  Future<void> _startGPSListening() async {
    try {
      bool serviceEnabled = await Geolocator.isLocationServiceEnabled();
      if (!serviceEnabled) {
        if (mounted) {
          setState(() => _locationServiceDisabled = true);
          TopMessageOverlay.showLocationAlert(
            context,
            onOpenSettings: Geolocator.openLocationSettings,
            onReload: _retryLocationPermission,
          );
        }
        return;
      }

      _serviceStatusSub?.cancel();
      if (!kIsWeb) {
        _serviceStatusSub = Geolocator.getServiceStatusStream().listen((ServiceStatus status) {
          if (status == ServiceStatus.disabled && mounted) {
            setState(() => _locationServiceDisabled = true);
            TopMessageOverlay.showLocationAlert(
              context,
              onOpenSettings: Geolocator.openLocationSettings,
              onReload: _retryLocationPermission,
            );
          }
        });
      }

      LocationPermission permission = await Geolocator.checkPermission();
      if (permission == LocationPermission.denied) {
        permission = await Geolocator.requestPermission();
      }
      if (permission == LocationPermission.deniedForever) {
        if (mounted) setState(() => _locationDeniedForever = true);
        return;
      }
      if (permission == LocationPermission.denied) {
        if (mounted) setState(() => _locationDenied = true);
        return;
      }
      if (permission == LocationPermission.always ||
          permission == LocationPermission.whileInUse) {
        if (mounted) {
          setState(() {
            _locationDenied = false;
            _locationDeniedForever = false;
            _locationServiceDisabled = false;
          });
        }
        LocationSettings locationSettings;
        if (kIsWeb) {
          locationSettings = const LocationSettings(
            accuracy: LocationAccuracy.bestForNavigation,
            distanceFilter: 0,
          );
        } else if (defaultTargetPlatform == TargetPlatform.android) {
          locationSettings = AndroidSettings(
            accuracy: LocationAccuracy.bestForNavigation,
            distanceFilter: 0,
            intervalDuration: const Duration(milliseconds: 200),
            forceLocationManager: false,
          );
        } else if (defaultTargetPlatform == TargetPlatform.iOS) {
          locationSettings = AppleSettings(
            accuracy: LocationAccuracy.bestForNavigation,
            distanceFilter: 0,
            activityType: ActivityType.fitness,
            pauseLocationUpdatesAutomatically: false,
          );
        } else {
          locationSettings = const LocationSettings(
            accuracy: LocationAccuracy.bestForNavigation,
            distanceFilter: 0,
          );
        }

        _gpsSubscription?.cancel();
        _gpsSubscription = Geolocator.getPositionStream(
          locationSettings: locationSettings,
        ).listen((Position position) {
          if (!mounted) return;
          final newPos = LatLng(position.latitude, position.longitude);
          _rawDeviceGpsPosition = newPos;
          _currentPosition = newPos;
          _positionNotifier.value = newPos;
          
          // Update altitude and speed without triggering a full rebuild
          _currentAltitude = position.altitude;
          if (_isNavigating && position.speed > 0) {
            // Circular buffer write — O(1), no GC pressure
            _speedHistory[_speedHistoryIndex % 8] = position.speed;
            _speedHistoryIndex++;
            if (_speedHistoryLength < 8) _speedHistoryLength++;
          }
          
          // Also update telemetry immediately if sensor dashboard is open
          if (_showSensorDashboard) {
            final current = _telemetryNotifier.value;
            _telemetryNotifier.value = TelemetryData(
              heading: current.heading,
              accelX: current.accelX,
              accelY: current.accelY,
              accelZ: current.accelZ,
              accelMag: current.accelMag,
              magHistory: current.magHistory,
              altitude: position.altitude,
            );
          }
          
          if (!_pdrService.isActive) {
            _pdrService.startPDR(newPos);
          }
          
          _pdrService.updateGPSPosition(
            newPos,
            position.accuracy,
            position.speed,
            position.heading,
          );
        }, onError: (e) {
          debugPrint("GPS stream error: $e");
        });
      }
    } catch (e) {
      debugPrint("Error starting GPS listening: $e");
    }
  }

  Future<void> _checkOnboarding() async {
    final prefs = await SharedPreferences.getInstance();
    if (!mounted) return;
    final hasSeen = prefs.getBool('seen_onboarding') ?? false;
    if (!hasSeen) {
      setState(() {
        _showOnboarding = true;
      });
    }
  }

  Future<void> _dismissOnboarding() async {
    final prefs = await SharedPreferences.getInstance();
    await prefs.setBool('seen_onboarding', true);
    setState(() {
      _showOnboarding = false;
    });
  }

  /// Calculate distance in meters between two LatLng points (Haversine).
  /// Fast equirectangular distance for nearby points (campus-scale, avoids trig of Haversine)
  double _fastDistanceMeters(LatLng a, LatLng b) {
    const double mPerDegLat = 111320.0;
    final double mPerDegLng = 111320.0 * cos(a.latitude * (pi / 180.0));
    final double dx = (a.longitude - b.longitude) * mPerDegLng;
    final double dy = (a.latitude - b.latitude) * mPerDegLat;
    return sqrt(dx * dx + dy * dy);
  }

  double _distanceMeters(LatLng a, LatLng b) {
    return _routingService.distance(a, b);
  }

  String _formatDistance(double meters) {
    if (meters < 1000) return "${meters.toStringAsFixed(0)} m";
    return "${(meters / 1000).toStringAsFixed(1)} km";
  }

  void _handleStartupDeepLink() {
    try {
      final queryParams = Uri.base.queryParameters;
      
      final gridParam = queryParams['grid'];
      final latParam = queryParams['lat'];
      final lngParam = queryParams['lng'];

      LatLng? loc;
      if (latParam != null && lngParam != null) {
        final parsedLat = double.tryParse(latParam);
        final parsedLng = double.tryParse(lngParam);
        if (parsedLat != null && parsedLng != null) {
          loc = LatLng(parsedLat, parsedLng);
        }
      }

      if (loc == null && gridParam != null && gridParam.isNotEmpty) {
        loc = GridAddressingService.getLatLngFromGridAddress(gridParam);
      }

      if (loc != null) {
        final displayGrid = gridParam != null && gridParam.isNotEmpty
            ? gridParam
            : GridAddressingService.getCampusGridAddress(loc);
        debugPrint("Deep link detected for location: $loc (grid: $displayGrid)");
        final sharedBuilding = Building(
          id: 'shared_${displayGrid.replaceAll(' ', '_')}',
          name: 'Shared Location ($displayGrid)',
          lat: loc.latitude,
          lng: loc.longitude,
          tags: {
            'place_type': 'Shared Location',
            'custom': 'true',
            'grid_code': displayGrid,
          },
        );
        setState(() {
          _sharedGridLocation = loc;
        });
        _mapController.move(loc, 18.5);
        _selectBuilding(sharedBuilding);
        return;
      }

      final placeId = queryParams['placeId'] ?? queryParams['placeid'];
      if (placeId != null && placeId.isNotEmpty) {
        Building? target;
        for (final b in _buildings) {
          if (b.id == placeId) {
            target = b;
            break;
          }
        }
        if (target != null) {
          debugPrint("Deep link detected for building: ${target.name}");
          _selectBuilding(target);
        } else {
          debugPrint("Deep link placeId $placeId not found in buildings list.");
        }
      }
    } catch (e) {
      debugPrint("Error handling startup deep link: $e");
    }
  }

  void _selectBuilding(Building building) {
    setState(() {
      _selectedBuilding = building;
      if (_isNavigating) {
        _isNavigating = false;
        _staircaseCompleted = false;
        _stepsAtStairsZoneEnter = null;
        _startStaircaseCompleted = false;
        _stepsAtStartStairsZoneEnter = null;
        _pdrTrailIndex = 0;
        _pdrTrailLength = 0;
        _routingPath.clear();
        _routeInstructions.clear();
        _routeInstructionIndices.clear();
        _currentInstructionIndex = 0;
      }
      FocusScope.of(context).unfocus();
    });

    _mapController.move(LatLng(building.lat, building.lng), 18.5);
    _showBuildingDetails(building);
  }

  Future<int?> _promptForCurrentFloor(BuildContext context) async {
    return showDialog<int>(
      context: context,
      barrierDismissible: true,
      builder: (context) {
        return AlertDialog(
          backgroundColor: _cardBgColor,
          shape: RoundedRectangleBorder(
            borderRadius: BorderRadius.circular(24),
            side: BorderSide(color: _borderColor),
          ),
          title: Row(
            children: [
              Icon(Icons.stairs, color: const Color(0xFF3B82F6)),
              const SizedBox(width: 12),
              Text(
                "Current Floor",
                style: TextStyle(color: _textColor, fontWeight: FontWeight.bold),
              ),
            ],
          ),
          content: Column(
            mainAxisSize: MainAxisSize.min,
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              Text(
                "Which floor are you currently on?",
                style: TextStyle(color: _textColor.withValues(alpha: 0.7), fontSize: 15),
              ),
              const SizedBox(height: 20),
              Wrap(
                spacing: 12,
                runSpacing: 12,
                alignment: WrapAlignment.center,
                children: List.generate(5, (index) {
                  return InkWell(
                    onTap: () => Navigator.pop(context, index),
                    borderRadius: BorderRadius.circular(16),
                    child: Container(
                      width: 100,
                      padding: const EdgeInsets.symmetric(vertical: 16),
                      decoration: BoxDecoration(
                        color: _cardBgColor.withValues(alpha: 0.5),
                        borderRadius: BorderRadius.circular(16),
                        border: Border.all(color: _borderColor),
                      ),
                      child: Column(
                        mainAxisSize: MainAxisSize.min,
                        children: [
                          Text(
                            "$index",
                            style: TextStyle(
                              color: _textColor,
                              fontSize: 22,
                              fontWeight: FontWeight.bold,
                            ),
                          ),
                          const SizedBox(height: 4),
                          Text(
                            index == 0 ? "Ground" : "Floor $index",
                            style: TextStyle(
                              color: _textColor.withValues(alpha: 0.54),
                              fontSize: 12,
                            ),
                            textAlign: TextAlign.center,
                          ),
                        ],
                      ),
                    ),
                  );
                }),
              ),
            ],
          ),
          actions: [
            TextButton(
              onPressed: () => Navigator.pop(context, null),
              child: const Text("Cancel", style: TextStyle(color: Colors.redAccent)),
            ),
          ],
        );
      },
    );
  }

  int _offRouteCount = 0;

  void _updateActiveRoutePath(LatLng newPos) {
    if (_originalRoutingPath.isEmpty) return;

    // Search the entire route length to prevent false "off-route" triggers when moving fast
    int searchStart = 0;
    int searchEnd = _originalRoutingPath.length;
    int closestIndex = _lastClosestRouteIndex;
    double minDistance = double.infinity;

    for (int i = searchStart; i < searchEnd; i++) {
      double d = _fastDistanceMeters(newPos, _originalRoutingPath[i]);
      if (d < minDistance) {
        minDistance = d;
        closestIndex = i;
      }
    }

    _lastClosestRouteIndex = closestIndex;

    // Freeze route state while async recalculation is in flight
    if (_isRecalculating) return;

    // Require 2 consecutive off-route samples (> 20 meters) before triggering recalculation
    if (minDistance > 20.0) {
      _offRouteCount++;
      if (_offRouteCount >= 2 && !_isRecalculating) {
        _offRouteCount = 0;
        _recalculateRoute(newPos);
        return;
      }
    } else {
      _offRouteCount = 0;
    }

    // Update current turn-by-turn instruction index based on closest route index
    if (_routeInstructionIndices.isNotEmpty) {
      int newInstructionIdx = 0;
      for (int i = 0; i < _routeInstructionIndices.length; i++) {
        if (_lastClosestRouteIndex >= _routeInstructionIndices[i]) {
          newInstructionIdx = i;
        }
      }
      if (newInstructionIdx != _currentInstructionIndex) {
        HapticFeedback.lightImpact(); // Haptic transition alert
        _currentInstructionIndex = newInstructionIdx;
        _hasAnnouncedAdvanceWarning = false; // Reset for next segment
        _hasAnnouncedTurnNow = false;

        final currentInst = _routeInstructions[_currentInstructionIndex];
        if (_currentInstructionIndex < _routeInstructions.length - 1) {
          final distToNext = _distanceToNextTurn(newPos);
          if (distToNext > 25.0) {
            _announceInstruction("Continue straight for ${distToNext.round()} meters");
          } else {
            _announceInstruction(currentInst);
          }
        } else {
          _announceInstruction(currentInst);
        }
      }

      final distToNext = _distanceToNextTurn(newPos);

      // Layered advance warning: announce at ~20-25m before next turn
      if (!_hasAnnouncedAdvanceWarning && distToNext > 9.0 && distToNext <= 25.0 &&
          _currentInstructionIndex + 1 < _routeInstructions.length) {
        _hasAnnouncedAdvanceWarning = true;
        final nextInstruction = _routeInstructions[_currentInstructionIndex + 1];
        _announceInstruction("In ${distToNext.round()} meters, $nextInstruction");
      }

      // Immediate turn execution announcement at < 7m before turn point
      if (!_hasAnnouncedTurnNow && distToNext > 0.5 && distToNext <= 7.0 &&
          _currentInstructionIndex + 1 < _routeInstructions.length) {
        _hasAnnouncedTurnNow = true;
        HapticFeedback.mediumImpact();
        final nextInstruction = _routeInstructions[_currentInstructionIndex + 1];
        final shortAction = _extractShortTurnAction(nextInstruction);
        _announceInstruction(shortAction);
      }
    }

    // Check arrival announcement (15m for buildings, 5m for rooms)
    if (_isNavigating && _selectedBuilding != null && !_hasAnnouncedArrival) {
      final isRoom = _selectedBuilding!.tags['room'] == 'yes';
      final double dist = _distanceMeters(newPos, LatLng(_selectedBuilding!.lat, _selectedBuilding!.lng));
      final double arrivalThreshold = isRoom ? 5.0 : 15.0;
      
      if (dist <= arrivalThreshold) {
        _hasAnnouncedArrival = true;
        _announceInstruction("You have arrived at ${_selectedBuilding!.name}");
      }
    }

    // Dynamic path shrinking: update visible path when closest index advances or head moves
    if (closestIndex != _lastRouteClosestIndex) {
      _lastRouteClosestIndex = closestIndex;
      List<LatLng> newPath = [newPos];
      for (int i = closestIndex; i < _originalRoutingPath.length; i++) {
        if (i == closestIndex && _distanceMeters(newPos, _originalRoutingPath[i]) < 2.0) {
          continue;
        }
        newPath.add(_originalRoutingPath[i]);
      }
      if (newPath.length < 2) {
        newPath = [newPos, _originalRoutingPath.last];
      }
      _routingPathNotifier.value = newPath;
    } else {
      if (_routingPathNotifier.value.isNotEmpty) {
        final updated = List<LatLng>.from(_routingPathNotifier.value);
        updated[0] = newPos;
        _routingPathNotifier.value = updated;
      }
    }
  }

  void _announceInstruction(String text) {
    if (!_audioNavigationEnabled) return;
    if (text.isEmpty) return;
    if (_lastAnnouncedInstruction == text) return;
    _lastAnnouncedInstruction = text;
    TtsHelper.stop();
    TtsHelper.speak(text);
  }

  Future<void> _recalculateRoute(LatLng currentPos) async {
    if (_selectedBuilding == null || _isRecalculating) return;
    _isRecalculating = true;
    
    _announceInstruction("Recalculating route");
    if (mounted) {
      ScaffoldMessenger.of(context).showSnackBar(
        const SnackBar(
          content: Text('Off route! Recalculating route...'),
          backgroundColor: Colors.orangeAccent,
          duration: Duration(seconds: 2),
        ),
      );
    }

    try {
      final endPos = LatLng(_selectedBuilding!.lat, _selectedBuilding!.lng);
      final routeRes = await _routingService.getDetailedRoute(
        currentPos,
        endPos,
        customBuildings: _buildings,
      );
      final path = routeRes.fullPath;
      final instData = _routingService.getRouteInstructionsWithIndices(path);
      final instructions = instData.map((e) => e['text'] as String).toList();
      final indices = instData.map((e) => e['index'] as int).toList();

      if (!mounted) return;

      setState(() {
        _activeGateClosureNotice = routeRes.gateClosureNotice;
        _routingPath = path;
        _startAccessPath = routeRes.startAccessPath;
        _endAccessPath = routeRes.endAccessPath;
        _originalRoutingPath = List<LatLng>.from(path);
        _lastClosestRouteIndex = 0;
        _lastRouteClosestIndex = -1;
        _routeInstructions = instructions;
        _routeInstructionIndices = indices;
        _currentInstructionIndex = 0;
      });

      if (routeRes.gateClosureNotice != null && routeRes.gateClosureNotice!.isNotEmpty) {
        _announceInstruction(routeRes.gateClosureNotice!);
      }
    } catch (e) {
      debugPrint('Re-routing failed: $e');
    } finally {
      _isRecalculating = false;
    }
  }

  double _distanceToNextTurn(LatLng currentPos) {
    if (_routeInstructionIndices.isEmpty || 
        _currentInstructionIndex >= _routeInstructionIndices.length - 1) {
      return 0.0;
    }

    final nextIdx = _routeInstructionIndices[_currentInstructionIndex + 1];
    if (_lastClosestRouteIndex >= nextIdx) return 0.0;

    // Distance from user to the next waypoint on the route (avoid double-counting)
    double dist = 0.0;
    if (_lastClosestRouteIndex + 1 < _originalRoutingPath.length) {
      dist = _distanceMeters(currentPos, _originalRoutingPath[_lastClosestRouteIndex + 1]);
    }
    for (int i = _lastClosestRouteIndex + 1; i < nextIdx; i++) {
      if (i + 1 < _originalRoutingPath.length) {
        dist += _distanceMeters(_originalRoutingPath[i], _originalRoutingPath[i + 1]);
      }
    }
    return dist;
  }

  void _showOutsideRangeSnackBar() {
    if (!mounted) return;
    ScaffoldMessenger.of(context).hideCurrentSnackBar();
    ScaffoldMessenger.of(context).showSnackBar(
      SnackBar(
        content: const Row(
          children: [
            Icon(Icons.location_off, color: Colors.white, size: 20),
            SizedBox(width: 10),
            Expanded(
              child: Text(
                "You are outside campus area range",
                style: TextStyle(fontWeight: FontWeight.bold, fontSize: 13),
              ),
            ),
          ],
        ),
        backgroundColor: const Color(0xFFE11D48),
        behavior: SnackBarBehavior.floating,
        shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
        margin: const EdgeInsets.only(bottom: 80, left: 16, right: 16),
        duration: const Duration(seconds: 4),
      ),
    );
  }

  Future<void> _startNavigation() async {
    if (_selectedBuilding == null) return;
    
    // Show a loading SnackBar
    ScaffoldMessenger.of(context).showSnackBar(
      const SnackBar(
        content: Row(
          children: [
            SizedBox(
              width: 16,
              height: 16,
              child: CircularProgressIndicator(strokeWidth: 2, color: Colors.white),
            ),
            SizedBox(width: 12),
            Expanded(
              child: Text('Fetching live location and calculating route...', style: TextStyle(fontWeight: FontWeight.w600)),
            ),
          ],
        ),
        duration: Duration(seconds: 15),
        backgroundColor: Color(0xFF3B82F6),
      ),
    );

    // Fetch fresh user GPS location before computing and showing route
    LatLng? startPos = _currentPosition;
    try {
      final serviceEnabled = await Geolocator.isLocationServiceEnabled().timeout(const Duration(seconds: 2), onTimeout: () => false);
      if (serviceEnabled) {
        LocationPermission perm = await Geolocator.checkPermission().timeout(const Duration(seconds: 2), onTimeout: () => LocationPermission.denied);
        if (perm == LocationPermission.denied) {
          perm = await Geolocator.requestPermission().timeout(const Duration(seconds: 4), onTimeout: () => LocationPermission.denied);
        }
        if (perm == LocationPermission.whileInUse || perm == LocationPermission.always) {
          final pos = await Geolocator.getCurrentPosition(
            desiredAccuracy: LocationAccuracy.high,
            timeLimit: const Duration(seconds: 4),
          ).timeout(const Duration(seconds: 4), onTimeout: () async {
            final lastKnown = await Geolocator.getLastKnownPosition();
            if (lastKnown != null) return lastKnown;
            throw TimeoutException("Location timeout");
          });
          final freshLatLng = LatLng(pos.latitude, pos.longitude);
          startPos = freshLatLng;
          _pdrService.updateGPSPosition(freshLatLng);
          _positionNotifier.value = freshLatLng;
          setState(() {
            _currentPosition = freshLatLng;
          });
        }
      }
    } catch (e) {
      debugPrint("GPS location fetch note before routing: $e");
    }

    startPos ??= _currentPosition ?? _campusCenter;
    final endPos = LatLng(_selectedBuilding!.lat, _selectedBuilding!.lng);

    try {
      // Get OSRM path asynchronously
      final routeRes = await _routingService.getDetailedRoute(
        startPos,
        endPos,
        customBuildings: _buildings,
      );
      final path = routeRes.fullPath;
      final instData = _routingService.getRouteInstructionsWithIndices(path);
      final instructions = instData.map((e) => e['text'] as String).toList();
      final indices = instData.map((e) => e['index'] as int).toList();

      if (!mounted) return;
      ScaffoldMessenger.of(context).hideCurrentSnackBar();

      _pdrService.startPDR(startPos);
      setState(() {
        _activeGateClosureNotice = routeRes.gateClosureNotice;
        _isNavigating = true;
        _staircaseCompleted = false;
        _stepsAtStairsZoneEnter = null;
        _startStaircaseCompleted = false;
        _stepsAtStartStairsZoneEnter = null;
        _stepCount = 0;
        _pdrTrailIndex = 0;
        _pdrTrailLength = 1;
        _pdrTrail[0] = startPos;
        _speedHistoryIndex = 0;
        _speedHistoryLength = 0;
        _routingPath = path;
        _startAccessPath = routeRes.startAccessPath;
        _endAccessPath = routeRes.endAccessPath;
        _originalRoutingPath = List<LatLng>.from(path);
        _lastClosestRouteIndex = 0;
        _lastRouteClosestIndex = -1;
        _routeInstructions = instructions;
        _routeInstructionIndices = indices;
        _currentInstructionIndex = 0;
        _isRecalculating = false;
        _hasAnnouncedArrival = false;
        _hasAnnouncedAdvanceWarning = false;
        _hasAnnouncedTurnNow = false;
        _lastAnnouncedInstruction = "";
      });

      if (routeRes.gateClosureNotice != null && routeRes.gateClosureNotice!.isNotEmpty) {
        _announceInstruction(routeRes.gateClosureNotice!);
        ScaffoldMessenger.of(context).showSnackBar(
          SnackBar(
            content: Row(
              children: [
                const Icon(Icons.warning_amber_rounded, color: Colors.white, size: 20),
                const SizedBox(width: 10),
                Expanded(
                  child: Text(
                    routeRes.gateClosureNotice!,
                    style: const TextStyle(fontWeight: FontWeight.bold, fontSize: 13),
                  ),
                ),
              ],
            ),
            backgroundColor: const Color(0xFFD97706),
            behavior: SnackBarBehavior.floating,
            shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
            duration: const Duration(seconds: 5),
          ),
        );
      } else {
        _announceInstruction(instructions.isNotEmpty ? instructions.first : "");
      }

      final LatLng rawPos = _rawDeviceGpsPosition ?? startPos;
      final double distToCampus = _routingService.distance(rawPos, _campusCenter);
      if (distToCampus > 2500.0) {
        _showOutsideRangeSnackBar();
      } else if (routeRes.gateClosureNotice == null) {
        ScaffoldMessenger.of(context).showSnackBar(
          const SnackBar(
            content: Text('Navigation started along campus walkways!'),
            backgroundColor: Color(0xFF10B981),
          ),
        );
      }
    } catch (e) {
      if (!mounted) return;
      ScaffoldMessenger.of(context).hideCurrentSnackBar();
      ScaffoldMessenger.of(context).showSnackBar(
        SnackBar(
          content: Text('Failed to calculate route: $e'),
          backgroundColor: Colors.redAccent,
        ),
      );
    }
  }

  void _startTelemetryListening() {
    _pdrService.startTelemetryOnly();
  }

  void _stopTelemetryListening() {
    _pdrService.stopTelemetryOnly();
  }

  void _stopNavigation() {
    setState(() {
      _isNavigating = false;
      _activeGateClosureNotice = null;
      _staircaseCompleted = false;
      _stepsAtStairsZoneEnter = null;
      _startStaircaseCompleted = false;
      _stepsAtStartStairsZoneEnter = null;
      _pdrTrailIndex = 0;
      _pdrTrailLength = 0;
      _speedHistoryIndex = 0;
      _speedHistoryLength = 0;
      _routingPath.clear();
      _routeInstructions.clear();
      _routeInstructionIndices.clear();
      _currentInstructionIndex = 0;
      _hasAnnouncedArrival = false;
      _hasAnnouncedAdvanceWarning = false;
      _hasAnnouncedTurnNow = false;
      _lastAnnouncedInstruction = "";
    });
  }

  Future<void> _downloadApk() async {
    try {
      final base = Uri.base;
      final downloadUrl = Uri(
        scheme: base.scheme,
        host: base.host,
        port: base.port,
        path: '/app-release.apk',
      );
      final success = await launchUrl(downloadUrl, mode: LaunchMode.externalApplication);
      if (!success) {
        if (mounted) {
          ScaffoldMessenger.of(context).showSnackBar(
            const SnackBar(
              content: Text('Could not trigger APK download. Please try opening the link directly.'),
              behavior: SnackBarBehavior.floating,
            ),
          );
        }
      }
    } catch (e) {
      if (mounted) {
        ScaffoldMessenger.of(context).showSnackBar(
          SnackBar(
            content: Text('Error downloading APK: $e'),
            behavior: SnackBarBehavior.floating,
          ),
        );
      }
    }
  }

  Future<void> _downloadIpa() async {
    try {
      final base = Uri.base;
      final downloadUrl = Uri(
        scheme: base.scheme,
        host: base.host,
        port: base.port,
        path: '/app-release.ipa',
      );
      final success = await launchUrl(downloadUrl, mode: LaunchMode.externalApplication);
      if (!success) {
        if (mounted) {
          ScaffoldMessenger.of(context).showSnackBar(
            const SnackBar(
              content: Text('Could not trigger IPA download. Please make sure the file is hosted on the server.'),
              behavior: SnackBarBehavior.floating,
            ),
          );
        }
      }
    } catch (e) {
      if (mounted) {
        ScaffoldMessenger.of(context).showSnackBar(
          SnackBar(
            content: Text('Error downloading IPA: $e'),
            behavior: SnackBarBehavior.floating,
          ),
        );
      }
    }
  }

  void _showIosInstructionsDialog() {
    showDialog(
      context: context,
      builder: (context) => AlertDialog(
        backgroundColor: _cardBgColor,
        shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(24), side: BorderSide(color: _borderColor)),
        title: Row(
          children: [
            Icon(Icons.apple, color: _textColor),
            const SizedBox(width: 10),
            Text("Install on iOS", style: TextStyle(color: _textColor, fontWeight: FontWeight.bold)),
          ],
        ),
        content: Column(
          mainAxisSize: MainAxisSize.min,
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Text(
              "To run GECT Compass as a web app on iOS Safari:",
              style: TextStyle(color: _textColor, fontSize: 14, fontWeight: FontWeight.bold),
            ),
            const SizedBox(height: 16),
            _buildIosStep("1", "Open this website in your Safari browser."),
            const SizedBox(height: 12),
            _buildIosStep("2", "Tap the Share button at the bottom of Safari."),
            const SizedBox(height: 12),
            _buildIosStep("3", "Scroll down and select 'Add to Home Screen'."),
            const SizedBox(height: 20),
            Text(
              "Alternative option:",
              style: TextStyle(color: _textColor, fontSize: 13, fontWeight: FontWeight.bold),
            ),
            const SizedBox(height: 8),
            InkWell(
              onTap: () {
                Navigator.pop(context);
                _downloadIpa();
              },
              child: Row(
                children: [
                  const Icon(Icons.download, color: Color(0xFF3B82F6), size: 18),
                  const SizedBox(width: 8),
                  Text("Download iOS .ipa file directly", style: TextStyle(color: const Color(0xFF3B82F6), fontSize: 13, decoration: TextDecoration.underline)),
                ],
              ),
            ),
            const SizedBox(height: 16),
            Text(
              "Note: Sideloading raw .ipa files on iOS requires AltStore, Developer mode, or enterprise deployment. PWAs are recommended.",
              style: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 10, fontStyle: FontStyle.italic),
            ),
          ],
        ),
        actions: [
          TextButton(
            onPressed: () => Navigator.pop(context),
            child: const Text("Got It", style: TextStyle(color: Color(0xFF10B981), fontWeight: FontWeight.bold)),
          ),
        ],
      ),
    );
  }

  Widget _buildIosStep(String number, String text) {
    return Row(
      crossAxisAlignment: CrossAxisAlignment.start,
      children: [
        CircleAvatar(
          radius: 10,
          backgroundColor: const Color(0xFF10B981),
          child: Text(number, style: const TextStyle(color: Colors.white, fontSize: 11, fontWeight: FontWeight.bold)),
        ),
        const SizedBox(width: 10),
        Expanded(
          child: Text(
            text,
            style: TextStyle(color: _textColor.withValues(alpha: 0.8), fontSize: 13),
          ),
        ),
      ],
    );
  }

  void _showMorePanel() {
    showModalBottomSheet(
      context: context,
      backgroundColor: Colors.transparent,
      builder: (context) {
        return Container(
          padding: const EdgeInsets.all(24),
          decoration: BoxDecoration(
            color: _cardBgColor,
            borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
            border: Border.all(color: _borderColor.withValues(alpha: 0.5)),
          ),
          child: Column(
            mainAxisSize: MainAxisSize.min,
            children: [
              Container(
                width: 40,
                height: 4,
                margin: const EdgeInsets.only(bottom: 24),
                decoration: BoxDecoration(
                  color: Colors.grey.withValues(alpha: 0.3),
                  borderRadius: BorderRadius.circular(2),
                ),
              ),
              if (kIsWeb)
                ListTile(
                  leading: const Icon(Icons.install_mobile, color: Color(0xFF10B981)),
                  title: Text('Download Mobile App', style: TextStyle(color: _textColor)),
                  onTap: () {
                    Navigator.pop(context);
                    _showDownloadOptionsDialog();
                  },
                ),
              ListTile(
                leading: const Icon(Icons.share_location, color: Color(0xFF8B5CF6)),
                title: Text('Share Campus Grid Location', style: TextStyle(color: _textColor)),
                subtitle: _currentPosition != null
                    ? Text(
                        GridAddressingService.getCampusGridAddress(_currentPosition!),
                        style: TextStyle(color: const Color(0xFF8B5CF6).withValues(alpha: 0.8), fontSize: 11.5),
                      )
                    : null,
                onTap: () {
                  Navigator.pop(context);
                  if (_currentPosition != null) {
                    final grid = GridAddressingService.getCampusGridAddress(_currentPosition!);
                    final precisionGrid = GridAddressingService.getPrecisionGridAddress(_currentPosition!, decimals: 3);
                    final latStr = _currentPosition!.latitude.toStringAsFixed(7);
                    final lngStr = _currentPosition!.longitude.toStringAsFixed(7);
                    final shareUrl = (kIsWeb && Uri.base.host.isNotEmpty && !Uri.base.host.contains('localhost') && !Uri.base.host.contains('127.0.0.1'))
                        ? Uri.base.replace(queryParameters: {'grid': precisionGrid, 'lat': latStr, 'lng': lngStr}).toString()
                        : 'https://gecmaps.vercel.app/?grid=$precisionGrid&lat=$latStr&lng=$lngStr';
                    final shareMsg = "📍 My Live Campus Location (GEC Compass):\n"
                        "• High-Precision Grid: $precisionGrid\n"
                        "• GPS Coordinates: $latStr, $lngStr\n"
                        "• Open in GEC Compass: $shareUrl";
                    SharePlus.instance.share(ShareParams(text: shareMsg));
                  } else {
                    ScaffoldMessenger.of(context).showSnackBar(const SnackBar(content: Text("Location not available to share")));
                  }
                },
              ),
              ListTile(
                leading: const Icon(Icons.event, color: Color(0xFFF59E0B)),
                title: Text('Add Event Location', style: TextStyle(color: _textColor)),
                onTap: () {
                  Navigator.pop(context);
                  _showAddEventModal();
                },
              ),
            ],
          ),
        );
      },
    );
  }

  void _showAddEventModal() {
    final nameController = TextEditingController();
    final descriptionController = TextEditingController();
    DateTime startTime = DateTime.now();
    DateTime endTime = DateTime.now().add(const Duration(hours: 2));
    
    String locationType = 'current';
    Building? selectedExistingBuilding;

    final availableBuildings = _buildings
        .where((b) => b.tags['is_event'] != 'true' && b.name.isNotEmpty && b.name != 'Unnamed Location')
        .toList();
    availableBuildings.sort((a, b) => a.name.compareTo(b.name));

    showModalBottomSheet(
      context: context,
      backgroundColor: Colors.transparent,
      isScrollControlled: true,
      builder: (context) => StatefulBuilder(
        builder: (context, setModalState) {
          return Padding(
            padding: EdgeInsets.only(bottom: MediaQuery.of(context).viewInsets.bottom),
            child: SingleChildScrollView(
              child: Container(
                padding: const EdgeInsets.all(24),
                decoration: BoxDecoration(
                  color: _cardBgColor,
                  borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
                  border: Border.all(color: _borderColor.withValues(alpha: 0.5)),
                ),
                child: Column(
                  mainAxisSize: MainAxisSize.min,
                  crossAxisAlignment: CrossAxisAlignment.start,
                  children: [
                    Row(
                      children: [
                        const Icon(Icons.event, color: Color(0xFFF59E0B), size: 24),
                        const SizedBox(width: 10),
                        Text("Add Live Event Location", style: TextStyle(color: _textColor, fontSize: 18, fontWeight: FontWeight.bold)),
                      ],
                    ),
                    const SizedBox(height: 16),
                    TextField(
                      controller: nameController,
                      style: TextStyle(color: _textColor),
                      decoration: InputDecoration(
                        labelText: 'Event Name',
                        hintText: 'e.g. Tech Fest Main Stage / Seminar',
                        labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.6)),
                        border: OutlineInputBorder(borderRadius: BorderRadius.circular(12)),
                      ),
                    ),
                    const SizedBox(height: 14),
                    TextField(
                      controller: descriptionController,
                      maxLines: 2,
                      style: TextStyle(color: _textColor),
                      decoration: InputDecoration(
                        labelText: 'Event Description (Optional)',
                        hintText: 'Add details, schedule, or notes for attendees...',
                        labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.6)),
                        border: OutlineInputBorder(borderRadius: BorderRadius.circular(12)),
                      ),
                    ),
                    const SizedBox(height: 16),
                    Text("EVENT LOCATION", style: TextStyle(color: _textColor.withValues(alpha: 0.55), fontSize: 11, fontWeight: FontWeight.bold, letterSpacing: 0.8)),
                    const SizedBox(height: 8),
                    SegmentedButton<String>(
                      segments: const [
                        ButtonSegment(value: 'current', label: Text('Current GPS'), icon: Icon(Icons.my_location, size: 16)),
                        ButtonSegment(value: 'existing', label: Text('Existing Place'), icon: Icon(Icons.business, size: 16)),
                      ],
                      selected: {locationType},
                      onSelectionChanged: (val) {
                        setModalState(() {
                          locationType = val.first;
                        });
                      },
                    ),
                    if (locationType == 'existing') ...[
                      const SizedBox(height: 12),
                      DropdownButtonFormField<Building>(
                        dropdownColor: _cardBgColor,
                        initialValue: selectedExistingBuilding,
                        isExpanded: true,
                        style: TextStyle(color: _textColor, fontSize: 14),
                        decoration: InputDecoration(
                          labelText: 'Select Campus Location',
                          labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.6)),
                          border: OutlineInputBorder(borderRadius: BorderRadius.circular(12)),
                        ),
                        items: availableBuildings.map((b) {
                          return DropdownMenuItem<Building>(
                            value: b,
                            child: Text(b.name, overflow: TextOverflow.ellipsis),
                          );
                        }).toList(),
                        onChanged: (val) {
                          setModalState(() {
                            selectedExistingBuilding = val;
                          });
                        },
                      ),
                    ],
                    const SizedBox(height: 16),
                    Row(
                      children: [
                        Expanded(
                          child: ListTile(
                            contentPadding: EdgeInsets.zero,
                            title: Text("Start Time", style: TextStyle(color: _textColor, fontSize: 13)),
                            subtitle: Text("${startTime.hour.toString().padLeft(2,'0')}:${startTime.minute.toString().padLeft(2,'0')}", style: TextStyle(color: _textColor.withValues(alpha: 0.6))),
                            trailing: const Icon(Icons.access_time, size: 20),
                            onTap: () async {
                              final time = await showTimePicker(context: context, initialTime: TimeOfDay.fromDateTime(startTime));
                              if (time != null) {
                                setModalState(() {
                                  startTime = DateTime(startTime.year, startTime.month, startTime.day, time.hour, time.minute);
                                });
                              }
                            },
                          ),
                        ),
                        Expanded(
                          child: ListTile(
                            contentPadding: EdgeInsets.zero,
                            title: Text("End Time", style: TextStyle(color: _textColor, fontSize: 13)),
                            subtitle: Text("${endTime.hour.toString().padLeft(2,'0')}:${endTime.minute.toString().padLeft(2,'0')}", style: TextStyle(color: _textColor.withValues(alpha: 0.6))),
                            trailing: const Icon(Icons.access_time, size: 20),
                            onTap: () async {
                              final time = await showTimePicker(context: context, initialTime: TimeOfDay.fromDateTime(endTime));
                              if (time != null) {
                                setModalState(() {
                                  endTime = DateTime(endTime.year, endTime.month, endTime.day, time.hour, time.minute);
                                });
                              }
                            },
                          ),
                        ),
                      ],
                    ),
                    const SizedBox(height: 20),
                    SizedBox(
                      width: double.infinity,
                      height: 50,
                      child: ElevatedButton(
                        style: ElevatedButton.styleFrom(backgroundColor: const Color(0xFFF59E0B), shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12))),
                        onPressed: () async {
                          if (nameController.text.trim().isEmpty) {
                            ScaffoldMessenger.of(context).showSnackBar(const SnackBar(content: Text('Please enter an event name')));
                            return;
                          }
                          
                          if (locationType == 'existing' && selectedExistingBuilding == null) {
                            ScaffoldMessenger.of(context).showSnackBar(const SnackBar(content: Text('Please select an existing location')));
                            return;
                          }

                          final LatLng loc;
                          String? locationVenueName;
                          if (locationType == 'existing' && selectedExistingBuilding != null) {
                            loc = LatLng(selectedExistingBuilding!.lat, selectedExistingBuilding!.lng);
                            locationVenueName = selectedExistingBuilding!.name;
                          } else {
                            loc = _currentPosition ?? _campusCenter;
                          }

                          final descriptionText = descriptionController.text.trim();
                          
                          final newEvent = Building(
                            id: 'event_${DateTime.now().millisecondsSinceEpoch}',
                            name: nameController.text.trim(),
                            lat: loc.latitude,
                            lng: loc.longitude,
                            tags: {
                              'is_event': 'true',
                              'event_start': startTime.toIso8601String(),
                              'event_end': endTime.toIso8601String(),
                              'custom': 'true', 
                              if (descriptionText.isNotEmpty) 'description': descriptionText,
                              if (locationVenueName != null) 'venue': locationVenueName,
                            }
                          );
                          
                          final nav = Navigator.of(context);
                          final messenger = ScaffoldMessenger.of(context);

                          await _dataService.saveCustomBuilding(newEvent);
                          _buildings.add(newEvent);
                          
                          if (!mounted) return;
                          nav.pop();
                          messenger.showSnackBar(const SnackBar(content: Text('Event added successfully!')));
                          setState((){});
                        },
                        child: const Text('Publish Event', style: TextStyle(color: Colors.white, fontSize: 16, fontWeight: FontWeight.bold)),
                      ),
                    ),
                  ],
                ),
              ),
            ),
          );
        },
      ),
    );
  }

  void _showDownloadOptionsDialog() {
    showDialog(
      context: context,
      builder: (context) => AlertDialog(
        backgroundColor: _cardBgColor,
        shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(24), side: BorderSide(color: _borderColor)),
        title: Row(
          children: [
            Icon(Icons.download_for_offline, color: const Color(0xFF10B981)),
            const SizedBox(width: 10),
            Text("Download GECT Compass", style: TextStyle(color: _textColor, fontWeight: FontWeight.bold)),
          ],
        ),
        content: Column(
          mainAxisSize: MainAxisSize.min,
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Text(
              "Choose your platform to install the mobile application:",
              style: TextStyle(color: _textColor.withValues(alpha: 0.8), fontSize: 14),
            ),
            const SizedBox(height: 20),
            ListTile(
              contentPadding: EdgeInsets.zero,
              leading: Container(
                padding: const EdgeInsets.all(8),
                decoration: BoxDecoration(color: Colors.green.withValues(alpha: 0.15), shape: BoxShape.circle),
                child: const Icon(Icons.android, color: Colors.green),
              ),
              title: Text("Android App (.apk)", style: TextStyle(color: _textColor, fontWeight: FontWeight.bold)),
              subtitle: Text("Direct download & install on Android devices", style: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 11)),
              trailing: const Icon(Icons.chevron_right),
              onTap: () {
                Navigator.pop(context);
                _downloadApk();
              },
            ),
            const Divider(),
            ListTile(
              contentPadding: EdgeInsets.zero,
              leading: Container(
                padding: const EdgeInsets.all(8),
                decoration: BoxDecoration(color: Colors.blue.withValues(alpha: 0.15), shape: BoxShape.circle),
                child: const Icon(Icons.phone_iphone, color: Colors.blue),
              ),
              title: Text("iOS App (Safari PWA)", style: TextStyle(color: _textColor, fontWeight: FontWeight.bold)),
              subtitle: Text("Install directly without App Store using Safari", style: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 11)),
              trailing: const Icon(Icons.chevron_right),
              onTap: () {
                Navigator.pop(context);
                _showIosInstructionsDialog();
              },
            ),
          ],
        ),
        actions: [
          TextButton(
            onPressed: () => Navigator.pop(context),
            child: Text("Cancel", style: TextStyle(color: _textColor.withValues(alpha: 0.6))),
          ),
        ],
      ),
    );
  }





  List<Building>? _cachedFilteredBuildings;
  String? _lastFilterCategory;
  bool? _lastShowRooms;
  int _lastBuildingCount = 0;
  double _lastFilterZoom = 0.0; // Track zoom to invalidate showRooms cache at 17.5 threshold

  // Filter buildings on the map based on the active category chip
  List<Building> _getFilteredBuildings() {
    final showRooms = _selectedCategory == 'Rooms/Labs' || (_selectedCategory == 'All' && _currentZoom >= 17.5);
    // Also check if zoom crossed 17.5 threshold which changes showRooms
    final bool zoomCrossed = (_lastFilterZoom >= 17.5) != (_currentZoom >= 17.5);

    if (_cachedFilteredBuildings != null &&
        _lastFilterCategory == _selectedCategory &&
        _lastShowRooms == showRooms &&
        _lastBuildingCount == _buildings.length &&
        !zoomCrossed) {
      return _cachedFilteredBuildings!;
    }

    final filtered = _buildings.where((b) {
      if (b.tags['is_event'] == 'true') {
        final endTimeStr = b.tags['event_end'] as String?;
        if (endTimeStr != null) {
          final endTime = DateTime.tryParse(endTimeStr);
          if (endTime != null && DateTime.now().isAfter(endTime)) {
            return false;
          }
        }
      }

      final isRoom = b.tags['room'] == 'yes';
      final placeType = (b.tags['place_type'] ?? b.tags['type']) as String?;

      if (isRoom && !showRooms && placeType != 'Rooms/Labs') {
        return false;
      }

      if (_selectedCategory == 'All') {
        return true;
      }

      final resolvedCategory = _resolveBuildingCategory(b);
      return resolvedCategory == _selectedCategory;
    }).toList();

    _lastFilterCategory = _selectedCategory;
    _lastShowRooms = showRooms;
    _lastBuildingCount = _buildings.length;
    _lastFilterZoom = _currentZoom;
    _cachedFilteredBuildings = filtered;
    return filtered;
  }

  String _getTileUrl() {
    switch (_mapType) {
      case 'satellite':
        return 'https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}';
      case 'light':
        return 'https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png';
      case 'ambient':
      default:
        return 'https://{s}.basemaps.cartocdn.com/rastertiles/voyager/{z}/{x}/{y}{r}.png';
    }
  }


  void _showShareLocationModal(Building building) async {
    final shareUrl = await _dataService.getBaseShareUrl(building.id);
    final String shareText = "Find '${building.name}' on GEC Compass: $shareUrl";
    
    if (!mounted) return;

    showModalBottomSheet(
      context: context,
      backgroundColor: Colors.transparent,
      isScrollControlled: true,
      builder: (context) => ClipRRect(
        borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
        child: BackdropFilter(
          filter: ImageFilter.blur(sigmaX: 12, sigmaY: 12),
          child: Container(
            decoration: BoxDecoration(
              color: _cardBgColor.withValues(alpha: 0.85),
              borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
              border: Border.all(color: _borderColor),
              boxShadow: [
                BoxShadow(
                  color: Colors.black.withValues(alpha: _appThemeMode == 'light' ? 0.15 : 0.6),
                  blurRadius: 25,
                  spreadRadius: 8,
                )
              ],
            ),
            padding: const EdgeInsets.only(left: 24, right: 24, top: 16, bottom: 32),
            child: Column(
              mainAxisSize: MainAxisSize.min,
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                Center(
                  child: Container(
                    width: 46,
                    height: 5,
                    decoration: BoxDecoration(
                      color: _textColor.withValues(alpha: 0.2),
                      borderRadius: BorderRadius.circular(3),
                    ),
                  ),
                ),
                const SizedBox(height: 18),
                Row(
                  mainAxisAlignment: MainAxisAlignment.spaceBetween,
                  children: [
                    Text(
                      "Share Location",
                      style: TextStyle(
                        fontSize: 20,
                        fontWeight: FontWeight.bold,
                        color: _textColor,
                      ),
                    ),
                    IconButton(
                      icon: Icon(Icons.close, color: _textColor.withValues(alpha: 0.7)),
                      onPressed: () => Navigator.pop(context),
                    ),
                  ],
                ),
                const SizedBox(height: 8),
                Text(
                  "Choose how you want to share the location link for \"${building.name}\":",
                  style: TextStyle(color: _subTextColor, fontSize: 14),
                ),
                const SizedBox(height: 24),
                
                // Copy Link display box
                Container(
                  padding: const EdgeInsets.symmetric(horizontal: 14, vertical: 12),
                  decoration: BoxDecoration(
                    color: _scaffoldBgColor.withValues(alpha: 0.5),
                    borderRadius: BorderRadius.circular(14),
                    border: Border.all(color: _borderColor),
                  ),
                  child: Row(
                    children: [
                      Expanded(
                        child: Text(
                          shareUrl,
                          maxLines: 1,
                          overflow: TextOverflow.ellipsis,
                          style: TextStyle(color: _textColor.withValues(alpha: 0.8), fontSize: 13),
                        ),
                      ),
                      const SizedBox(width: 8),
                      TextButton.icon(
                        style: TextButton.styleFrom(
                          foregroundColor: const Color(0xFF3B82F6),
                          padding: const EdgeInsets.symmetric(horizontal: 12, vertical: 8),
                          backgroundColor: const Color(0xFF3B82F6).withValues(alpha: 0.1),
                          shape: RoundedRectangleBorder(
                            borderRadius: BorderRadius.circular(10),
                          ),
                        ),
                        icon: const Icon(Icons.copy, size: 16),
                        label: const Text("Copy", style: TextStyle(fontWeight: FontWeight.bold, fontSize: 13)),
                        onPressed: () async {
                          await Clipboard.setData(ClipboardData(text: shareUrl));
                          if (context.mounted) {
                            Navigator.pop(context);
                            _showShareSnackBar("Share link copied to clipboard!");
                          }
                        },
                      ),
                    ],
                  ),
                ),
                const SizedBox(height: 24),
                
                // Share options row
                Row(
                  mainAxisAlignment: MainAxisAlignment.spaceEvenly,
                  children: [
                    _buildShareOption(
                      icon: Icons.chat_bubble_outline_rounded,
                      color: const Color(0xFF25D366),
                      label: "WhatsApp",
                      onTap: () async {
                        final url = Uri.parse("https://wa.me/?text=${Uri.encodeComponent(shareText)}");
                        await _launchShareUrl(url);
                        if (context.mounted) Navigator.pop(context);
                      },
                    ),
                    _buildShareOption(
                      icon: Icons.send_rounded,
                      color: const Color(0xFF0088CC),
                      label: "Telegram",
                      onTap: () async {
                        final url = Uri.parse("https://t.me/share/url?url=${Uri.encodeComponent(shareUrl)}&text=${Uri.encodeComponent("Find '${building.name}' on GEC Compass!")}");
                        await _launchShareUrl(url);
                        if (context.mounted) Navigator.pop(context);
                      },
                    ),
                    _buildShareOption(
                      icon: Icons.mail_outline_rounded,
                      color: const Color(0xFFEA4335),
                      label: "Email",
                      onTap: () async {
                        final url = Uri.parse("mailto:?subject=${Uri.encodeComponent("Location on GEC Compass: ${building.name}")}&body=${Uri.encodeComponent(shareText)}");
                        await _launchShareUrl(url);
                        if (context.mounted) Navigator.pop(context);
                      },
                    ),
                    _buildShareOption(
                      icon: Icons.share_rounded,
                      color: const Color(0xFF64748B),
                      label: "System",
                      onTap: () async {
                        if (context.mounted) Navigator.pop(context);
                        try {
                          final RenderBox? box = context.findRenderObject() as RenderBox?;
                          await SharePlus.instance.share(
                            ShareParams(
                              text: shareText,
                              subject: "Find '${building.name}' on GEC Compass",
                              sharePositionOrigin: box != null ? (box.localToGlobal(Offset.zero) & box.size) : null,
                            ),
                          );
                        } catch (e) {
                          // fallback to copy clipboard
                          await Clipboard.setData(ClipboardData(text: shareText));
                          _showShareSnackBar("Share failed, link copied instead.");
                        }
                      },
                    ),
                  ],
                ),
              ],
            ),
          ),
        ),
      ),
    );
  }

  Widget _buildShareOption({
    required IconData icon,
    required Color color,
    required String label,
    required VoidCallback onTap,
  }) {
    return InkWell(
      onTap: onTap,
      borderRadius: BorderRadius.circular(16),
      child: Padding(
        padding: const EdgeInsets.symmetric(horizontal: 12, vertical: 8),
        child: Column(
          mainAxisSize: MainAxisSize.min,
          children: [
            Container(
              width: 56,
              height: 56,
              decoration: BoxDecoration(
                color: color.withValues(alpha: 0.15),
                shape: BoxShape.circle,
                border: Border.all(color: color.withValues(alpha: 0.3), width: 1.5),
              ),
              child: Icon(
                icon,
                color: color,
                size: 26,
              ),
            ),
            const SizedBox(height: 8),
            Text(
              label,
              style: TextStyle(
                fontSize: 12,
                fontWeight: FontWeight.w600,
                color: _textColor,
              ),
            ),
          ],
        ),
      ),
    );
  }

  Future<void> _launchShareUrl(Uri url) async {
    try {
      final success = await launchUrl(url, mode: LaunchMode.externalApplication);
      if (!success) {
        await Clipboard.setData(ClipboardData(text: url.toString()));
        _showShareSnackBar("Could not open app. Link copied to clipboard.");
      }
    } catch (e) {
      await Clipboard.setData(ClipboardData(text: url.toString()));
      _showShareSnackBar("Could not open app. Link copied to clipboard.");
    }
  }

  void _showShareSnackBar(String text) {
    if (!mounted) return;
    ScaffoldMessenger.of(context).showSnackBar(
      SnackBar(
        content: Row(
          children: [
            const Icon(Icons.check_circle, color: Colors.greenAccent, size: 20),
            const SizedBox(width: 8),
            Expanded(
              child: Text(
                text,
                style: const TextStyle(color: Colors.white),
              ),
            ),
          ],
        ),
        behavior: SnackBarBehavior.floating,
        backgroundColor: _cardBgColor,
        shape: RoundedRectangleBorder(
          borderRadius: BorderRadius.circular(12),
          side: BorderSide(color: _borderColor),
        ),
      ),
    );
  }

  void _showBuildingDetails(Building building) {
    final double? dist = _currentPosition != null
        ? _distanceMeters(_currentPosition!, LatLng(building.lat, building.lng))
        : null;

    showModalBottomSheet(
      context: context,
      backgroundColor: Colors.transparent,
      isScrollControlled: true,
      builder: (context) => ClipRRect(
        borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
        child: BackdropFilter(
          filter: ImageFilter.blur(sigmaX: 12, sigmaY: 12),
          child: Container(
            decoration: BoxDecoration(
              color: _cardBgColor.withValues(alpha: 0.85),
              borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
              border: Border.all(color: _borderColor),
              boxShadow: [
                BoxShadow(
                  color: Colors.black.withValues(alpha: _appThemeMode == 'light' ? 0.15 : 0.6),
                  blurRadius: 25,
                  spreadRadius: 8,
                )
              ],
            ),
        padding: const EdgeInsets.all(24),
        child: Column(
          mainAxisSize: MainAxisSize.min,
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Center(
              child: Container(
                width: 46,
                height: 5,
                decoration: BoxDecoration(
                  color: _textColor.withValues(alpha: 0.2),
                  borderRadius: BorderRadius.circular(3),
                ),
              ),
            ),
            const SizedBox(height: 24),
            if (building.photoUrl != null || building.photoBase64 != null || building.vpsBoardPhotoUrl != null || building.tags['image'] != null || building.tags['photoUrl'] != null) ...[
              GestureDetector(
                onTap: () => _showZoomablePhotoModal(context, building),
                child: Hero(
                  tag: 'building_photo_${building.id}',
                  child: ClipRRect(
                    borderRadius: BorderRadius.circular(16),
                    child: SizedBox(
                      height: 180,
                      width: double.infinity,
                      child: _buildPlaceThumbnailImage(building, size: double.infinity),
                    ),
                  ),
                ),
              ),
              const SizedBox(height: 18),
            ],
            Row(
              mainAxisAlignment: MainAxisAlignment.spaceBetween,
              children: [
                Expanded(
                  child: Text(
                    building.name,
                    style: TextStyle(
                      fontSize: 19,
                      fontWeight: FontWeight.bold,
                      color: _textColor,
                      letterSpacing: 0.2,
                    ),
                  ),
                ),
                Builder(
                  builder: (context) {
                    final String badgeLabel;
                    final bool isRoom = building.tags['room'] == 'yes';
                    final String placeType = building.tags['place_type']?.toString() ?? building.tags['building']?.toString() ?? '';

                    if (building.tags['is_event'] == 'true') {
                      badgeLabel = 'Live Event';
                    } else if (placeType == 'Washrooms' || placeType == 'Wash room' || building.tags['amenity'] == 'toilets' || building.name.toLowerCase().contains('washroom') || building.name.toLowerCase().contains('toilet')) {
                      badgeLabel = 'Washroom';
                    } else if (placeType == 'Departments' || building.tags['building'] == 'college') {
                      badgeLabel = 'Department';
                    } else if (isRoom || placeType == 'Rooms/Labs') {
                      badgeLabel = 'Lab / Room';
                    } else if (building.tags.containsKey('custom')) {
                      badgeLabel = 'Custom Place';
                    } else {
                      badgeLabel = '';
                    }

                    if (badgeLabel.isEmpty) return const SizedBox.shrink();

                    return Container(
                      padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 4),
                      decoration: BoxDecoration(
                        color: Colors.blueAccent.withValues(alpha: 0.15),
                        borderRadius: BorderRadius.circular(20),
                        border: Border.all(color: Colors.blueAccent.withValues(alpha: 0.3)),
                      ),
                      child: Text(
                        badgeLabel,
                        style: const TextStyle(color: Colors.blueAccent, fontSize: 11, fontWeight: FontWeight.bold),
                      ),
                    );
                  },
                ),
              ],
            ),
            const SizedBox(height: 12),
            Row(
              children: [
                const Icon(Icons.location_on, color: Color(0xFF3B82F6), size: 18),
                const SizedBox(width: 8),
                Expanded(
                  child: Text(
                    "${building.lat.toStringAsFixed(6)}, ${building.lng.toStringAsFixed(6)}",
                    style: TextStyle(color: _subTextColor, fontSize: 13),
                  ),
                ),
              ],
            ),
            if (building.tags['venue'] != null) ...[
              const SizedBox(height: 8),
              Row(
                children: [
                  const Icon(Icons.business, color: Color(0xFFF59E0B), size: 18),
                  const SizedBox(width: 8),
                  Expanded(
                    child: Text(
                      "Venue: ${building.tags['venue']}",
                      style: TextStyle(color: _textColor, fontSize: 13, fontWeight: FontWeight.w600),
                    ),
                  ),
                ],
              ),
            ],
            if (building.tags['description'] != null && (building.tags['description'] as String).isNotEmpty) ...[
              const SizedBox(height: 12),
              Container(
                width: double.infinity,
                padding: const EdgeInsets.all(12),
                decoration: BoxDecoration(
                  color: const Color(0xFFF59E0B).withValues(alpha: 0.1),
                  borderRadius: BorderRadius.circular(12),
                  border: Border.all(color: const Color(0xFFF59E0B).withValues(alpha: 0.3)),
                ),
                child: Column(
                  crossAxisAlignment: CrossAxisAlignment.start,
                  children: [
                    Row(
                      children: [
                        const Icon(Icons.info_outline, color: Color(0xFFF59E0B), size: 16),
                        const SizedBox(width: 6),
                        Text("EVENT DETAILS", style: TextStyle(color: const Color(0xFFF59E0B), fontSize: 11, fontWeight: FontWeight.bold)),
                      ],
                    ),
                    const SizedBox(height: 6),
                    Text(
                      building.tags['description'].toString(),
                      style: TextStyle(color: _textColor, fontSize: 13, height: 1.4),
                    ),
                  ],
                ),
              ),
            ],
            if (dist != null) ...[
              const SizedBox(height: 8),
              Row(
                children: [
                  const Icon(Icons.directions_walk, color: Color(0xFF10B981), size: 18),
                  const SizedBox(width: 8),
                  Text(
                    _formatDistance(dist),
                    style: const TextStyle(
                      color: Color(0xFF10B981),
                      fontWeight: FontWeight.w600,
                    ),
                  ),
                  Text(" away along paths", style: TextStyle(color: _subTextColor)),
                ],
              ),
            ],
            if (building.tags.isNotEmpty) ...[
              const SizedBox(height: 16),
              Wrap(
                spacing: 8,
                runSpacing: 6,
                children: building.tags.entries
                    .where((e) => ['amenity', 'building', 'tourism', 'cuisine', 'floor', 'ref'].contains(e.key))
                    .map((e) => Container(
                          padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 5),
                          decoration: BoxDecoration(
                            color: _scaffoldBgColor.withValues(alpha: 0.5),
                            borderRadius: BorderRadius.circular(12),
                            border: Border.all(color: _borderColor),
                          ),
                          child: Text(
                            "${e.key}: ${e.value}",
                            style: TextStyle(fontSize: 11, color: _textColor.withValues(alpha: 0.8)),
                          ),
                        ))
                    .toList(),
              ),
            ],
            
            // Render Contact Options (Call / WhatsApp) if phone exists
            () {
              final String? rawPhone = (building.tags['phone'] ?? building.tags['contact:phone']) as String?;
              final List<String> phoneNumbers = rawPhone != null 
                  ? rawPhone.split(';').map((p) => p.trim()).where((p) => p.isNotEmpty).toList()
                  : [];

              if (phoneNumbers.isEmpty) return const SizedBox.shrink();

              return Column(
                crossAxisAlignment: CrossAxisAlignment.start,
                children: [
                  const SizedBox(height: 18),
                  Text(
                    "CONTACT OPTIONS",
                    style: TextStyle(
                      color: _textColor.withValues(alpha: 0.55),
                      fontSize: 10,
                      fontWeight: FontWeight.bold,
                      letterSpacing: 1.0,
                    ),
                  ),
                  const SizedBox(height: 8),
                  ...phoneNumbers.map((phone) {
                    final cleanPhone = phone.replaceAll(RegExp(r'[^+\d]'), '');
                    final standardPhone = (cleanPhone.length == 10 && !cleanPhone.startsWith('+'))
                        ? '+91$cleanPhone'
                        : cleanPhone;

                    return Padding(
                      padding: const EdgeInsets.only(bottom: 8.0),
                      child: Container(
                        padding: const EdgeInsets.symmetric(horizontal: 14, vertical: 8),
                        decoration: BoxDecoration(
                          color: _scaffoldBgColor.withValues(alpha: 0.3),
                          borderRadius: BorderRadius.circular(14),
                          border: Border.all(color: _borderColor),
                        ),
                        child: Row(
                          children: [
                            Expanded(
                              child: Column(
                                crossAxisAlignment: CrossAxisAlignment.start,
                                children: [
                                  Text(
                                    phone,
                                    style: TextStyle(
                                      color: _textColor,
                                      fontSize: 14,
                                      fontWeight: FontWeight.bold,
                                    ),
                                  ),
                                  const SizedBox(height: 2),
                                  Text(
                                    "Tap icons to Call or Chat",
                                    style: TextStyle(
                                      color: _subTextColor,
                                      fontSize: 10,
                                    ),
                                  ),
                                ],
                              ),
                            ),
                            IconButton(
                              onPressed: () async {
                                final url = Uri.parse("tel:$standardPhone");
                                try {
                                  await launchUrl(url);
                                } catch (e) {
                                  if (!context.mounted) return;
                                  ScaffoldMessenger.of(context).showSnackBar(
                                    SnackBar(content: Text("Could not call $phone")),
                                  );
                                }
                              },
                              icon: const Icon(Icons.phone, size: 20),
                              style: IconButton.styleFrom(
                                foregroundColor: const Color(0xFF3B82F6),
                                backgroundColor: const Color(0xFF3B82F6).withValues(alpha: 0.12),
                                shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(10)),
                              ),
                            ),
                            const SizedBox(width: 8),
                            IconButton(
                              onPressed: () async {
                                final text = "Hello! I am using the GECT Compass app and wanted to query about ${building.name}.";
                                final url = Uri.parse("https://wa.me/${standardPhone.replaceAll('+', '').replaceAll(' ', '')}?text=${Uri.encodeComponent(text)}");
                                try {
                                  final success = await launchUrl(url, mode: LaunchMode.externalApplication);
                                  if (!success) throw Exception();
                                } catch (e) {
                                  if (!context.mounted) return;
                                  ScaffoldMessenger.of(context).showSnackBar(
                                    SnackBar(content: Text("Could not open WhatsApp for $phone")),
                                  );
                                }
                              },
                              icon: const Icon(Icons.chat, size: 20),
                              style: IconButton.styleFrom(
                                foregroundColor: const Color(0xFF10B981),
                                backgroundColor: const Color(0xFF10B981).withValues(alpha: 0.12),
                                shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(10)),
                              ),
                            ),
                          ],
                        ),
                      ),
                    );
                  }),
                ],
              );
            }(),
            
            const SizedBox(height: 24),
            SizedBox(
              width: double.infinity,
              child: ElevatedButton.icon(
                onPressed: () async {
                  Navigator.pop(context);
                  final isRoomDestination = building.tags.containsKey('room') || building.tags['room'] == 'yes' || building.tags['place_type'] == 'Rooms/Labs';
                  
                  int? selectedFloor;
                  if (isRoomDestination) {
                    selectedFloor = await _promptForCurrentFloor(context);
                  } else {
                    // For building-to-building navigation, assume ground floor (0)
                    selectedFloor = 0;
                  }
                  
                  if (selectedFloor != null) {
                    setState(() {
                      _userCurrentFloor = selectedFloor!;
                    });
                    _startNavigation();
                  }
                },
                icon: const Icon(Icons.directions_walk, color: Colors.white),
                label: const Text(
                  "Navigate Along Paths",
                  style: TextStyle(color: Colors.white, fontSize: 16, fontWeight: FontWeight.bold),
                ),
                style: ElevatedButton.styleFrom(
                  backgroundColor: const Color(0xFF3B82F6),
                  padding: const EdgeInsets.symmetric(vertical: 16),
                  shape: RoundedRectangleBorder(
                    borderRadius: BorderRadius.circular(16),
                  ),
                  elevation: 5,
                ),
              ),
            ),
            const SizedBox(height: 12),
            Row(
              children: [
                Expanded(
                  child: OutlinedButton.icon(
                    onPressed: () {
                      Navigator.pop(context);
                      _showEditPlaceModal(building);
                    },
                    icon: Icon(Icons.edit, color: _textColor, size: 18),
                    label: Text(
                      "Edit Info",
                      style: TextStyle(color: _textColor, fontSize: 14, fontWeight: FontWeight.bold),
                    ),
                    style: OutlinedButton.styleFrom(
                      padding: const EdgeInsets.symmetric(vertical: 14),
                      shape: RoundedRectangleBorder(
                        borderRadius: BorderRadius.circular(16),
                      ),
                      side: BorderSide(color: _borderColor),
                    ),
                  ),
                ),
                const SizedBox(width: 12),
                Expanded(
                  child: OutlinedButton.icon(
                    onPressed: () => _showShareLocationModal(building),
                    icon: Icon(Icons.share, color: _textColor, size: 18),
                    label: Text(
                      "Share Location",
                      style: TextStyle(color: _textColor, fontSize: 14, fontWeight: FontWeight.bold),
                    ),
                    style: OutlinedButton.styleFrom(
                      padding: const EdgeInsets.symmetric(vertical: 14),
                      shape: RoundedRectangleBorder(
                        borderRadius: BorderRadius.circular(16),
                      ),
                      side: BorderSide(color: _borderColor),
                    ),
                  ),
                ),
              ],
            ),
            const SizedBox(height: 12),
          ],
        ),
      ),
    ),
  ),
);
  }

  @override
  Widget build(BuildContext context) {
    final filteredBuildings = _getFilteredBuildings();

    if (_cachedThemeData == null || _lastThemeMode != _appThemeMode) {
      _lastThemeMode = _appThemeMode;
      _cachedThemeData = ThemeData(
        brightness: _appThemeMode == 'light' ? Brightness.light : Brightness.dark,
        primaryColor: _scaffoldBgColor,
        scaffoldBackgroundColor: _scaffoldBgColor,
        cardColor: _cardBgColor,
        colorScheme: ColorScheme(
          brightness: _appThemeMode == 'light' ? Brightness.light : Brightness.dark,
          primary: const Color(0xFF3B82F6),
          onPrimary: Colors.white,
          secondary: const Color(0xFF10B981),
          onSecondary: Colors.white,
          error: Colors.redAccent,
          onError: Colors.white,
          surface: _cardBgColor,
          onSurface: _textColor,
        ),
        useMaterial3: true,
      );
    }

    return Theme(
      data: _cachedThemeData!,
      child: Builder(
        builder: (context) {
          return Scaffold(
            backgroundColor: _scaffoldBgColor,
            body: Stack(
              children: [
                // Loading / Error / Map
                if (_isLoading)
                  const GradientLoadingOverlay(message: 'Initializing GEC Compass...')
                else if (_loadError != null)
                  Center(
                    child: Padding(
                      padding: const EdgeInsets.all(32),
                      child: Column(
                        mainAxisSize: MainAxisSize.min,
                        children: [
                          const Icon(Icons.error_outline, size: 48, color: Colors.redAccent),
                          const SizedBox(height: 16),
                          Text("Failed to load: $_loadError",
                              textAlign: TextAlign.center,
                              style: TextStyle(color: _textColor.withValues(alpha: 0.7))),
                          const SizedBox(height: 16),
                          ElevatedButton(onPressed: _initData, child: const Text("Retry")),
                        ],
                      ),
                    ),
                  )
                else
                  FlutterMap(
                    mapController: _mapController,
                    options: MapOptions(
                      initialCenter: _campusCenter,
                      initialZoom: 16.8,
                      minZoom: 14.5,
                      maxZoom: 22.0,
                      cameraConstraint: CameraConstraint.contain(
                        bounds: LatLngBounds(
                          const LatLng(10.5088, 76.1745),
                          const LatLng(10.5988, 76.2665),
                        ),
                      ),
                      onPositionChanged: (pos, hasGesture) {
                        if (hasGesture) {
                          FocusScope.of(context).unfocus();
                          if (_isAutoRecentering) {
                            setState(() {
                              _isAutoRecentering = false;
                            });
                          }
                        }
                        final newZoom = pos.zoom;
                        final wasZoomedIn = _currentZoom >= 18.1;
                        final isZoomedIn = newZoom >= 18.1;
                        if (wasZoomedIn != isZoomedIn) {
                          setState(() {
                            _currentZoom = newZoom;
                          });
                        } else {
                          _currentZoom = newZoom;
                        }
                      },
                      onTap: (tapPosition, point) {
                        FocusScope.of(context).unfocus();
                        if (!_isNavigating && GridAddressingService.isInsideCampusGrid(point)) {
                          final gridAddr = GridAddressingService.getCampusGridAddress(point);
                          final precisionGrid = GridAddressingService.getPrecisionGridAddress(point);
                          final tappedBuilding = Building(
                            id: 'grid_${gridAddr.replaceAll(' ', '_')}',
                            name: '📍 Grid Location ($gridAddr)',
                            lat: point.latitude,
                            lng: point.longitude,
                            tags: {
                              'place_type': 'Campus Grid Code',
                              'custom': 'true',
                              'grid_code': gridAddr,
                              'precision_grid': precisionGrid,
                            },
                          );
                          _selectBuilding(tappedBuilding);
                        }
                      },
                    ),
                    children: [
                      // Map Tile Layer (reflects active selected theme)
                      TileLayer(
                        key: ValueKey('map_tiles_$_mapType'),
                        urlTemplate: _getTileUrl(),
                        subdomains: const ['a', 'b', 'c', 'd'],
                        maxNativeZoom: 19,
                        keepBuffer: 5,
                        panBuffer: 2,
                        tileDisplay: const TileDisplay.instantaneous(),
                        userAgentPackageName: 'com.example.gec_compass_app',
                      ),
                      
                      // Campus boundary perimeter stroke
                      PolygonLayer(
                        polygons: [
                          Polygon(
                            points: _campusBoundaryPoints,
                            color: Colors.transparent,
                            borderColor: const Color(0xFF15803D),
                            borderStrokeWidth: 3.0,
                          ),
                        ],
                      ),
                      
                      // Polyline layer for road-snapped route with dynamic path shrinking
                      if (_isNavigating) ...[
                        ValueListenableBuilder<List<LatLng>>(
                          valueListenable: _routingPathNotifier,
                          builder: (context, activePath, _) {
                            return PolylineLayer(
                              polylines: [
                                // Access Walkway to Road (connector)
                                if (_startAccessPath.length >= 2)
                                  Polyline(
                                    points: _startAccessPath,
                                    color: const Color(0xFF60A5FA),
                                    strokeWidth: 4.0,
                                    borderStrokeWidth: 1.5,
                                    borderColor: Colors.white,
                                  ),
                                // Main Road Route — casing (dark blue outline)
                                if (activePath.length >= 2) ...[
                                  Polyline(
                                    points: activePath,
                                    color: const Color(0xFF1E40AF),
                                    strokeWidth: 9.0,
                                    strokeCap: StrokeCap.round,
                                    strokeJoin: StrokeJoin.round,
                                  ),
                                  // Main Road Route — fill (bright blue)
                                  Polyline(
                                    points: activePath,
                                    color: const Color(0xFF3B82F6),
                                    strokeWidth: 6.0,
                                    strokeCap: StrokeCap.round,
                                    strokeJoin: StrokeJoin.round,
                                  ),
                                ],
                                // Access Walkway from Road to Destination Door (connector)
                                if (_endAccessPath.length >= 2)
                                  Polyline(
                                    points: _endAccessPath,
                                    color: const Color(0xFF60A5FA),
                                    strokeWidth: 4.0,
                                    borderStrokeWidth: 1.5,
                                    borderColor: Colors.white,
                                  ),
                              ],
                            );
                          },
                        ),
                      ],
                      
                      // Building markers with dynamic zoom and navigation text labels (always upright & readable on screen rotation)
                      MarkerLayer(
                        rotate: true,
                        markers: filteredBuildings.map((b) {
                          final isSelected = _selectedBuilding?.id == b.id;
                          final isEvent = b.tags['is_event'] == 'true';
                          final bool showLabels = _isNavigating || _currentZoom >= 18.1 || isEvent;
                          final double markerWidth = isEvent ? 210.0 : (showLabels ? 140.0 : (isSelected ? 48.0 : 36.0));
                          final double markerHeight = isEvent ? 100.0 : (showLabels ? 64.0 : (isSelected ? 48.0 : 36.0));

                          if (isEvent) {
                            final venueName = b.tags['venue'] as String?;
                            return Marker(
                              key: ValueKey(b.id),
                              point: LatLng(b.lat, b.lng),
                              width: markerWidth,
                              height: markerHeight,
                              alignment: Alignment.bottomCenter,
                              rotate: true,
                              child: GestureDetector(
                                onTap: () => _selectBuilding(b),
                                child: Column(
                                  mainAxisSize: MainAxisSize.min,
                                  mainAxisAlignment: MainAxisAlignment.end,
                                  crossAxisAlignment: CrossAxisAlignment.center,
                                  children: [
                                    // Prominent Live Event & Location Tag Banner
                                    Container(
                                      padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 6),
                                      decoration: BoxDecoration(
                                        color: const Color(0xFF0F172A).withValues(alpha: 0.92),
                                        borderRadius: BorderRadius.circular(14),
                                        border: Border.all(color: const Color(0xFFEF4444), width: 1.8),
                                        boxShadow: [
                                          BoxShadow(
                                            color: Colors.redAccent.withValues(alpha: 0.3),
                                            blurRadius: 10,
                                            spreadRadius: 1,
                                            offset: const Offset(0, 3),
                                          )
                                        ],
                                      ),
                                      child: Column(
                                        mainAxisSize: MainAxisSize.min,
                                        children: [
                                          Row(
                                            mainAxisSize: MainAxisSize.min,
                                            children: [
                                              Container(
                                                padding: const EdgeInsets.symmetric(horizontal: 6, vertical: 2),
                                                decoration: BoxDecoration(
                                                  color: const Color(0xFFEF4444),
                                                  borderRadius: BorderRadius.circular(6),
                                                ),
                                                child: const Row(
                                                  mainAxisSize: MainAxisSize.min,
                                                  children: [
                                                    Icon(Icons.circle, color: Colors.white, size: 6),
                                                    SizedBox(width: 4),
                                                    Text('LIVE', style: TextStyle(color: Colors.white, fontSize: 10, fontWeight: FontWeight.w900, letterSpacing: 0.5)),
                                                  ],
                                                ),
                                              ),
                                              const SizedBox(width: 8),
                                              Flexible(
                                                child: Text(
                                                  b.name,
                                                  maxLines: 1,
                                                  overflow: TextOverflow.ellipsis,
                                                  style: const TextStyle(color: Colors.white, fontSize: 12, fontWeight: FontWeight.bold),
                                                ),
                                              ),
                                            ],
                                          ),
                                          if (venueName != null && venueName.isNotEmpty) ...[
                                            const SizedBox(height: 3),
                                            Row(
                                              mainAxisSize: MainAxisSize.min,
                                              children: [
                                                const Icon(Icons.location_on, color: Color(0xFFF59E0B), size: 12),
                                                const SizedBox(width: 3),
                                                Flexible(
                                                  child: Text(
                                                    "at $venueName",
                                                    maxLines: 1,
                                                    overflow: TextOverflow.ellipsis,
                                                    style: const TextStyle(color: Color(0xFFF59E0B), fontSize: 11, fontWeight: FontWeight.w600),
                                                  ),
                                                ),
                                              ],
                                            ),
                                          ],
                                        ],
                                      ),
                                    ),
                                    const SizedBox(height: 4),
                                    _buildMarkerIcon(b),
                                  ],
                                ),
                              ),
                            );
                          }

                          return Marker(
                            key: ValueKey(b.id),
                            point: LatLng(b.lat, b.lng),
                            width: markerWidth,
                            height: markerHeight,
                            alignment: showLabels ? Alignment.topCenter : Alignment.bottomCenter,
                            rotate: true,
                            child: GestureDetector(
                              onTap: () => _selectBuilding(b),
                              child: Column(
                                mainAxisSize: MainAxisSize.min,
                                mainAxisAlignment: MainAxisAlignment.start,
                                crossAxisAlignment: CrossAxisAlignment.center,
                                children: [
                                  _buildMarkerIcon(b),
                                  if (showLabels) ...[
                                    const SizedBox(height: 2),
                                    Text(
                                      b.name,
                                      maxLines: 1,
                                      overflow: TextOverflow.ellipsis,
                                      textAlign: TextAlign.center,
                                      style: TextStyle(
                                        color: isSelected ? const Color(0xFF059669) : Colors.black,
                                        fontSize: 11.0,
                                        fontWeight: FontWeight.bold,
                                        shadows: const [
                                          Shadow(
                                            offset: Offset(0, 1),
                                            blurRadius: 2.0,
                                            color: Colors.white,
                                          ),
                                          Shadow(
                                            offset: Offset(0, -1),
                                            blurRadius: 2.0,
                                            color: Colors.white,
                                          ),
                                        ],
                                      ),
                                    ),
                                  ],
                                ],
                              ),
                            ),
                          );
                        }).toList(),
                      ),
          
                      // User position marker (isolated rebuilds via ValueListenableBuilder)
                      ValueListenableBuilder<LatLng?>(
                        valueListenable: _positionNotifier,
                        builder: (context, userPos, child) {
                          if (userPos == null) return const SizedBox.shrink();
                          return MarkerLayer(
                            markers: [
                              Marker(
                                point: userPos,
                                width: 55,
                                height: 55,
                                alignment: Alignment.center,
                                child: _buildUserLocationMarker(),
                              )
                            ],
                          );
                        },
                      ),
                        
                      // Shared Grid Location Marker
                      if (_sharedGridLocation != null)
                        MarkerLayer(
                          rotate: true,
                          markers: [
                            Marker(
                              point: _sharedGridLocation!,
                              width: 140,
                              height: 64,
                              alignment: Alignment.topCenter,
                              rotate: true,
                              child: GestureDetector(
                                onTap: () {
                                  final gridAddr = GridAddressingService.getCampusGridAddress(_sharedGridLocation!);
                                  final sharedBuilding = Building(
                                    id: 'shared_location',
                                    name: 'Shared Location ($gridAddr)',
                                    lat: _sharedGridLocation!.latitude,
                                    lng: _sharedGridLocation!.longitude,
                                    tags: {'place_type': 'Shared Location', 'custom': 'true'},
                                  );
                                  _selectBuilding(sharedBuilding);
                                },
                                child: Column(
                                  mainAxisSize: MainAxisSize.min,
                                  children: [
                                    const Icon(Icons.location_on, color: Colors.redAccent, size: 40),
                                    Container(
                                      padding: const EdgeInsets.symmetric(horizontal: 6, vertical: 2),
                                      decoration: BoxDecoration(
                                        color: _bgOverlayColor,
                                        borderRadius: BorderRadius.circular(4),
                                      ),
                                      child: Text(
                                        "Shared Location", 
                                        style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.bold)
                                      ),
                                    ),
                                  ],
                                ),
                              ),
                            )
                          ],
                        ),
                    ],
                  ),
          
                // Location Permission Banner
                if (_locationDenied || _locationDeniedForever || _locationServiceDisabled)
                  Positioned(
                    top: MediaQuery.of(context).padding.top + 12,
                    left: 16,
                    right: 16,
                    child: GestureDetector(
                      onTap: _retryLocationPermission,
                      child: Container(
                        padding: const EdgeInsets.symmetric(horizontal: 16, vertical: 12),
                        decoration: BoxDecoration(
                          gradient: const LinearGradient(
                            colors: [Color(0xFFEF4444), Color(0xFFDC2626)],
                          ),
                          borderRadius: BorderRadius.circular(16),
                          boxShadow: [
                            BoxShadow(
                              color: const Color(0xFFEF4444).withValues(alpha: 0.4),
                              blurRadius: 12,
                              spreadRadius: 1,
                            ),
                          ],
                        ),
                        child: Row(
                          children: [
                            const Icon(Icons.location_off, color: Colors.white, size: 22),
                            const SizedBox(width: 12),
                            Expanded(
                              child: Column(
                                crossAxisAlignment: CrossAxisAlignment.start,
                                mainAxisSize: MainAxisSize.min,
                                children: [
                                  const Text(
                                    "Location Unavailable",
                                    style: TextStyle(color: Colors.white, fontWeight: FontWeight.bold, fontSize: 13),
                                  ),
                                  const SizedBox(height: 2),
                                  Text(
                                    _locationServiceDisabled
                                        ? "Turn on location services to use navigation."
                                        : _locationDeniedForever
                                            ? "Location permanently denied. Tap to open Settings."
                                            : "Allow location access for accurate navigation.",
                                    style: const TextStyle(color: Colors.white70, fontSize: 11),
                                  ),
                                ],
                              ),
                            ),
                            const SizedBox(width: 8),
                            GestureDetector(
                              onTap: _retryLocationPermission,
                              child: Container(
                                padding: const EdgeInsets.symmetric(horizontal: 14, vertical: 8),
                                decoration: BoxDecoration(
                                  color: Colors.white.withValues(alpha: 0.25),
                                  borderRadius: BorderRadius.circular(8),
                                  border: Border.all(color: Colors.white30, width: 1),
                                ),
                                child: Text(
                                  _locationServiceDisabled
                                      ? "Enable"
                                      : _locationDeniedForever
                                          ? "Settings"
                                          : "Allow",
                                  style: const TextStyle(color: Colors.white, fontWeight: FontWeight.bold, fontSize: 12),
                                ),
                              ),
                            ),
                          ],
                        ),
                      ),
                    ),
                  ),

                // Search Bar & Horizontal Category Filters (Top)
                if (!_isNavigating)
                  Positioned(
                    top: MediaQuery.of(context).padding.top + (_locationDenied || _locationDeniedForever || _locationServiceDisabled ? 90 : 12),
                    left: 16,
                    right: 16,
                    child: Column(
                      crossAxisAlignment: CrossAxisAlignment.start,
                      mainAxisSize: MainAxisSize.min,
                      children: [
                        // Modern Glassmorphism Search Bar with Animated Gradient Border
                        Autocomplete<Building>(
                          optionsBuilder: (TextEditingValue textEditingValue) {
                            if (textEditingValue.text.isEmpty) {
                              return const Iterable<Building>.empty();
                            }
                            final rawText = textEditingValue.text.trim();
                            final query = rawText.toLowerCase();

                            // 1. Instant GEC Campus Grid Code Resolution
                            final gridPos = GridAddressingService.getLatLngFromGridAddress(rawText);
                            if (gridPos != null) {
                              final canonicalGrid = GridAddressingService.getCampusGridAddress(gridPos);
                              final precisionGrid = GridAddressingService.getPrecisionGridAddress(gridPos);
                              final gridBuilding = Building(
                                id: 'grid_${canonicalGrid.replaceAll(' ', '_')}',
                                name: '📍 Grid Location ($canonicalGrid)',
                                lat: gridPos.latitude,
                                lng: gridPos.longitude,
                                tags: {
                                  'place_type': 'Campus Grid Code',
                                  'custom': 'true',
                                  'grid_code': canonicalGrid,
                                  'precision_grid': precisionGrid,
                                },
                              );
                              final rest = _buildings.where((Building option) {
                                final nameMatches = option.name.toLowerCase().contains(query);
                                final tagsStr = option.tags['search_tags']?.toString() ??
                                                option.tags['tags']?.toString() ??
                                                option.tags['keywords']?.toString() ??
                                                option.tags['alias']?.toString() ?? '';
                                return nameMatches || tagsStr.toLowerCase().contains(query);
                              });
                              return [gridBuilding, ...rest];
                            }

                            return _buildings.where((Building option) {
                              final nameMatches = option.name.toLowerCase().contains(query);
                              final tagsStr = option.tags['search_tags']?.toString() ??
                                              option.tags['tags']?.toString() ??
                                              option.tags['keywords']?.toString() ??
                                              option.tags['alias']?.toString() ?? '';
                              final tagsMatches = tagsStr.toLowerCase().contains(query);
                              final refMatches = option.tags['ref']?.toString().toLowerCase().contains(query) ?? false;
                              final parentMatches = option.tags['parent_name']?.toString().toLowerCase().contains(query) ?? false;
                              return nameMatches || tagsMatches || refMatches || parentMatches;
                            });
                          },
                          displayStringForOption: (Building option) => option.name,
                          onSelected: (Building selection) {
                            _selectBuilding(selection);
                          },
                          fieldViewBuilder: (BuildContext context,
                              TextEditingController textEditingController,
                              FocusNode focusNode,
                              VoidCallback onFieldSubmitted) {
                            return AnimatedBuilder(
                              animation: _searchGradientController,
                              builder: (context, child) {
                                final bool isSearchEmpty = textEditingController.text.isEmpty;
                                final double angle = _searchGradientController.value * 2 * pi;

                                return Container(
                                  decoration: BoxDecoration(
                                    borderRadius: BorderRadius.circular(30),
                                    gradient: isSearchEmpty
                                        ? SweepGradient(
                                            transform: GradientRotation(angle),
                                            colors: const [
                                              Color(0xFF2563EB), // Royal Blue
                                              Color(0xFF06B6D4), // Cyan
                                              Color(0xFF8B5CF6), // Violet
                                              Color(0xFFEC4899), // Pink
                                              Color(0xFF3B82F6), // Bright Blue
                                              Color(0xFF2563EB),
                                            ],
                                          )
                                        : null,
                                    boxShadow: [
                                      if (isSearchEmpty)
                                        BoxShadow(
                                          color: const Color(0xFF2563EB).withValues(alpha: 0.60),
                                          blurRadius: 24,
                                          spreadRadius: 3,
                                          offset: const Offset(0, 4),
                                        )
                                      else
                                        BoxShadow(
                                          color: Colors.black.withValues(alpha: _appThemeMode == 'light' ? 0.08 : 0.35),
                                          blurRadius: 18,
                                          spreadRadius: -2,
                                          offset: const Offset(0, 6),
                                        ),
                                    ],
                                  ),
                                  padding: EdgeInsets.all(isSearchEmpty ? 2.5 : 1.0),
                                  child: ClipRRect(
                                    borderRadius: BorderRadius.circular(28),
                                    child: BackdropFilter(
                                      filter: ImageFilter.blur(sigmaX: 16, sigmaY: 16),
                                      child: Container(
                                        decoration: BoxDecoration(
                                          color: _bgOverlayColor,
                                          borderRadius: BorderRadius.circular(28),
                                          border: isSearchEmpty ? null : Border.all(color: _borderColor, width: 1.2),
                                        ),
                                        child: child,
                                      ),
                                    ),
                                  ),
                                );
                              },
                              child: TextField(
                                controller: textEditingController,
                                focusNode: focusNode,
                                style: TextStyle(
                                  color: _textColor,
                                  fontSize: 15.5,
                                  fontWeight: FontWeight.w500,
                                  letterSpacing: 0.2,
                                ),
                                decoration: InputDecoration(
                                  hintText: 'Where do you want to go?',
                                  hintStyle: TextStyle(
                                    color: _textColor.withValues(alpha: 0.50),
                                    fontSize: 15.0,
                                    fontWeight: FontWeight.w400,
                                    letterSpacing: 0.1,
                                  ),
                                  prefixIcon: Padding(
                                    padding: const EdgeInsets.only(left: 10, right: 8),
                                    child: Container(
                                      width: 36,
                                      height: 36,
                                      decoration: BoxDecoration(
                                        color: const Color(0xFF2563EB).withValues(alpha: 0.14),
                                        shape: BoxShape.circle,
                                      ),
                                      child: const Icon(
                                        Icons.search_rounded,
                                        color: Color(0xFF2563EB),
                                        size: 20,
                                      ),
                                    ),
                                  ),
                                  prefixIconConstraints: const BoxConstraints(minWidth: 48, minHeight: 48),
                                  suffixIcon: textEditingController.text.isNotEmpty 
                                      ? IconButton(
                                          icon: Icon(Icons.cancel_rounded, color: _textColor.withValues(alpha: 0.5), size: 20),
                                          onPressed: () {
                                            textEditingController.clear();
                                          },
                                        )
                                      : Padding(
                                          padding: const EdgeInsets.only(right: 12),
                                          child: Icon(Icons.explore_outlined, color: _textColor.withValues(alpha: 0.40), size: 20),
                                        ),
                                  border: InputBorder.none,
                                  contentPadding: const EdgeInsets.symmetric(horizontal: 16, vertical: 16),
                                ),
                              ),
                            );
                          },
                                optionsViewBuilder: (BuildContext context,
                                    AutocompleteOnSelected<Building> onSelected,
                                    Iterable<Building> options) {
                                  return Align(
                                    alignment: Alignment.topLeft,
                                    child: Material(
                                      color: Colors.transparent,
                                      child: Container(
                                        width: MediaQuery.of(context).size.width - 32,
                                        margin: const EdgeInsets.only(top: 8),
                                        constraints: const BoxConstraints(maxHeight: 280),
                                        decoration: BoxDecoration(
                                          color: _cardBgColor,
                                          borderRadius: BorderRadius.circular(20),
                                          border: Border.all(color: _borderColor, width: 1.2),
                                          boxShadow: [
                                            BoxShadow(
                                                color: Colors.black.withValues(alpha: 0.35),
                                                blurRadius: 20,
                                                offset: const Offset(0, 8))
                                          ],
                                        ),
                                        child: ClipRRect(
                                          borderRadius: BorderRadius.circular(20),
                                          child: ListView.separated(
                                            padding: const EdgeInsets.symmetric(vertical: 6),
                                            shrinkWrap: true,
                                            itemCount: options.length,
                                            separatorBuilder: (c, i) => Divider(color: _borderColor.withValues(alpha: 0.5), height: 1),
                                            itemBuilder: (BuildContext context, int index) {
                                              final Building option = options.elementAt(index);
                                              return ListTile(
                                                contentPadding: const EdgeInsets.symmetric(horizontal: 16, vertical: 4),
                                                title: Text(option.name,
                                                    style: TextStyle(color: _textColor, fontSize: 14.5, fontWeight: FontWeight.w600)),
                                                subtitle: (option.tags['parent_name'] != null || option.tags['search_tags'] != null)
                                                    ? Text(
                                                        [
                                                          if (option.tags['parent_name'] != null) 'In: ${option.tags['parent_name']}',
                                                          if (option.tags['search_tags'] != null) 'Tags: ${option.tags['search_tags']}',
                                                        ].join(' • '),
                                                        style: TextStyle(color: _textColor.withValues(alpha: 0.6), fontSize: 12),
                                                        maxLines: 1,
                                                        overflow: TextOverflow.ellipsis,
                                                      )
                                                    : null,
                                                leading: Container(
                                                  padding: const EdgeInsets.all(8),
                                                  decoration: BoxDecoration(
                                                    color: _getMarkerColor(option).withValues(alpha: 0.12),
                                                    borderRadius: BorderRadius.circular(10),
                                                  ),
                                                  child: Icon(_getMarkerIcon(option),
                                                      color: _getMarkerColor(option), size: 18),
                                                ),
                                                trailing: const Icon(Icons.arrow_forward_ios_rounded, color: Colors.grey, size: 12),
                                                onTap: () {
                                                  onSelected(option);
                                                },
                                              );
                                            },
                                          ),
                                        ),
                                      ),
                                    ),
                                  );
                                },
                              ),
                        const SizedBox(height: 12),
                        
                        // Modern Category Filter Chips
                        SizedBox(
                          height: 42,
                          child: ListView.builder(
                            scrollDirection: Axis.horizontal,
                            itemCount: _categories.length,
                            itemBuilder: (context, index) {
                              final cat = _categories[index];
                              final isSelected = _selectedCategory == cat;
                              return Padding(
                                padding: const EdgeInsets.only(right: 8.0),
                                child: InkWell(
                                  onTap: () {
                                    setState(() {
                                      _selectedCategory = cat;
                                    });
                                  },
                                  borderRadius: BorderRadius.circular(22),
                                  child: AnimatedContainer(
                                    duration: const Duration(milliseconds: 200),
                                    padding: const EdgeInsets.symmetric(horizontal: 16, vertical: 10),
                                    decoration: BoxDecoration(
                                      color: isSelected
                                          ? const Color(0xFF3B82F6)
                                          : _cardBgColor.withValues(alpha: 0.7),
                                      borderRadius: BorderRadius.circular(22),
                                      border: Border.all(
                                        color: isSelected ? const Color(0xFF60A5FA) : _borderColor,
                                        width: 1.2,
                                      ),
                                      boxShadow: isSelected
                                          ? [
                                              BoxShadow(
                                                color: const Color(0xFF3B82F6).withValues(alpha: 0.4),
                                                blurRadius: 10,
                                                offset: const Offset(0, 4),
                                              )
                                            ]
                                          : [],
                                    ),
                                    child: Center(
                                      child: Text(
                                        cat,
                                        style: TextStyle(
                                          color: isSelected ? Colors.white : _textColor.withValues(alpha: 0.85),
                                          fontWeight: isSelected ? FontWeight.w700 : FontWeight.w500,
                                          fontSize: 13,
                                          letterSpacing: 0.2,
                                        ),
                                      ),
                                    ),
                                  ),
                                ),
                              );
                            },
                          ),
                        ),
                      ],
                    ),
                  ),
          
                // Floating Buttons on the right (responsive positioning)
                Positioned(
                  bottom: _isNavigating ? 140 : 32,
                  right: 16,
                  child: Column(
                    mainAxisSize: MainAxisSize.min,
                    children: [
                      // Telemetry Dashboard Toggle (Hidden on Web)
                      if (!kIsWeb) ...[
                        Container(
                          decoration: BoxDecoration(
                            shape: BoxShape.circle,
                            boxShadow: [
                              BoxShadow(
                                color: Colors.black.withValues(alpha: 0.15),
                                blurRadius: 8,
                                offset: const Offset(0, 4),
                              ),
                            ],
                          ),
                          child: ClipOval(
                            child: BackdropFilter(
                              filter: ImageFilter.blur(sigmaX: 8, sigmaY: 8),
                              child: FloatingActionButton(
                                heroTag: 'sensors_btn',
                                elevation: 0,
                                highlightElevation: 0,
                                backgroundColor: _showSensorDashboard 
                                    ? const Color(0xFF10B981).withValues(alpha: 0.85) 
                                    : _cardBgColor.withValues(alpha: 0.7),
                                foregroundColor: _showSensorDashboard ? Colors.white : const Color(0xFF3B82F6),
                                onPressed: () {
                                  setState(() {
                                    _showSensorDashboard = !_showSensorDashboard;
                                    _showLayerSelector = false;
                                    if (_showSensorDashboard) {
                                      _startTelemetryListening();
                                    } else {
                                      if (!_isNavigating) {
                                        _stopTelemetryListening();
                                      }
                                    }
                                  });
                                },
                                child: Icon(_showSensorDashboard ? Icons.sensors : Icons.sensors_off),
                              ),
                            ),
                          ),
                        ),
                        const SizedBox(height: 14),
                      ],
                      // Theme/Layer Switcher Button (Visible during navigation!)
                      Container(
                        decoration: BoxDecoration(
                          shape: BoxShape.circle,
                          boxShadow: [
                            BoxShadow(
                              color: Colors.black.withValues(alpha: 0.15),
                              blurRadius: 8,
                              offset: const Offset(0, 4),
                            ),
                          ],
                        ),
                        child: ClipOval(
                          child: BackdropFilter(
                            filter: ImageFilter.blur(sigmaX: 8, sigmaY: 8),
                            child: FloatingActionButton(
                              heroTag: 'layer_btn',
                              elevation: 0,
                              highlightElevation: 0,
                              backgroundColor: _cardBgColor.withValues(alpha: 0.7),
                              foregroundColor: const Color(0xFF3B82F6),
                              onPressed: () {
                                setState(() {
                                  _showLayerSelector = !_showLayerSelector;
                                });
                              },
                              child: const Icon(Icons.layers),
                            ),
                          ),
                        ),
                      ),
                      const SizedBox(height: 14),
                      if (!_isNavigating) ...[
                        // Add Place Button
                        Container(
                          decoration: BoxDecoration(
                            shape: BoxShape.circle,
                            boxShadow: [
                              BoxShadow(
                                color: Colors.black.withValues(alpha: 0.15),
                                blurRadius: 8,
                                offset: const Offset(0, 4),
                              ),
                            ],
                          ),
                          child: ClipOval(
                            child: BackdropFilter(
                              filter: ImageFilter.blur(sigmaX: 8, sigmaY: 8),
                              child: FloatingActionButton(
                                heroTag: 'add_place_btn',
                                elevation: 0,
                                highlightElevation: 0,
                                backgroundColor: const Color(0xFF3B82F6).withValues(alpha: 0.85),
                                foregroundColor: Colors.white,
                                onPressed: _showAddPlaceModal,
                                child: const Icon(Icons.add_location_alt),
                              ),
                            ),
                          ),
                        ),
                        const SizedBox(height: 14),
                      ],
                      if (!_isNavigating) ...[
                        // More Button
                        Container(
                          decoration: BoxDecoration(
                            shape: BoxShape.circle,
                            boxShadow: [
                              BoxShadow(
                                color: Colors.black.withValues(alpha: 0.15),
                                blurRadius: 8,
                                offset: const Offset(0, 4),
                              ),
                            ],
                          ),
                          child: ClipOval(
                            child: BackdropFilter(
                              filter: ImageFilter.blur(sigmaX: 8, sigmaY: 8),
                              child: FloatingActionButton(
                                heroTag: 'more_btn',
                                elevation: 0,
                                highlightElevation: 0,
                                backgroundColor: _cardBgColor.withValues(alpha: 0.85),
                                foregroundColor: _textColor,
                                tooltip: 'More Options',
                                onPressed: _showMorePanel,
                                child: const Icon(Icons.more_horiz),
                              ),
                            ),
                          ),
                        ),
                        const SizedBox(height: 14),
                      ],
                      // Recenter Button
                      Container(
                        decoration: BoxDecoration(
                          shape: BoxShape.circle,
                          boxShadow: [
                            BoxShadow(
                              color: Colors.black.withValues(alpha: 0.15),
                              blurRadius: 8,
                              offset: const Offset(0, 4),
                            ),
                          ],
                        ),
                        child: ClipOval(
                          child: BackdropFilter(
                            filter: ImageFilter.blur(sigmaX: 8, sigmaY: 8),
                            child: FloatingActionButton(
                              heroTag: 'recenter_btn',
                              elevation: 0,
                              highlightElevation: 0,
                              backgroundColor: _cardBgColor.withValues(alpha: 0.7),
                              foregroundColor: _isAutoRecentering ? const Color(0xFF3B82F6) : _textColor.withValues(alpha: 0.6),
                              onPressed: _recenterOnUserLocation,
                              child: Icon(_isAutoRecentering ? Icons.my_location : Icons.location_searching),
                            ),
                          ),
                        ),
                      ),
                    ],
                  ),
                ),
          
                // Theme & Layer Selector Panel
                if (_showLayerSelector)
                  Positioned(
                    bottom: _isNavigating ? 210 : 222,
                    right: 16,
                    child: ClipRRect(
                      borderRadius: BorderRadius.circular(20),
                      child: BackdropFilter(
                        filter: ImageFilter.blur(sigmaX: 10, sigmaY: 10),
                        child: Container(
                          padding: const EdgeInsets.all(16),
                          decoration: BoxDecoration(
                            color: _bgOverlayColor,
                            borderRadius: BorderRadius.circular(20),
                            border: Border.all(color: _borderColor),
                            boxShadow: [
                              BoxShadow(
                                color: Colors.black.withValues(alpha: 0.3),
                                blurRadius: 15,
                              )
                            ],
                          ),
                          child: Column(
                            mainAxisSize: MainAxisSize.min,
                            crossAxisAlignment: CrossAxisAlignment.start,
                            children: [
                              Text(
                                "Theme & Map Layer",
                                style: TextStyle(
                                  color: _textColor,
                                  fontWeight: FontWeight.bold,
                                  fontSize: 14,
                                ),
                              ),
                              const SizedBox(height: 14),
                              Row(
                                children: [
                                  _buildLayerOption('light', Icons.light_mode, 'Light'),
                                  const SizedBox(width: 14),
                                  _buildLayerOption('ambient', Icons.palette, 'Ambient'),
                                  const SizedBox(width: 14),
                                  _buildLayerOption('satellite', Icons.satellite_alt, 'Satellite'),
                                ],
                              ),
                            ],
                          ),
                        ),
                      ),
                    ),
                  ),

                // Feedback Button
                if (!_isNavigating)
                  Positioned(
                    bottom: 32,
                    left: 16,
                    child: Container(
                      decoration: BoxDecoration(
                        borderRadius: BorderRadius.circular(30),
                        boxShadow: [
                          BoxShadow(
                            color: Colors.black.withValues(alpha: 0.15),
                            blurRadius: 8,
                            offset: const Offset(0, 4),
                          ),
                        ],
                      ),
                      child: ClipRRect(
                        borderRadius: BorderRadius.circular(30),
                        child: BackdropFilter(
                          filter: ImageFilter.blur(sigmaX: 8, sigmaY: 8),
                          child: FloatingActionButton.extended(
                            heroTag: 'feedback_btn',
                            elevation: 0,
                            highlightElevation: 0,
                            backgroundColor: const Color(0xFF10B981).withValues(alpha: 0.85),
                            foregroundColor: Colors.white,
                            icon: const Icon(Icons.rate_review),
                            label: const Text('Feedback',
                                style: TextStyle(fontWeight: FontWeight.bold, letterSpacing: 0.5)),
                            onPressed: _showFeedbackModal,
                          ),
                        ),
                      ),
                    ),
                  ),
          

          
                // Telemetry Sensor Dashboard Overlay (Hidden on Web)
                if (_showSensorDashboard && !kIsWeb)
                  Positioned(
                    top: MediaQuery.of(context).padding.top + 80,
                    left: 16,
                    child: ValueListenableBuilder<TelemetryData>(
                      valueListenable: _telemetryNotifier,
                      builder: (context, telemetry, child) {
                        return _buildSensorDashboardWidget(context, telemetry);
                      },
                    ),
                  ),

                // Navigation UI Overlay
                if (_isNavigating) _buildNavigationOverlay(),
          
                // Welcome Onboarding Overlay
                if (_showOnboarding) _buildOnboardingOverlay(),
              ],
            ),
          );
        }
      ),
    );
  }

  Widget _buildLayerOption(String type, IconData icon, String label) {
    final isSelected = _mapType == type;
    final color = isSelected ? const Color(0xFF3B82F6) : _cardBgColor.withValues(alpha: 0.6);
    
    return GestureDetector(
      onTap: () {
        setState(() {
          _mapType = type;
          if (type != 'satellite') {
            _appThemeMode = type;
          }
          _showLayerSelector = false;
        });
      },
      child: Column(
        children: [
          Container(
            padding: const EdgeInsets.all(12),
            decoration: BoxDecoration(
              color: color,
              shape: BoxShape.circle,
              border: Border.all(
                color: isSelected ? const Color(0xFF3B82F6) : _borderColor,
                width: 1.5,
              ),
            ),
            child: Icon(
              icon,
              color: isSelected ? Colors.white : _textColor.withValues(alpha: 0.8),
              size: 22,
            ),
          ),
          const SizedBox(height: 6),
          Text(
            label,
            style: TextStyle(
              color: isSelected ? const Color(0xFF3B82F6) : _textColor.withValues(alpha: 0.8),
              fontSize: 11,
              fontWeight: isSelected ? FontWeight.bold : FontWeight.normal,
            ),
          ),
        ],
      ),
    );
  }

  // Draw user position with smooth pulsing outer glow
  Widget _buildUserLocationMarker() {
    return ValueListenableBuilder<TelemetryData>(
      valueListenable: _telemetryNotifier,
      builder: (context, telemetry, child) {
        final headingRad = telemetry.heading * (pi / 180.0);
        return AnimatedBuilder(
          animation: _pulseController,
          builder: (context, child) {
            return Stack(
              alignment: Alignment.center,
              children: [
                // Directional Beam (pointing forward, Google Maps style)
                Transform.rotate(
                  angle: headingRad,
                  child: CustomPaint(
                    size: const Size(65, 65),
                    painter: DirectionBeamPainter(),
                  ),
                ),
                // Pulsing background circle
                Container(
                  width: 26 + _pulseController.value * 16,
                  height: 26 + _pulseController.value * 16,
                  decoration: BoxDecoration(
                    shape: BoxShape.circle,
                    color: const Color(0xFF3B82F6).withValues(alpha: 0.25 * (1.0 - _pulseController.value)),
                  ),
                ),
                // Blue outer circle border with white core
                Container(
                  width: 22,
                  height: 22,
                  decoration: BoxDecoration(
                    shape: BoxShape.circle,
                    color: Colors.white,
                    boxShadow: [
                      BoxShadow(
                        color: Colors.black.withValues(alpha: 0.2),
                        blurRadius: 4,
                        offset: const Offset(0, 2),
                      )
                    ],
                  ),
                  child: Center(
                    child: Container(
                      width: 18,
                      height: 18,
                      decoration: const BoxDecoration(
                        shape: BoxShape.circle,
                        color: Color(0xFF3B82F6),
                      ),
                      child: Center(
                        // Google Maps style navigation arrow
                        child: Transform.rotate(
                          angle: headingRad,
                          child: const Icon(
                            Icons.navigation,
                            color: Colors.white,
                            size: 11,
                          ),
                        ),
                      ),
                    ),
                  ),
                ),
              ],
            );
          },
        );
      },
    );
  }

  Widget _buildMarkerIcon(Building b) {
    final isSelected = _selectedBuilding?.id == b.id;
    final isEvent = b.tags['is_event'] == 'true';
    final color = isSelected ? Colors.greenAccent : _getMarkerColor(b);
    final icon = _getMarkerIcon(b);

    if (isEvent) {
      return AnimatedBuilder(
        animation: _pulseController,
        builder: (context, child) {
          return Stack(
            alignment: Alignment.center,
            children: [
              // Pulsing outer aura ring
              Container(
                width: 42.0 + _pulseController.value * 14.0,
                height: 42.0 + _pulseController.value * 14.0,
                decoration: BoxDecoration(
                  shape: BoxShape.circle,
                  color: const Color(0xFFEF4444).withValues(alpha: 0.35 * (1.0 - _pulseController.value)),
                ),
              ),
              // Main Glowing Pin Point Circle
              Container(
                width: 38,
                height: 38,
                decoration: BoxDecoration(
                  shape: BoxShape.circle,
                  gradient: const LinearGradient(
                    colors: [Color(0xFFEF4444), Color(0xFFF59E0B)],
                    begin: Alignment.topLeft,
                    end: Alignment.bottomRight,
                  ),
                  border: Border.all(color: Colors.white, width: 2.5),
                  boxShadow: [
                    BoxShadow(
                      color: Colors.redAccent.withValues(alpha: 0.5),
                      blurRadius: 10,
                      spreadRadius: 2,
                    ),
                  ],
                ),
                child: const Center(
                  child: Icon(Icons.stars, color: Colors.white, size: 20),
                ),
              ),
            ],
          );
        },
      );
    }

    final double pinSize = isSelected ? 48.0 : 36.0;
    final double innerCircleSize = isSelected ? 18.0 : 13.0;
    final double iconSize = isSelected ? 13.0 : 9.0;
    final double offsetUp = isSelected ? -5.0 : -3.5;

    if (!isSelected) {
      return Stack(
        alignment: Alignment.center,
        children: [
          Icon(
            Icons.location_on,
            color: color,
            size: pinSize,
          ),
          Transform.translate(
            offset: Offset(0, offsetUp),
            child: Container(
              width: innerCircleSize,
              height: innerCircleSize,
              decoration: const BoxDecoration(
                shape: BoxShape.circle,
                color: Colors.white,
              ),
              child: Center(
                child: Icon(
                  icon,
                  color: color,
                  size: iconSize,
                ),
              ),
            ),
          ),
        ],
      );
    }

    return AnimatedBuilder(
      animation: _pulseController,
      builder: (context, child) {
        return Stack(
          alignment: Alignment.center,
          children: [
            Transform.translate(
              offset: Offset(0, offsetUp),
              child: Container(
                width: innerCircleSize + _pulseController.value * 20,
                height: innerCircleSize + _pulseController.value * 20,
                decoration: BoxDecoration(
                  shape: BoxShape.circle,
                  color: color.withValues(alpha: 0.4 * (1.0 - _pulseController.value)),
                ),
              ),
            ),
            Icon(
              Icons.location_on,
              color: color,
              size: pinSize,
            ),
            Transform.translate(
              offset: Offset(0, offsetUp),
              child: Container(
                width: innerCircleSize,
                height: innerCircleSize,
                decoration: const BoxDecoration(
                  shape: BoxShape.circle,
                  color: Colors.white,
                ),
                child: Center(
                  child: Icon(
                    icon,
                    color: color,
                    size: iconSize,
                  ),
                ),
              ),
            ),
          ],
        );
      },
    );
  }

  double get _calculatedSpeed {
    if (_navMode == 'walking') {
      return 1.3;
    } else if (_navMode == 'cycling') {
      return 4.5;
    } else { // auto mode
      if (_speedHistoryLength == 0) return 1.3;
      double sum = 0.0;
      for (int i = 0; i < _speedHistoryLength; i++) {
        sum += _speedHistory[i];
      }
      final avg = sum / _speedHistoryLength;
      if (avg < 0.5) return 1.3;
      return avg.clamp(0.5, 10.0);
    }
  }

  Widget _buildModeChip(String mode, IconData icon, String label) {
    final isSelected = _navMode == mode;
    return GestureDetector(
      onTap: () {
        HapticFeedback.selectionClick();
        setState(() {
          _navMode = mode;
        });
      },
      child: AnimatedContainer(
        duration: const Duration(milliseconds: 250),
        padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 5),
        decoration: BoxDecoration(
          color: isSelected 
              ? const Color(0xFF10B981) 
              : (_appThemeMode == 'light' ? Colors.black.withValues(alpha: 0.05) : Colors.white.withValues(alpha: 0.05)),
          borderRadius: BorderRadius.circular(16),
          border: Border.all(
            color: isSelected ? Colors.transparent : _borderColor,
          ),
        ),
        child: Row(
          mainAxisSize: MainAxisSize.min,
          children: [
            Icon(icon, size: 14, color: isSelected ? Colors.white : _textColor),
            const SizedBox(width: 4),
            Text(
              label,
              style: TextStyle(
                color: isSelected ? Colors.white : _textColor.withValues(alpha: 0.8),
                fontSize: 11.5,
                fontWeight: isSelected ? FontWeight.bold : FontWeight.normal,
              ),
            ),
          ],
        ),
      ),
    );
  }

  Widget _buildNavigationOverlay() {
    if (_selectedBuilding == null || _currentPosition == null) return const SizedBox.shrink();

    final dist = _distanceMeters(_currentPosition!, LatLng(_selectedBuilding!.lat, _selectedBuilding!.lng));
    double pathDistance = 0.0;
    if (_routingPath.length >= 2) {
      for (int i = 0; i < _routingPath.length - 1; i++) {
        pathDistance += _distanceMeters(_routingPath[i], _routingPath[i + 1]);
      }
    } else {
      pathDistance = dist;
    }
    final floorTag = _selectedBuilding!.tags['floor'];
    
    String primaryInstruction = "Head towards ${_selectedBuilding!.name}";
    String secondaryInstruction = "Follow the highlighted path on the map.";
    IconData turnIcon = Icons.straight_rounded;
    Color topBarColor = const Color(0xFF0F9D58); // Green for active nav

    if (_routeInstructions.isNotEmpty) {
      if (_currentInstructionIndex < _routeInstructions.length - 1) {
        final double distToNext = _distanceToNextTurn(_currentPosition!);
        final nextInst = _routeInstructions[_currentInstructionIndex + 1];
        if (distToNext <= 8.0) {
          primaryInstruction = _extractShortTurnAction(nextInst);
          secondaryInstruction = nextInst;
        } else {
          primaryInstruction = "In ${distToNext.round()} m";
          secondaryInstruction = nextInst;
        }
      } else {
        primaryInstruction = _routeInstructions[_currentInstructionIndex];
        secondaryInstruction = "Arriving at ${_selectedBuilding!.name}";
      }
    }

    final String act = '$primaryInstruction $secondaryInstruction'.toLowerCase();
    if (act.contains('sharp right')) {
      turnIcon = Icons.turn_sharp_right_rounded;
    } else if (act.contains('sharp left')) {
      turnIcon = Icons.turn_sharp_left_rounded;
    } else if (act.contains('slight right')) {
      turnIcon = Icons.turn_slight_right_rounded;
    } else if (act.contains('slight left')) {
      turnIcon = Icons.turn_slight_left_rounded;
    } else if (act.contains('turn right') || act.contains('right')) {
      turnIcon = Icons.turn_right_rounded;
    } else if (act.contains('turn left') || act.contains('left')) {
      turnIcon = Icons.turn_left_rounded;
    } else if (act.contains('gate')) {
      turnIcon = Icons.sensor_door_rounded;
    } else if (act.contains('arrive')) {
      turnIcon = Icons.place_rounded;
    } else {
      turnIcon = Icons.straight_rounded;
    }

    int destFloor = 0;
    if (floorTag != null) {
      final String fs = floorTag.toString().trim().toLowerCase();
      if (fs == 'ground' || fs == 'g') {
        destFloor = 0;
      } else {
        destFloor = int.tryParse(fs) ?? 0;
      }
    }

    // 1. Check if user starts on an upper floor and must descend first to walk along campus paths
    final bool showStartStairs = dist >= 15.0 && _userCurrentFloor > 0 && !_startStaircaseCompleted;
    int startStepsWalkedInZone = 0;
    int startTargetSteps = 18;

    if (showStartStairs) {
      final int floorsToDescend = _userCurrentFloor;
      startTargetSteps = floorsToDescend > 0 ? floorsToDescend * 18 : 18;

      _stepsAtStartStairsZoneEnter ??= _stepCount;
      startStepsWalkedInZone = _stepCount - _stepsAtStartStairsZoneEnter!;
      if (startStepsWalkedInZone < 0) {
        _stepsAtStartStairsZoneEnter = _stepCount;
        startStepsWalkedInZone = 0;
      }

      if (startStepsWalkedInZone >= startTargetSteps) {
        WidgetsBinding.instance.addPostFrameCallback((_) {
          if (mounted && !_startStaircaseCompleted) {
            HapticFeedback.mediumImpact();
            setState(() {
              _startStaircaseCompleted = true;
              _userCurrentFloor = 0;
            });
          }
        });
      }
    }

    // 2. Check if user has arrived at destination building (or starts nearby) and needs to climb/descend stairs
    final bool showStairs = !showStartStairs &&
                            dist < 15.0 && 
                            floorTag != null && 
                            floorTag.toString().isNotEmpty && 
                            _userCurrentFloor != destFloor &&
                            !(destFloor == 0 && _userCurrentFloor == 0) &&
                            !_staircaseCompleted;

    int stepsWalkedInZone = 0;
    int targetSteps = 18;

    if (showStairs) {
      final int floorsToClimb = (destFloor - _userCurrentFloor).abs();
      targetSteps = floorsToClimb > 0 ? floorsToClimb * 18 : 18;

      _stepsAtStairsZoneEnter ??= _stepCount;
      stepsWalkedInZone = _stepCount - _stepsAtStairsZoneEnter!;
      if (stepsWalkedInZone < 0) {
        _stepsAtStairsZoneEnter = _stepCount;
        stepsWalkedInZone = 0;
      }

      if (stepsWalkedInZone >= targetSteps) {
        WidgetsBinding.instance.addPostFrameCallback((_) {
          if (mounted && !_staircaseCompleted) {
            HapticFeedback.mediumImpact();
            setState(() {
              _staircaseCompleted = true;
              _userCurrentFloor = destFloor;
            });
          }
        });
      }
    }

    final bool isRoom = _selectedBuilding!.tags['room'] == 'yes';
    final double arrivalThreshold = isRoom ? 5.0 : 15.0;

    if (showStartStairs) {
      primaryInstruction = "Take stairs down to Ground Floor (Floor 0)";
      secondaryInstruction = "Descend to start campus guidance";
      turnIcon = Icons.stairs;
      topBarColor = const Color(0xFF3B82F6); // Blue for indoor instructions
    } else if (showStairs) {
      final direction = destFloor > _userCurrentFloor ? "up" : "down";
      primaryInstruction = "Take stairs $direction to Floor $destFloor";
      secondaryInstruction = "Then proceed to ${_selectedBuilding!.name}";
      turnIcon = Icons.stairs;
      topBarColor = const Color(0xFF3B82F6); // Blue for indoor instructions
    } else if (dist < arrivalThreshold || (dist < 15.0 && _staircaseCompleted)) {
      primaryInstruction = "You have arrived";
      secondaryInstruction = _selectedBuilding!.name;
      turnIcon = Icons.place;
      topBarColor = const Color(0xFF10B981); // Emerald green for arrival
    }

    // Calculate time to reach based on speed of movement and path distance
    final double timeSeconds = pathDistance / _calculatedSpeed;
    int minutes = (timeSeconds / 60).ceil();
    if (minutes < 1) minutes = 1;

    return Stack(
      children: [
        // Top Navigation Instruction Card (Glassmorphic)
        Positioned(
          top: MediaQuery.of(context).padding.top + 16,
          left: 16,
          right: 16,
          child: ClipRRect(
            borderRadius: BorderRadius.circular(20),
            child: BackdropFilter(
              filter: ImageFilter.blur(sigmaX: 10, sigmaY: 10),
              child: Container(
                decoration: BoxDecoration(
                  color: topBarColor.withValues(alpha: 0.85),
                  borderRadius: BorderRadius.circular(20),
                  border: Border.all(color: Colors.white.withValues(alpha: 0.15)),
                  boxShadow: [
                    BoxShadow(color: Colors.black45, blurRadius: 15, offset: const Offset(0, 5)),
                  ],
                ),
                padding: const EdgeInsets.symmetric(horizontal: 20, vertical: 16),
                child: Row(
                  children: [
                    Icon(turnIcon, color: Colors.white, size: 36),
                    const SizedBox(width: 16),
                    Expanded(
                      child: Column(
                        crossAxisAlignment: CrossAxisAlignment.start,
                        mainAxisSize: MainAxisSize.min,
                        children: [
                          Text(
                            primaryInstruction,
                            style: const TextStyle(color: Colors.white, fontSize: 18, fontWeight: FontWeight.bold),
                          ),
                          const SizedBox(height: 4),
                          Text(
                            secondaryInstruction,
                            style: TextStyle(color: Colors.white.withValues(alpha: 0.8), fontSize: 13),
                          ),
                          if (_activeGateClosureNotice != null && _activeGateClosureNotice!.isNotEmpty) ...[
                            const SizedBox(height: 8),
                            Container(
                              padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 5),
                              decoration: BoxDecoration(
                                color: Colors.amber.shade900.withValues(alpha: 0.9),
                                borderRadius: BorderRadius.circular(8),
                                border: Border.all(color: Colors.amberAccent.withValues(alpha: 0.6)),
                              ),
                              child: Row(
                                mainAxisSize: MainAxisSize.min,
                                children: [
                                  const Icon(Icons.warning_amber_rounded, color: Colors.amberAccent, size: 14),
                                  const SizedBox(width: 6),
                                  Flexible(
                                    child: Text(
                                      _activeGateClosureNotice!,
                                      style: const TextStyle(color: Colors.white, fontSize: 11.5, fontWeight: FontWeight.bold),
                                      maxLines: 2,
                                      overflow: TextOverflow.ellipsis,
                                    ),
                                  ),
                                ],
                              ),
                            ),
                          ],
                          if (showStartStairs) ...[
                            const SizedBox(height: 8),
                            Row(
                              children: [
                                SizedBox(
                                  width: 80,
                                  child: ClipRRect(
                                    borderRadius: BorderRadius.circular(4),
                                    child: LinearProgressIndicator(
                                      value: (startStepsWalkedInZone / startTargetSteps).clamp(0.0, 1.0),
                                      backgroundColor: Colors.white.withValues(alpha: 0.2),
                                      valueColor: const AlwaysStoppedAnimation<Color>(Colors.greenAccent),
                                      minHeight: 6,
                                    ),
                                  ),
                                ),
                                const SizedBox(width: 8),
                                Text(
                                  "Descending: $startStepsWalkedInZone / $startTargetSteps steps",
                                  style: const TextStyle(color: Colors.greenAccent, fontSize: 11, fontWeight: FontWeight.bold),
                                ),
                              ],
                            ),
                          ],
                          if (showStairs) ...[
                            const SizedBox(height: 8),
                            Row(
                              children: [
                                SizedBox(
                                  width: 80,
                                  child: ClipRRect(
                                    borderRadius: BorderRadius.circular(4),
                                    child: LinearProgressIndicator(
                                      value: (stepsWalkedInZone / targetSteps).clamp(0.0, 1.0),
                                      backgroundColor: Colors.white.withValues(alpha: 0.2),
                                      valueColor: const AlwaysStoppedAnimation<Color>(Colors.greenAccent),
                                      minHeight: 6,
                                    ),
                                  ),
                                ),
                                const SizedBox(width: 8),
                                Text(
                                  "Climbing: $stepsWalkedInZone / $targetSteps steps",
                                  style: const TextStyle(color: Colors.greenAccent, fontSize: 11, fontWeight: FontWeight.bold),
                                ),
                              ],
                            ),
                          ],
                        ],
                      ),
                    ),
                    if (showStartStairs) ...[
                      const SizedBox(width: 12),
                      ElevatedButton.icon(
                        onPressed: () {
                          HapticFeedback.lightImpact();
                          setState(() {
                            _startStaircaseCompleted = true;
                            _userCurrentFloor = 0;
                          });
                        },
                        icon: const Icon(Icons.check_circle_outline, color: Colors.white, size: 16),
                        label: const Text(
                          "Done",
                          style: TextStyle(color: Colors.white, fontSize: 12, fontWeight: FontWeight.bold),
                        ),
                        style: ElevatedButton.styleFrom(
                          backgroundColor: Colors.white.withValues(alpha: 0.2),
                          elevation: 0,
                          padding: const EdgeInsets.symmetric(horizontal: 12, vertical: 8),
                          shape: RoundedRectangleBorder(
                            borderRadius: BorderRadius.circular(12),
                            side: BorderSide(color: Colors.white.withValues(alpha: 0.15)),
                          ),
                        ),
                      ),
                    ],
                    if (showStairs) ...[
                      const SizedBox(width: 12),
                      ElevatedButton.icon(
                        onPressed: () {
                          HapticFeedback.lightImpact();
                          setState(() {
                            _staircaseCompleted = true;
                            _userCurrentFloor = destFloor;
                          });
                        },
                        icon: const Icon(Icons.check_circle_outline, color: Colors.white, size: 16),
                        label: const Text(
                          "Done",
                          style: TextStyle(color: Colors.white, fontSize: 12, fontWeight: FontWeight.bold),
                        ),
                        style: ElevatedButton.styleFrom(
                          backgroundColor: Colors.white.withValues(alpha: 0.2),
                          elevation: 0,
                          padding: const EdgeInsets.symmetric(horizontal: 12, vertical: 8),
                          shape: RoundedRectangleBorder(
                            borderRadius: BorderRadius.circular(12),
                            side: BorderSide(color: Colors.white.withValues(alpha: 0.15)),
                          ),
                        ),
                      ),
                    ],
                    // Destination Place Photo Card (Tap to Expand & Zoom)
                    if (_selectedBuilding != null) ...[
                      const SizedBox(width: 10),
                      GestureDetector(
                        onTap: () {
                          HapticFeedback.lightImpact();
                          _showZoomablePhotoModal(context, _selectedBuilding!);
                        },
                        child: Tooltip(
                          message: "Tap to view & zoom photo",
                          child: Container(
                            width: 50,
                            height: 50,
                            decoration: BoxDecoration(
                              color: Colors.black.withValues(alpha: 0.3),
                              borderRadius: BorderRadius.circular(12),
                              border: Border.all(color: Colors.white.withValues(alpha: 0.6), width: 1.5),
                              boxShadow: [
                                BoxShadow(
                                  color: Colors.black.withValues(alpha: 0.3),
                                  blurRadius: 6,
                                  offset: const Offset(0, 2),
                                ),
                              ],
                            ),
                            child: Stack(
                              alignment: Alignment.center,
                              children: [
                                ClipRRect(
                                  borderRadius: BorderRadius.circular(10),
                                  child: _buildPlaceThumbnailImage(_selectedBuilding!, size: 50),
                                ),
                                Positioned(
                                  bottom: 2,
                                  right: 2,
                                  child: Container(
                                    padding: const EdgeInsets.all(2),
                                    decoration: const BoxDecoration(
                                      color: Color(0xFF2563EB),
                                      shape: BoxShape.circle,
                                      boxShadow: [
                                        BoxShadow(color: Colors.black38, blurRadius: 2),
                                      ],
                                    ),
                                    child: const Icon(
                                      Icons.zoom_in,
                                      color: Colors.white,
                                      size: 12,
                                    ),
                                  ),
                                ),
                              ],
                            ),
                          ),
                        ),
                      ),
                    ],
                  ],
                ),
              ),
            ),
          ),
        ),
        
        // Bottom Navigation Status Bar
        Positioned(
          bottom: 0,
          left: 0,
          right: 0,
          child: Container(
            decoration: BoxDecoration(
              color: _scaffoldBgColor,
              borderRadius: const BorderRadius.vertical(top: Radius.circular(24)),
              border: Border.all(color: _borderColor),
              boxShadow: [
                BoxShadow(color: Colors.black.withValues(alpha: 0.35), blurRadius: 20, offset: const Offset(0, -4)),
              ],
            ),
            padding: EdgeInsets.only(
              left: 16, 
              right: 16, 
              top: 14, 
              bottom: MediaQuery.of(context).padding.bottom > 0 
                  ? MediaQuery.of(context).padding.bottom + 8 
                  : 14,
            ),
            child: Row(
              crossAxisAlignment: CrossAxisAlignment.center,
              children: [
                Expanded(
                  child: Column(
                    crossAxisAlignment: CrossAxisAlignment.start,
                    mainAxisSize: MainAxisSize.min,
                    children: [
                      Row(
                        crossAxisAlignment: CrossAxisAlignment.baseline,
                        textBaseline: TextBaseline.alphabetic,
                        children: [
                          Text("$minutes min", style: const TextStyle(color: Color(0xFF10B981), fontSize: 24, fontWeight: FontWeight.bold)),
                          const SizedBox(width: 8),
                          Text(_formatDistance(pathDistance), style: TextStyle(color: _textColor.withValues(alpha: 0.8), fontSize: 15, fontWeight: FontWeight.w500)),
                        ],
                      ),
                      const SizedBox(height: 6),
                      SingleChildScrollView(
                        scrollDirection: Axis.horizontal,
                        child: Row(
                          children: [
                            _buildModeChip('walking', Icons.directions_walk, "Walk"),
                            const SizedBox(width: 6),
                            _buildModeChip('cycling', Icons.directions_bike, "Cycle"),
                            const SizedBox(width: 6),
                            _buildModeChip(
                              'auto', 
                              Icons.speed, 
                              "Auto ${(_calculatedSpeed * 3.6).toStringAsFixed(1)} km/h"
                            ),
                          ],
                        ),
                      ),
                    ],
                  ),
                ),
                const SizedBox(width: 8),
                (() {
                  final bool isNearDestination = dist < 20.0;
                  final bool isOnCorrectFloor = _userCurrentFloor == destFloor;
                  final bool isVpsButtonEnabled = isNearDestination && isOnCorrectFloor;
                  return SizedBox(
                    width: 44,
                    height: 44,
                    child: ElevatedButton(
                      onPressed: isVpsButtonEnabled
                          ? () {
                              HapticFeedback.mediumImpact();
                              Navigator.push<dynamic>(
                                context,
                                MaterialPageRoute(
                                  builder: (context) => VPSCameraScreen(
                                    startPosition: _currentPosition ?? _campusCenter,
                                    routingPath: _routingPath,
                                    destinationName: _selectedBuilding!.name,
                                    targetFloor: destFloor,
                                    vpsBoardPhotoBase64: _selectedBuilding!.vpsBoardPhotoBase64,
                                    vpsText: _selectedBuilding!.tags['vps_text']?.toString(),
                                  ),
                                ),
                              ).then((result) {
                                if (result != null && mounted) {
                                  LatLng finalPos;
                                  int? finalFloor;
                                  VPSGPSComparisonReport? report;

                                  if (result is VPSRelocalizationResult) {
                                    finalPos = result.position;
                                    finalFloor = result.floor;
                                    report = result.comparisonReport;
                                  } else if (result is VPSSensorFusionResult) {
                                    finalPos = result.position;
                                    finalFloor = result.floor;
                                  } else if (result is LatLng) {
                                    finalPos = result;
                                  } else {
                                    return;
                                  }

                                  setState(() {
                                    _currentPosition = finalPos;
                                    if (finalFloor != null) _userCurrentFloor = finalFloor;
                                    _positionNotifier.value = finalPos;
                                  });

                                  _pdrService.forceSetPosition(finalPos);

                                  if (report != null) {
                                    _pdrService.calibrateGpsBias(
                                      report.latitudeBiasCorrection,
                                      report.longitudeBiasCorrection,
                                    );
                                    ScaffoldMessenger.of(context).showSnackBar(
                                      SnackBar(
                                        content: Row(
                                          children: [
                                            const Icon(Icons.verified, color: Colors.white, size: 20),
                                            const SizedBox(width: 10),
                                            Expanded(
                                              child: Text(
                                                "🎯 VPS Calibrated: ${report.locationName}\nAccuracy: ±${report.fusedAccuracyMeters.toStringAsFixed(1)}m (GPS drift: ${report.displacementMeters.toStringAsFixed(1)}m compensated)",
                                                style: const TextStyle(fontSize: 12.5, fontWeight: FontWeight.w600),
                                              ),
                                            ),
                                          ],
                                        ),
                                        backgroundColor: const Color(0xFF10B981),
                                        duration: const Duration(seconds: 4),
                                        behavior: SnackBarBehavior.floating,
                                      ),
                                    );
                                  }
                                }
                              });
                            }
                          : () {
                              HapticFeedback.heavyImpact();
                              String message = "";
                              if (!isNearDestination) {
                                message = "Please walk closer to ${_selectedBuilding!.name} to enable VPS.";
                              } else if (!isOnCorrectFloor) {
                                message = "VPS is only active on Floor $destFloor. Please reach Floor $destFloor to enable.";
                              }
                              ScaffoldMessenger.of(context).showSnackBar(
                                SnackBar(
                                  content: Text(message),
                                  backgroundColor: Colors.orangeAccent,
                                ),
                              );
                            },
                      style: ElevatedButton.styleFrom(
                        backgroundColor: isVpsButtonEnabled
                            ? const Color(0xFF3B82F6).withValues(alpha: 0.85)
                            : Colors.grey.withValues(alpha: 0.5),
                        padding: EdgeInsets.zero,
                        shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(22)),
                      ),
                      child: Icon(
                        isVpsButtonEnabled ? Icons.view_in_ar : Icons.lock_outline,
                        color: isVpsButtonEnabled ? Colors.white : Colors.white54,
                        size: 22,
                      ),
                    ),
                  );
                })(),
                const SizedBox(width: 8),
                SizedBox(
                  width: 44,
                  height: 44,
                  child: ElevatedButton(
                    onPressed: () {
                      HapticFeedback.lightImpact();
                      setState(() {
                        _audioNavigationEnabled = !_audioNavigationEnabled;
                      });
                      ScaffoldMessenger.of(context).hideCurrentSnackBar();
                      ScaffoldMessenger.of(context).showSnackBar(
                        SnackBar(
                          content: Text(_audioNavigationEnabled ? 'Voice Guidance Enabled' : 'Voice Guidance Muted'),
                          duration: const Duration(seconds: 1),
                        ),
                      );
                    },
                    style: ElevatedButton.styleFrom(
                      backgroundColor: (_audioNavigationEnabled ? const Color(0xFF10B981) : Colors.grey).withValues(alpha: 0.85),
                      padding: EdgeInsets.zero,
                      shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(22)),
                    ),
                    child: Icon(
                      _audioNavigationEnabled ? Icons.volume_up : Icons.volume_off,
                      color: Colors.white,
                      size: 22,
                    ),
                  ),
                ),
                const SizedBox(width: 8),
                SizedBox(
                  width: 44,
                  height: 44,
                  child: ElevatedButton(
                    onPressed: _stopNavigation,
                    style: ElevatedButton.styleFrom(
                      backgroundColor: Colors.redAccent.withValues(alpha: 0.85),
                      padding: EdgeInsets.zero,
                      shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(22)),
                    ),
                    child: const Icon(Icons.close, color: Colors.white, size: 22),
                  ),
                ),
              ],
            ),
          ),
        ),
      ],
    );
  }

  // Render onboarding/instructional carousel
  Widget _buildOnboardingOverlay() {
    final slides = [
      if (kIsWeb)
        _buildOnboardingSlide(
          title: "Download Mobile App",
          desc: "For the absolute best experience on campus with native step-tracking, offline navigation, and real-time haptic feedback, download our Android App.",
          icon: Icons.install_mobile,
          iconColor: const Color(0xFF3DDC84),
          actionButton: ElevatedButton.icon(
            onPressed: _downloadApk,
            icon: const Icon(Icons.android, color: Colors.white),
            label: const Text("Download Android App", style: TextStyle(color: Colors.white, fontWeight: FontWeight.bold)),
            style: ElevatedButton.styleFrom(
              backgroundColor: const Color(0xFF3DDC84),
              shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(16)),
              padding: const EdgeInsets.symmetric(horizontal: 20, vertical: 14),
              elevation: 4,
            ),
          ),
        ),
      _buildOnboardingSlide(
        title: "Welcome to GECT Compass",
        desc: "Interactive navigation along campus walkways, department buildings, labs, workshops, and facilities at GEC Thrissur.",
        icon: Icons.explore,
        iconColor: const Color(0xFF3B82F6),
      ),
      _buildOnboardingSlide(
        title: "Dead Reckoning (PDR)",
        desc: "Using the accelerometer & compass of your phone, the app detects steps and heading to track your indoor walking paths without GPS.",
        icon: Icons.directions_walk,
        iconColor: const Color(0xFF10B981),
      ),
      _buildOnboardingSlide(
        title: "Global Updates",
        desc: "Add missing rooms, classes, or labs with photos and coordinates. Updates sync globally to a shared cloud database instantly.",
        icon: Icons.cloud_sync,
        iconColor: Colors.purpleAccent,
      ),
      _buildOnboardingSlide(
        title: "Live Events & Location Sharing",
        desc: "Share your exact location on campus via link, and publish live event locations that appear globally during their scheduled time.",
        icon: Icons.event,
        iconColor: Colors.redAccent,
      )
    ];

    return Container(
      color: Colors.black87.withValues(alpha: 0.85),
      child: Center(
        child: ClipRRect(
          borderRadius: BorderRadius.circular(28),
          child: BackdropFilter(
            filter: ImageFilter.blur(sigmaX: 15, sigmaY: 15),
            child: Container(
              width: MediaQuery.of(context).size.width * 0.88,
              height: 500,
              decoration: BoxDecoration(
                color: _cardBgColor,
                borderRadius: BorderRadius.circular(28),
                border: Border.all(color: _borderColor),
              ),
              padding: const EdgeInsets.all(28),
              child: Column(
                children: [
                  Expanded(
                    child: PageView.builder(
                      controller: _onboardingPageController,
                      itemCount: slides.length,
                      onPageChanged: (index) {
                        setState(() {
                          _onboardingPageIndex = index;
                        });
                      },
                      itemBuilder: (context, index) => slides[index],
                    ),
                  ),
                  const SizedBox(height: 16),
                  
                  // Indicator Dots
                  Row(
                    mainAxisAlignment: MainAxisAlignment.center,
                    children: List.generate(
                      slides.length,
                      (index) => Container(
                        margin: const EdgeInsets.symmetric(horizontal: 4),
                        width: _onboardingPageIndex == index ? 20 : 8,
                        height: 8,
                        decoration: BoxDecoration(
                          borderRadius: BorderRadius.circular(4),
                          color: _onboardingPageIndex == index ? const Color(0xFF3B82F6) : _textColor.withValues(alpha: 0.3),
                        ),
                      ),
                    ),
                  ),
                  const SizedBox(height: 28),
                  
                  // Bottom Button
                  SizedBox(
                    width: double.infinity,
                    height: 52,
                    child: ElevatedButton(
                      onPressed: () {
                        if (_onboardingPageIndex < slides.length - 1) {
                          _onboardingPageController.nextPage(
                            duration: const Duration(milliseconds: 300),
                            curve: Curves.easeInOut,
                          );
                        } else {
                          _dismissOnboarding();
                        }
                      },
                      style: ElevatedButton.styleFrom(
                        backgroundColor: const Color(0xFF3B82F6),
                        shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(16)),
                      ),
                      child: Text(
                        _onboardingPageIndex == slides.length - 1 ? "Get Started" : "Continue",
                        style: const TextStyle(color: Colors.white, fontSize: 16, fontWeight: FontWeight.bold),
                      ),
                    ),
                  )
                ],
              ),
            ),
          ),
        ),
      ),
    );
  }

  Widget _buildOnboardingSlide({
    required String title,
    required String desc,
    required IconData icon,
    required Color iconColor,
    Widget? actionButton,
  }) {
    return Column(
      mainAxisAlignment: MainAxisAlignment.center,
      children: [
        Icon(icon, size: 80, color: iconColor),
        const SizedBox(height: 24),
        Text(
          title,
          style: TextStyle(color: _textColor, fontSize: 24, fontWeight: FontWeight.bold),
          textAlign: TextAlign.center,
        ),
        const SizedBox(height: 12),
        Text(
          desc,
          style: TextStyle(color: _textColor.withValues(alpha: 0.7), fontSize: 14, height: 1.4),
          textAlign: TextAlign.center,
        ),
        if (actionButton != null) ...[
          const SizedBox(height: 18),
          actionButton,
        ],
      ],
    );
  }

  String _resolveBuildingCategory(Building b) {
    final explicitType = (b.tags['place_type'] ?? b.tags['type'])?.toString().trim();
    if (explicitType != null && explicitType.isNotEmpty && explicitType != 'Other') {
      if (explicitType == 'Wash room' || explicitType == 'washroom') return 'Washrooms';
      return explicitType;
    }

    final amenity = b.tags['amenity']?.toString().toLowerCase();
    final buildingType = b.tags['building']?.toString().toLowerCase();
    final tourism = b.tags['tourism']?.toString().toLowerCase();
    final barrier = b.tags['barrier']?.toString().toLowerCase();
    final leisure = b.tags['leisure']?.toString().toLowerCase();
    final isRoom = b.tags['room'] == 'yes' || b.tags['room'] == true;
    final nameLower = b.name.toLowerCase();
    final tagsStr = (b.tags['search_tags'] ?? '').toString().toLowerCase();

    // 1. Entrance Gates
    if (barrier == 'gate' || nameLower.contains(' gate') || nameLower.startsWith('gate') || nameLower.contains('entrance')) {
      return 'Entrance Gate';
    }

    // 2. Washrooms
    if (amenity == 'toilets' ||
        nameLower.contains('washroom') ||
        nameLower.contains('wash room') ||
        nameLower.contains('toilet') ||
        nameLower.contains('restroom') ||
        tagsStr.contains('washroom') ||
        tagsStr.contains('toilet')) {
      return 'Washrooms';
    }

    // 3. Cafes / Canteen / Food / ATMs
    if (['restaurant', 'cafe', 'food_court', 'canteen', 'fast_food'].contains(amenity) ||
        nameLower.contains('canteen') ||
        nameLower.contains('cafe') ||
        nameLower.contains('cafeteria') ||
        nameLower.contains('coffee') ||
        nameLower.contains('mess') ||
        nameLower.contains('bakery')) {
      return 'Cafes/ATMs';
    }
    if (['atm', 'bank'].contains(amenity) || nameLower.contains('atm') || nameLower.contains('bank') || nameLower.contains('sbi')) {
      return 'Cafes/ATMs';
    }

    // 4. Hostels / Residential
    if (tourism == 'hostel' ||
        nameLower.contains('hostel') ||
        nameLower.contains('mens hostel') ||
        nameLower.contains('ladies hostel') ||
        nameLower.contains('lh ') ||
        nameLower.contains('mh ') ||
        nameLower.startsWith('lh') ||
        nameLower.startsWith('mh') ||
        nameLower.contains('dormitory')) {
      return 'Hostels';
    }

    // 5. Workshops
    if (nameLower.contains('workshop') ||
        nameLower.contains('foundry') ||
        nameLower.contains('smithy') ||
        nameLower.contains('carpentry') ||
        nameLower.contains('welding') ||
        nameLower.contains('machine shop') ||
        nameLower.contains('fitting')) {
      return 'Workshops';
    }

    // 6. Rooms / Labs / Classrooms
    if (isRoom ||
        nameLower.contains(' lab') ||
        nameLower.contains('laboratory') ||
        nameLower.contains('classroom') ||
        nameLower.contains('drawing hall') ||
        nameLower.contains('seminar hall') ||
        nameLower.contains('ccf')) {
      return 'Rooms/Labs';
    }

    // 7. Library
    if (amenity == 'library' || nameLower.contains('library')) {
      return 'Library';
    }

    // 8. Auditorium / Hall
    if (amenity == 'events_venue' ||
        amenity == 'community_centre' ||
        nameLower.contains('auditorium') ||
        nameLower.contains('open air stage') ||
        nameLower.contains('oas')) {
      return 'Auditorium';
    }

    // 9. Sports / Ground
    if (leisure == 'pitch' ||
        leisure == 'sports_centre' ||
        nameLower.contains('ground') ||
        nameLower.contains('court') ||
        nameLower.contains('stadium') ||
        nameLower.contains('gym')) {
      return 'Sports';
    }

    // 10. Medical
    if (amenity == 'pharmacy' ||
        amenity == 'clinic' ||
        amenity == 'hospital' ||
        nameLower.contains('medical') ||
        nameLower.contains('health') ||
        nameLower.contains('dispensary')) {
      return 'Medical';
    }

    // 11. Place of worship
    if (amenity == 'place_of_worship' ||
        nameLower.contains('temple') ||
        nameLower.contains('mosque') ||
        nameLower.contains('church') ||
        nameLower.contains('prayer')) {
      return 'Worship';
    }

    // 12. Departments / Academic Blocks
    if (buildingType == 'college' ||
        nameLower.contains('dept') ||
        nameLower.contains('department') ||
        nameLower.contains('block') ||
        nameLower.contains('engineering') ||
        nameLower.contains('architecture') ||
        nameLower.contains('admin')) {
      return 'Departments';
    }

    return 'Other';
  }

  IconData _getMarkerIcon(Building b) {
    if (b.tags['is_event'] == 'true') return Icons.stars_rounded;

    final category = _resolveBuildingCategory(b);
    final nameLower = b.name.toLowerCase();
    final amenity = b.tags['amenity']?.toString().toLowerCase();

    switch (category) {
      case 'Entrance Gate':
        return Icons.sensor_door_rounded;
      case 'Departments':
        return Icons.school_rounded;
      case 'Workshops':
        return Icons.construction_rounded;
      case 'Hostels':
        return Icons.hotel_rounded;
      case 'Cafes/ATMs':
        if (['atm', 'bank'].contains(amenity) || nameLower.contains('atm') || nameLower.contains('bank') || nameLower.contains('sbi')) {
          return Icons.atm_rounded;
        }
        return Icons.restaurant_rounded;
      case 'Rooms/Labs':
        if (nameLower.contains('computer') || nameLower.contains('ccf') || nameLower.contains('it lab')) {
          return Icons.computer_rounded;
        }
        if (nameLower.contains('lab') || nameLower.contains('laboratory')) {
          return Icons.science_rounded;
        }
        return Icons.meeting_room_rounded;
      case 'Washrooms':
        return Icons.wc_rounded;
      case 'Library':
        return Icons.local_library_rounded;
      case 'Auditorium':
        return Icons.theater_comedy_rounded;
      case 'Sports':
        return Icons.sports_soccer_rounded;
      case 'Medical':
        return Icons.local_hospital_rounded;
      case 'Worship':
        return Icons.temple_hindu_rounded;
      default:
        return Icons.location_on_rounded;
    }
  }

  Color _getMarkerColor(Building b) {
    if (b.tags['is_event'] == 'true') return const Color(0xFFEF4444);

    final category = _resolveBuildingCategory(b);
    final nameLower = b.name.toLowerCase();
    final amenity = b.tags['amenity']?.toString().toLowerCase();

    switch (category) {
      case 'Entrance Gate':
        return const Color(0xFF10B981); // Emerald
      case 'Departments':
        return const Color(0xFF2563EB); // Royal Blue
      case 'Workshops':
        return const Color(0xFFD97706); // Amber / Bronze
      case 'Hostels':
        return const Color(0xFF7C3AED); // Deep Violet
      case 'Cafes/ATMs':
        if (['atm', 'bank'].contains(amenity) || nameLower.contains('atm') || nameLower.contains('bank') || nameLower.contains('sbi')) {
          return const Color(0xFFF59E0B); // Gold Amber for ATMs
        }
        return const Color(0xFFEA580C); // Warm Orange for Cafes
      case 'Rooms/Labs':
        return const Color(0xFF9333EA); // Purple
      case 'Washrooms':
        return const Color(0xFF0891B2); // Cyan Teal
      case 'Library':
        return const Color(0xFF0284C7); // Sky Blue
      case 'Auditorium':
        return const Color(0xFFDB2777); // Rose Pink
      case 'Sports':
        return const Color(0xFF059669); // Forest Green
      case 'Medical':
        return const Color(0xFFDC2626); // Crimson Red
      case 'Worship':
        return const Color(0xFFCA8A04); // Golden Yellow
      default:
        return const Color(0xFFE11D48); // Classic Red
    }
  }

  Widget _buildPlaceThumbnailImage(Building building, {double size = 50}) {
    final List<String?> candidateSources = [
      building.photoUrl,
      building.photoBase64,
      building.vpsBoardPhotoUrl,
      building.vpsBoardPhotoBase64,
      building.tags['image'] as String?,
      building.tags['photoUrl'] as String?,
    ];

    for (final raw in candidateSources) {
      if (raw == null || raw.trim().isEmpty) continue;
      final src = raw.trim();

      if (src.startsWith('http://') || src.startsWith('https://')) {
        return Image.network(
          src,
          key: ValueKey('thumb_net_${building.id}_${src.hashCode}'),
          width: size,
          height: size,
          fit: BoxFit.cover,
          gaplessPlayback: true,
          errorBuilder: (_, __, ___) => _buildFallbackPlaceIcon(building, size: size),
        );
      }

      final bytes = safeBase64Decode(src);
      if (bytes != null && bytes.isNotEmpty) {
        return Image.memory(
          bytes,
          key: ValueKey('thumb_mem_${building.id}_${bytes.hashCode}'),
          width: size,
          height: size,
          fit: BoxFit.cover,
          gaplessPlayback: true,
          errorBuilder: (_, __, ___) => _buildFallbackPlaceIcon(building, size: size),
        );
      }
    }

    return _buildFallbackPlaceIcon(building, size: size);
  }

  Widget _buildFallbackPlaceIcon(Building building, {double size = 50}) {
    return Container(
      width: size,
      height: size,
      decoration: BoxDecoration(
        gradient: LinearGradient(
          colors: [
            const Color(0xFF2563EB).withValues(alpha: 0.9),
            const Color(0xFF1D4ED8).withValues(alpha: 0.95),
          ],
          begin: Alignment.topLeft,
          end: Alignment.bottomRight,
        ),
      ),
      child: Column(
        mainAxisAlignment: MainAxisAlignment.center,
        children: [
          Icon(_getMarkerIcon(building), color: Colors.white, size: 20),
          const SizedBox(height: 2),
          Text(
            building.name.length > 5 ? '${building.name.substring(0, 4)}..' : building.name,
            style: const TextStyle(color: Colors.white, fontSize: 8, fontWeight: FontWeight.bold),
            textAlign: TextAlign.center,
            overflow: TextOverflow.ellipsis,
          ),
        ],
      ),
    );
  }

  void _showZoomablePhotoModal(BuildContext context, Building building) {
    String? networkUrl;
    Uint8List? imageBytes;

    final List<String?> candidateSources = [
      building.photoUrl,
      building.photoBase64,
      building.vpsBoardPhotoUrl,
      building.vpsBoardPhotoBase64,
      building.tags['image'] as String?,
      building.tags['photoUrl'] as String?,
    ];

    for (final raw in candidateSources) {
      if (raw == null || raw.trim().isEmpty) continue;
      final src = raw.trim();

      if (src.startsWith('http://') || src.startsWith('https://')) {
        networkUrl = src;
        break;
      }
      final decoded = safeBase64Decode(src);
      if (decoded != null && decoded.isNotEmpty) {
        imageBytes = decoded;
        break;
      }
    }

    final String subtitleText = building.tags['amenity'] ??
        building.tags['building'] ??
        building.tags['department'] ??
        'Campus Destination';

    showGeneralDialog(
      context: context,
      barrierDismissible: true,
      barrierLabel: 'Destination Photo',
      barrierColor: Colors.black.withValues(alpha: 0.88),
      transitionDuration: const Duration(milliseconds: 250),
      transitionBuilder: (context, anim1, anim2, child) {
        return FadeTransition(
          opacity: CurvedAnimation(parent: anim1, curve: Curves.easeOutCubic),
          child: ScaleTransition(
            scale: Tween<double>(begin: 0.92, end: 1.0).animate(
              CurvedAnimation(parent: anim1, curve: Curves.easeOutCubic),
            ),
            child: child,
          ),
        );
      },
      pageBuilder: (context, anim1, anim2) {
        final TransformationController transformationController = TransformationController();
        TapDownDetails? doubleTapDetails;

        return StatefulBuilder(
          builder: (context, setModalState) {
            void handleDoubleTap() {
              if (transformationController.value != Matrix4.identity()) {
                transformationController.value = Matrix4.identity();
              } else {
                final position = doubleTapDetails?.localPosition ?? Offset.zero;
                // ignore: deprecated_member_use
                transformationController.value = Matrix4.identity()
                  // ignore: deprecated_member_use
                  ..translate(-position.dx * 1.2, -position.dy * 1.2)
                  // ignore: deprecated_member_use
                  ..scale(2.5);
              }
            }

            return Scaffold(
              backgroundColor: Colors.transparent,
              body: SafeArea(
                child: Stack(
                  children: [
                    // Full Screen Interactive Zoomable Image / Content
                    Center(
                      child: GestureDetector(
                        onDoubleTapDown: (details) => doubleTapDetails = details,
                        onDoubleTap: handleDoubleTap,
                        child: InteractiveViewer(
                          transformationController: transformationController,
                          clipBehavior: Clip.none,
                          minScale: 0.8,
                          maxScale: 5.0,
                          boundaryMargin: const EdgeInsets.all(40),
                          child: imageBytes != null
                              ? Image.memory(
                                  imageBytes,
                                  fit: BoxFit.contain,
                                )
                              : (networkUrl != null && networkUrl.isNotEmpty)
                                  ? Image.network(
                                      networkUrl,
                                      fit: BoxFit.contain,
                                      errorBuilder: (_, __, ___) => _buildLargePlaceholderCard(building),
                                    )
                                  : _buildLargePlaceholderCard(building),
                        ),
                      ),
                    ),

                    // Top Header Bar
                    Positioned(
                      top: 16,
                      left: 16,
                      right: 16,
                      child: Container(
                        padding: const EdgeInsets.symmetric(horizontal: 16, vertical: 12),
                        decoration: BoxDecoration(
                          color: const Color(0xFF0F172A).withValues(alpha: 0.85),
                          borderRadius: BorderRadius.circular(20),
                          border: Border.all(color: Colors.white.withValues(alpha: 0.15)),
                          boxShadow: const [
                            BoxShadow(
                              color: Colors.black45,
                              blurRadius: 15,
                              offset: Offset(0, 4),
                            ),
                          ],
                        ),
                        child: Row(
                          children: [
                            Container(
                              padding: const EdgeInsets.all(8),
                              decoration: BoxDecoration(
                                color: const Color(0xFF2563EB).withValues(alpha: 0.25),
                                shape: BoxShape.circle,
                              ),
                              child: const Icon(Icons.pin_drop, color: Color(0xFF3B82F6), size: 20),
                            ),
                            const SizedBox(width: 12),
                            Expanded(
                              child: Column(
                                crossAxisAlignment: CrossAxisAlignment.start,
                                mainAxisSize: MainAxisSize.min,
                                children: [
                                  Text(
                                    building.name,
                                    style: const TextStyle(
                                      color: Colors.white,
                                      fontSize: 16,
                                      fontWeight: FontWeight.bold,
                                    ),
                                    overflow: TextOverflow.ellipsis,
                                  ),
                                  Text(
                                    subtitleText.toUpperCase(),
                                    style: TextStyle(
                                      color: Colors.white.withValues(alpha: 0.7),
                                      fontSize: 11,
                                      letterSpacing: 0.5,
                                    ),
                                  ),
                                ],
                              ),
                            ),
                            IconButton(
                              icon: const Icon(Icons.link_rounded, color: Color(0xFF60A5FA)),
                              onPressed: () => _showPhotoUrlPreviewModal(context, networkUrl ?? building.photoUrl),
                              tooltip: "Preview Web Link",
                            ),
                            IconButton(
                              icon: const Icon(Icons.close, color: Colors.white),
                              onPressed: () => Navigator.of(context).pop(),
                              tooltip: "Close",
                            ),
                          ],
                        ),
                      ),
                    ),

                    // Bottom Guidance & Reset Zoom Control Bar
                    Positioned(
                      bottom: 24,
                      left: 24,
                      right: 24,
                      child: Container(
                        padding: const EdgeInsets.symmetric(horizontal: 20, vertical: 12),
                        decoration: BoxDecoration(
                          color: const Color(0xFF0F172A).withValues(alpha: 0.88),
                          borderRadius: BorderRadius.circular(20),
                          border: Border.all(color: Colors.white.withValues(alpha: 0.15)),
                          boxShadow: const [
                            BoxShadow(
                              color: Colors.black45,
                              blurRadius: 12,
                              offset: Offset(0, 4),
                            ),
                          ],
                        ),
                        child: Row(
                          mainAxisAlignment: MainAxisAlignment.spaceBetween,
                          children: [
                            const Row(
                              children: [
                                Icon(Icons.pinch_outlined, color: Colors.greenAccent, size: 20),
                                SizedBox(width: 10),
                                Text(
                                  "Pinch or double-tap to zoom",
                                  style: TextStyle(
                                    color: Colors.white,
                                    fontSize: 13,
                                    fontWeight: FontWeight.w500,
                                  ),
                                ),
                              ],
                            ),
                            TextButton.icon(
                              onPressed: () {
                                transformationController.value = Matrix4.identity();
                              },
                              icon: const Icon(Icons.restart_alt, color: Colors.white70, size: 16),
                              label: const Text(
                                "Reset Zoom",
                                style: TextStyle(color: Colors.white70, fontSize: 12),
                              ),
                            ),
                          ],
                        ),
                      ),
                    ),
                  ],
                ),
              ),
            );
          },
        );
      },
    );
  }

  void _showPhotoUrlPreviewModal(BuildContext context, [String? initialUrl]) {
    final controller = TextEditingController(text: initialUrl ?? '');
    showDialog(
      context: context,
      builder: (ctx) {
        return StatefulBuilder(
          builder: (ctx, setPreviewState) {
            final input = controller.text.trim();
            final isHttp = input.startsWith('http://') || input.startsWith('https://');
            final decodedBytes = safeBase64Decode(input);

            return AlertDialog(
              backgroundColor: _cardBgColor,
              shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(20)),
              title: Row(
                children: [
                  const Icon(Icons.preview_rounded, color: Color(0xFF2563EB)),
                  const SizedBox(width: 8),
                  Expanded(
                    child: Text(
                      'Web Photo Link Previewer',
                      style: TextStyle(color: _textColor, fontSize: 16, fontWeight: FontWeight.bold),
                    ),
                  ),
                ],
              ),
              content: SingleChildScrollView(
                child: Column(
                  mainAxisSize: MainAxisSize.min,
                  crossAxisAlignment: CrossAxisAlignment.start,
                  children: [
                    Text(
                      'Enter or paste any Cloudinary link, Gist image URL, or Web photo link:',
                      style: TextStyle(color: _textColor, fontSize: 12),
                    ),
                    const SizedBox(height: 8),
                    TextField(
                      controller: controller,
                      style: TextStyle(color: _textColor, fontSize: 13),
                      onChanged: (_) => setPreviewState(() {}),
                      decoration: InputDecoration(
                        hintText: 'https://res.cloudinary.com/...',
                        hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.5)),
                        contentPadding: const EdgeInsets.symmetric(horizontal: 12, vertical: 10),
                        enabledBorder: OutlineInputBorder(
                          borderSide: BorderSide(color: _borderColor),
                          borderRadius: BorderRadius.circular(8),
                        ),
                        focusedBorder: OutlineInputBorder(
                          borderSide: const BorderSide(color: Color(0xFF2563EB)),
                          borderRadius: BorderRadius.circular(8),
                        ),
                        suffixIcon: controller.text.isNotEmpty
                            ? IconButton(
                                icon: const Icon(Icons.clear, size: 18),
                                onPressed: () {
                                  controller.clear();
                                  setPreviewState(() {});
                                },
                              )
                            : null,
                      ),
                    ),
                    const SizedBox(height: 14),
                    Text(
                      'Live Image Preview:',
                      style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.bold),
                    ),
                    const SizedBox(height: 6),
                    Container(
                      height: 180,
                      width: double.infinity,
                      decoration: BoxDecoration(
                        color: Colors.black.withValues(alpha: 0.05),
                        borderRadius: BorderRadius.circular(12),
                        border: Border.all(color: _borderColor),
                      ),
                      child: input.isEmpty
                          ? Center(
                              child: Column(
                                mainAxisAlignment: MainAxisAlignment.center,
                                children: [
                                  Icon(Icons.image_search, color: _textColor.withValues(alpha: 0.4), size: 36),
                                  const SizedBox(height: 6),
                                  Text(
                                    'Paste a link above to preview image',
                                    style: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 11),
                                  ),
                                ],
                              ),
                            )
                          : isHttp
                              ? ClipRRect(
                                  borderRadius: BorderRadius.circular(12),
                                  child: Image.network(
                                    input,
                                    fit: BoxFit.cover,
                                    loadingBuilder: (_, child, progress) {
                                      if (progress == null) return child;
                                      return const Center(child: CircularProgressIndicator(strokeWidth: 2));
                                    },
                                    errorBuilder: (_, __, ___) => Center(
                                      child: Padding(
                                        padding: const EdgeInsets.all(12),
                                        child: Text(
                                          'Failed to load image from web link',
                                          style: TextStyle(color: Colors.redAccent, fontSize: 12),
                                          textAlign: TextAlign.center,
                                        ),
                                      ),
                                    ),
                                  ),
                                )
                              : decodedBytes != null && decodedBytes.isNotEmpty
                                  ? ClipRRect(
                                      borderRadius: BorderRadius.circular(12),
                                      child: Image.memory(decodedBytes, fit: BoxFit.cover),
                                    )
                                  : Center(
                                      child: Text(
                                        'Invalid image URL or base64 format',
                                        style: TextStyle(color: Colors.redAccent, fontSize: 12),
                                      ),
                                    ),
                    ),
                  ],
                ),
              ),
              actions: [
                if (input.isNotEmpty)
                  TextButton(
                    onPressed: () {
                      Clipboard.setData(ClipboardData(text: input));
                      ScaffoldMessenger.of(context).showSnackBar(
                        const SnackBar(content: Text('Link copied to clipboard!'), duration: Duration(seconds: 2)),
                      );
                    },
                    child: const Text('Copy Link', style: TextStyle(color: Color(0xFF2563EB))),
                  ),
                TextButton(
                  onPressed: () => Navigator.pop(ctx),
                  child: const Text('Close'),
                ),
              ],
            );
          },
        );
      },
    );
  }

  Widget _buildLargePlaceholderCard(Building building) {
    return Container(
      width: 320,
      height: 380,
      padding: const EdgeInsets.all(24),
      decoration: BoxDecoration(
        gradient: const LinearGradient(
          colors: [Color(0xFF1E293B), Color(0xFF0F172A)],
          begin: Alignment.topLeft,
          end: Alignment.bottomRight,
        ),
        borderRadius: BorderRadius.circular(24),
        border: Border.all(color: Colors.white.withValues(alpha: 0.15)),
        boxShadow: const [
          BoxShadow(color: Colors.black54, blurRadius: 20, offset: Offset(0, 8)),
        ],
      ),
      child: Column(
        mainAxisAlignment: MainAxisAlignment.center,
        children: [
          Container(
            padding: const EdgeInsets.all(20),
            decoration: BoxDecoration(
              color: const Color(0xFF2563EB).withValues(alpha: 0.15),
              shape: BoxShape.circle,
              border: Border.all(color: const Color(0xFF2563EB).withValues(alpha: 0.4)),
            ),
            child: const Icon(Icons.location_city, color: Color(0xFF3B82F6), size: 64),
          ),
          const SizedBox(height: 20),
          Text(
            building.name,
            style: const TextStyle(color: Colors.white, fontSize: 20, fontWeight: FontWeight.bold),
            textAlign: TextAlign.center,
          ),
          const SizedBox(height: 8),
          Text(
            "Coordinates: ${building.lat.toStringAsFixed(5)}, ${building.lng.toStringAsFixed(5)}",
            style: TextStyle(color: Colors.white.withValues(alpha: 0.6), fontSize: 12),
            textAlign: TextAlign.center,
          ),
          const SizedBox(height: 16),
          Container(
            padding: const EdgeInsets.symmetric(horizontal: 14, vertical: 8),
            decoration: BoxDecoration(
              color: Colors.white.withValues(alpha: 0.1),
              borderRadius: BorderRadius.circular(12),
            ),
            child: const Text(
              "Destination place overview card.",
              style: TextStyle(color: Colors.white70, fontSize: 12),
              textAlign: TextAlign.center,
            ),
          ),
        ],
      ),
    );
  }

  void _showFeedbackModal() {
    showDialog(
      context: context,
      builder: (context) => const EmbeddedFeedbackModal(
        gformEmbedUrl: 'https://docs.google.com/forms/d/e/1FAIpQLSccVou0M1k5iHBcA3U1FrsYya14GFVNX7ZRD2Q9fC2ykEJAGA/viewform?embedded=true',
      ),
    );
  }

  void _showAddPlaceModal() {
    final nameController = TextEditingController();
    final searchTagsController = TextEditingController();
    final floorController = TextEditingController();
    final roomController = TextEditingController();
    final vpsTextController = TextEditingController();
    final openTimeController = TextEditingController(text: '06:00 AM');
    final closeTimeController = TextEditingController(text: '10:00 PM');
    
    String selectedPlaceType = 'Departments';
    bool isClassroom = false;
    Building? selectedParent;
    LatLng? location;
    bool isFetchingLocation = false;
    String? photoBase64;
    Uint8List? mainPhotoBytes;
    bool isProcessingPhoto = false;
    bool enableVPS = false;
    String? vpsBoardPhotoBase64;
    Uint8List? vpsBoardPhotoBytes;
    bool isProcessingVpsPhoto = false;
    Map<String, String>? floorMapData;
    final ImagePicker picker = ImagePicker();
    bool isSaving = false;

    showModalBottomSheet(
      context: context,
      backgroundColor: Colors.transparent,
      isScrollControlled: true,
      builder: (context) => StatefulBuilder(
        builder: (context, setModalState) {
          return Padding(
            padding: EdgeInsets.only(bottom: MediaQuery.of(context).viewInsets.bottom),
            child: ClipRRect(
              borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
              child: BackdropFilter(
                filter: ImageFilter.blur(sigmaX: 12, sigmaY: 12),
                child: Container(
                  height: MediaQuery.of(context).size.height * 0.85,
                  decoration: BoxDecoration(
                    color: _cardBgColor.withValues(alpha: 0.85),
                    borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
                    border: Border.all(color: _borderColor),
                  ),
                  padding: const EdgeInsets.all(24),
              child: SingleChildScrollView(
                child: Column(
                  mainAxisSize: MainAxisSize.min,
                  crossAxisAlignment: CrossAxisAlignment.start,
                  children: [
                    Center(
                      child: Container(
                        width: 40,
                        height: 4,
                        decoration: BoxDecoration(
                          color: _textColor.withValues(alpha: 0.2),
                          borderRadius: BorderRadius.circular(2),
                        ),
                      ),
                    ),
                    const SizedBox(height: 24),
                    Text(
                      "Add a Place",
                      style: TextStyle(fontSize: 22, fontWeight: FontWeight.bold, color: _textColor),
                    ),
                    const SizedBox(height: 6),
                    Text(
                      "Contribute a missing classroom, laboratory, or office to the cloud database.",
                      style: TextStyle(color: _subTextColor, fontSize: 13),
                    ),
                    const SizedBox(height: 20),
                    
                    // Place Type / Category Selection for Sorting & Filtering
                    Text(
                      "Place Type (Used for Sorting & Filtering):",
                      style: TextStyle(color: _textColor, fontSize: 13.5, fontWeight: FontWeight.bold),
                    ),
                    const SizedBox(height: 8),
                    DropdownButtonFormField<String>(
                      initialValue: selectedPlaceType,
                      decoration: InputDecoration(
                        filled: true,
                        fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                        contentPadding: const EdgeInsets.symmetric(horizontal: 16, vertical: 12),
                        border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                      ),
                      dropdownColor: _cardBgColor,
                      items: const [
                        DropdownMenuItem(value: 'Departments', child: Text("🏛️ Department / Academic Block")),
                        DropdownMenuItem(value: 'Workshops', child: Text("🛠️ Workshop / Lab Facility")),
                        DropdownMenuItem(value: 'Hostels', child: Text("🏢 Hostel (Student / Staff)")),
                        DropdownMenuItem(value: 'Cafes/ATMs', child: Text("☕ Cafe / ATM / Canteen")),
                        DropdownMenuItem(value: 'Rooms/Labs', child: Text("🔬 Room / Classroom / Lab")),
                        DropdownMenuItem(value: 'Washrooms', child: Text("🚻 Washroom / Restroom / Toilet")),
                        DropdownMenuItem(value: 'Entrance Gate', child: Text("🚪 Entrance Gate / Campus Boundary")),
                        DropdownMenuItem(value: 'Other', child: Text("📌 Other / Campus Landmark")),
                      ],
                      onChanged: (val) {
                        if (val != null) {
                          setModalState(() {
                            selectedPlaceType = val;
                            isClassroom = (val == 'Rooms/Labs');
                          });
                        }
                      },
                    ),
                    const SizedBox(height: 20),

                    // Name Input
                    TextField(
                      controller: nameController,
                      style: TextStyle(color: _textColor),
                      decoration: InputDecoration(
                        labelText: "Place Name (e.g. Embedded Systems Lab)",
                        labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 14),
                        filled: true,
                        fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                        border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                      ),
                    ),
                    const SizedBox(height: 16),

                    // Search Tags Input for Search Optimization
                    TextField(
                      controller: searchTagsController,
                      style: TextStyle(color: _textColor),
                      decoration: InputDecoration(
                        labelText: "Search Tags / Keywords (comma separated)",
                        hintText: "e.g. ECE, Microprocessor, Lab, Electronics",
                        hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.35), fontSize: 13),
                        labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 14),
                        prefixIcon: Icon(Icons.style_outlined, color: _textColor.withValues(alpha: 0.5), size: 20),
                        filled: true,
                        fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                        border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                      ),
                    ),
                    const SizedBox(height: 16),

                    // Gate Operating Schedule & Timing
                    if (selectedPlaceType == 'Entrance Gate' || selectedPlaceType == 'Cafes/ATMs') ...[
                      Container(
                        padding: const EdgeInsets.all(16),
                        decoration: BoxDecoration(
                          color: _scaffoldBgColor.withValues(alpha: 0.5),
                          borderRadius: BorderRadius.circular(16),
                          border: Border.all(color: _borderColor),
                        ),
                        child: Column(
                          crossAxisAlignment: CrossAxisAlignment.start,
                          children: [
                            Row(
                              children: [
                                const Icon(Icons.access_time_filled_rounded, color: Color(0xFF3B82F6), size: 18),
                                const SizedBox(width: 8),
                                Text(
                                  "Gate / Place Operating Hours",
                                  style: TextStyle(color: _textColor, fontSize: 14, fontWeight: FontWeight.bold),
                                ),
                              ],
                            ),
                            const SizedBox(height: 12),
                            Row(
                              children: [
                                Expanded(
                                  child: TextField(
                                    controller: openTimeController,
                                    style: TextStyle(color: _textColor, fontSize: 13),
                                    decoration: InputDecoration(
                                      labelText: "Opening Time",
                                      hintText: "06:00 AM",
                                      prefixIcon: const Icon(Icons.wb_sunny_outlined, size: 16, color: Color(0xFFF59E0B)),
                                      filled: true,
                                      fillColor: _cardBgColor,
                                      border: OutlineInputBorder(borderRadius: BorderRadius.circular(12), borderSide: BorderSide.none),
                                    ),
                                    onChanged: (_) => setModalState(() {}),
                                  ),
                                ),
                                const SizedBox(width: 12),
                                Expanded(
                                  child: TextField(
                                    controller: closeTimeController,
                                    style: TextStyle(color: _textColor, fontSize: 13),
                                    decoration: InputDecoration(
                                      labelText: "Closing Time",
                                      hintText: "10:00 PM",
                                      prefixIcon: const Icon(Icons.nightlight_outlined, size: 16, color: Color(0xFF8B5CF6)),
                                      filled: true,
                                      fillColor: _cardBgColor,
                                      border: OutlineInputBorder(borderRadius: BorderRadius.circular(12), borderSide: BorderSide.none),
                                    ),
                                    onChanged: (_) => setModalState(() {}),
                                  ),
                                ),
                              ],
                            ),
                            const SizedBox(height: 10),
                            Wrap(
                              spacing: 8,
                              children: [
                                ActionChip(
                                  label: const Text("24/7 Open", style: TextStyle(fontSize: 11)),
                                  onPressed: () {
                                    setModalState(() {
                                      openTimeController.text = "24/7";
                                      closeTimeController.text = "24/7";
                                    });
                                  },
                                ),
                                ActionChip(
                                  label: const Text("06:00 AM - 10:30 PM", style: TextStyle(fontSize: 11)),
                                  onPressed: () {
                                    setModalState(() {
                                      openTimeController.text = "06:00 AM";
                                      closeTimeController.text = "10:30 PM";
                                    });
                                  },
                                ),
                                ActionChip(
                                  label: const Text("06:00 AM - 09:00 PM", style: TextStyle(fontSize: 11)),
                                  onPressed: () {
                                    setModalState(() {
                                      openTimeController.text = "06:00 AM";
                                      closeTimeController.text = "09:00 PM";
                                    });
                                  },
                                ),
                              ],
                            ),
                          ],
                        ),
                      ),
                      const SizedBox(height: 16),
                    ],

                    // Parent Building Search Selector (if room)
                    if (isClassroom) ...[
                      Autocomplete<Building>(
                        initialValue: TextEditingValue(text: selectedParent?.name ?? ''),
                        optionsBuilder: (TextEditingValue textEditingValue) {
                          final candidateBuildings = _buildings.where((b) =>
                            b.tags['building'] == 'college' || !b.tags.containsKey('room')
                          );
                          if (textEditingValue.text.isEmpty) {
                            return candidateBuildings;
                          }
                          return candidateBuildings.where((b) =>
                            b.name.toLowerCase().contains(textEditingValue.text.toLowerCase().trim())
                          );
                        },
                        displayStringForOption: (Building option) => option.name,
                        onSelected: (Building selection) {
                          setModalState(() {
                            selectedParent = selection;
                          });
                        },
                        fieldViewBuilder: (context, controller, focusNode, onSubmitted) {
                          return TextField(
                            controller: controller,
                            focusNode: focusNode,
                            style: TextStyle(color: _textColor),
                            decoration: InputDecoration(
                              labelText: "Located In (Building)",
                              hintText: "Type building name to search...",
                              hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.35), fontSize: 13),
                              labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 14),
                              prefixIcon: Icon(Icons.search_rounded, color: _textColor.withValues(alpha: 0.5), size: 20),
                              suffixIcon: selectedParent != null
                                  ? IconButton(
                                      icon: const Icon(Icons.clear, size: 18),
                                      onPressed: () {
                                        setModalState(() {
                                          selectedParent = null;
                                          controller.clear();
                                        });
                                      },
                                    )
                                  : const Icon(Icons.arrow_drop_down),
                              filled: true,
                              fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                              border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                            ),
                          );
                        },
                      ),
                      const SizedBox(height: 16),
                    ],

                    // Floor & Room number inputs
                    Row(
                      children: [
                        Expanded(
                          child: TextField(
                            controller: floorController,
                            keyboardType: TextInputType.number,
                            style: TextStyle(color: _textColor),
                            decoration: InputDecoration(
                              labelText: "Floor (e.g., 0, 1, 2)",
                              labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 13),
                              filled: true,
                              fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                              border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                            ),
                          ),
                        ),
                        const SizedBox(width: 16),
                        Expanded(
                          child: TextField(
                            controller: roomController,
                            style: TextStyle(color: _textColor),
                            decoration: InputDecoration(
                              labelText: "Room ID / Number",
                              labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 13),
                              filled: true,
                              fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                              border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                            ),
                          ),
                        ),
                      ],
                    ),
                    const SizedBox(height: 20),

                    // Location Card
                    Container(
                      padding: const EdgeInsets.all(18),
                      decoration: BoxDecoration(
                        color: _scaffoldBgColor.withValues(alpha: 0.5),
                        borderRadius: BorderRadius.circular(18),
                        border: Border.all(color: _borderColor),
                      ),
                      child: Column(
                        crossAxisAlignment: CrossAxisAlignment.start,
                        children: [
                          Text("Geographical Coordinates", style: TextStyle(color: _textColor, fontWeight: FontWeight.bold, fontSize: 14)),
                          const SizedBox(height: 8),
                          if (location != null)
                            Row(
                              children: [
                                const Icon(Icons.check_circle, color: Color(0xFF10B981), size: 16),
                                const SizedBox(width: 8),
                                Text(
                                  "Lat: ${location!.latitude.toStringAsFixed(6)}, Lng: ${location!.longitude.toStringAsFixed(6)}",
                                  style: const TextStyle(color: Color(0xFF10B981), fontSize: 13, fontWeight: FontWeight.bold),
                                ),
                              ],
                            )
                          else
                            Text("No coordinate assigned yet", style: TextStyle(color: _textColor.withValues(alpha: 0.4), fontSize: 13)),
                          const SizedBox(height: 14),
                          SizedBox(
                            width: double.infinity,
                            child: ElevatedButton.icon(
                              onPressed: isFetchingLocation ? null : () async {
                                setModalState(() { isFetchingLocation = true; });
                                try {
                                  bool serviceEnabled = await Geolocator.isLocationServiceEnabled();
                                  if (!serviceEnabled) throw Exception("Location services disabled.");
                                  
                                  LocationPermission permission = await Geolocator.checkPermission();
                                  if (permission == LocationPermission.denied) {
                                    permission = await Geolocator.requestPermission();
                                  }
                                  if (permission == LocationPermission.denied || permission == LocationPermission.deniedForever) {
                                    throw Exception("Location permission denied.");
                                  }
                                  
                                  final pos = await Geolocator.getCurrentPosition(
                                    locationSettings: const LocationSettings(accuracy: LocationAccuracy.bestForNavigation, timeLimit: Duration(seconds: 8)),
                                  );
                                  setModalState(() { location = LatLng(pos.latitude, pos.longitude); });
                                } catch (e) {
                                  if (!context.mounted) return;
                                  ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Error: $e'), backgroundColor: Colors.redAccent));
                                } finally {
                                  setModalState(() { isFetchingLocation = false; });
                                }
                              },
                              icon: isFetchingLocation 
                                ? const GradientSpinner(size: 18, strokeWidth: 2.2) 
                                : const Icon(Icons.gps_fixed, size: 18),
                              label: Text(isFetchingLocation ? "Acquiring satellites..." : "Use Current GPS Location"),
                              style: ElevatedButton.styleFrom(
                                backgroundColor: _scaffoldBgColor,
                                shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                              ),
                            ),
                          ),
                        ],
                      ),
                    ),
                    const SizedBox(height: 16),

                    // VPS Settings Card
                    Container(
                      padding: const EdgeInsets.all(18),
                      decoration: BoxDecoration(
                        color: _scaffoldBgColor.withValues(alpha: 0.5),
                        borderRadius: BorderRadius.circular(18),
                        border: Border.all(color: _borderColor),
                      ),
                      child: Column(
                        crossAxisAlignment: CrossAxisAlignment.start,
                        children: [
                          Row(
                            mainAxisAlignment: MainAxisAlignment.spaceBetween,
                            children: [
                              Text(
                                "VPS Positioning System",
                                style: TextStyle(color: _textColor, fontWeight: FontWeight.bold, fontSize: 14),
                              ),
                              Switch(
                                value: enableVPS,
                                activeThumbColor: const Color(0xFF3B82F6),
                                onChanged: (val) {
                                  setModalState(() {
                                    enableVPS = val;
                                  });
                                },
                              ),
                            ],
                          ),
                          const SizedBox(height: 8),
                          Text(
                            "Enable camera-based indoor navigation and sign calibration for this place.",
                            style: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 12),
                          ),
                          if (enableVPS) ...[
                            const SizedBox(height: 16),
                            Text(
                              "Room Board / Signboard Text (for OCR calibration):",
                              style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.w500),
                            ),
                            const SizedBox(height: 6),
                            TextField(
                              controller: vpsTextController,
                              style: TextStyle(color: _textColor),
                              decoration: InputDecoration(
                                labelText: "Signboard text (e.g. LAB 105)",
                                labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 13),
                                filled: true,
                                fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                                border: OutlineInputBorder(borderRadius: BorderRadius.circular(12), borderSide: BorderSide.none),
                              ),
                            ),
                            const SizedBox(height: 16),
                            Text(
                              "Signboard / Room Front Photo (for Visual Alignment):",
                              style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.w500),
                            ),
                            const SizedBox(height: 8),
                            Row(
                              children: [
                                Expanded(
                                  child: OutlinedButton.icon(
                                    onPressed: isProcessingVpsPhoto
                                        ? null
                                        : () async {
                                            setModalState(() {
                                              isProcessingVpsPhoto = true;
                                            });
                                            try {
                                              final XFile? image = await picker.pickImage(
                                                source: ImageSource.camera,
                                                imageQuality: 40,
                                                maxWidth: 600,
                                                maxHeight: 600,
                                              );
                                              if (image != null) {
                                                final bytes = await image.readAsBytes();
                                                final b64 = base64Encode(bytes);
                                                setModalState(() {
                                                  vpsBoardPhotoBase64 = b64;
                                                  vpsBoardPhotoBytes = bytes;
                                                  isProcessingVpsPhoto = false;
                                                });
                                              } else {
                                                setModalState(() {
                                                  isProcessingVpsPhoto = false;
                                                });
                                              }
                                            } catch (e) {
                                              setModalState(() {
                                                isProcessingVpsPhoto = false;
                                              });
                                              if (!context.mounted) return;
                                              ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Camera error: $e'), backgroundColor: Colors.redAccent));
                                            }
                                          },
                                    icon: const Icon(Icons.camera_alt, size: 16),
                                    label: Text(vpsBoardPhotoBase64 == null && vpsBoardPhotoBytes == null ? "Camera" : "Camera (OK)", style: const TextStyle(fontSize: 12)),
                                    style: OutlinedButton.styleFrom(
                                      padding: const EdgeInsets.symmetric(vertical: 10),
                                      shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                      side: BorderSide(color: _borderColor),
                                    ),
                                  ),
                                ),
                                const SizedBox(width: 8),
                                Expanded(
                                  child: OutlinedButton.icon(
                                    onPressed: isProcessingVpsPhoto
                                        ? null
                                        : () async {
                                            setModalState(() {
                                              isProcessingVpsPhoto = true;
                                            });
                                            try {
                                              final XFile? image = await picker.pickImage(
                                                source: ImageSource.gallery,
                                                imageQuality: 40,
                                                maxWidth: 600,
                                                maxHeight: 600,
                                              );
                                              if (image != null) {
                                                final bytes = await image.readAsBytes();
                                                final b64 = base64Encode(bytes);
                                                setModalState(() {
                                                  vpsBoardPhotoBase64 = b64;
                                                  vpsBoardPhotoBytes = bytes;
                                                  isProcessingVpsPhoto = false;
                                                });
                                              } else {
                                                setModalState(() {
                                                  isProcessingVpsPhoto = false;
                                                });
                                              }
                                            } catch (e) {
                                              setModalState(() {
                                                isProcessingVpsPhoto = false;
                                              });
                                              if (!context.mounted) return;
                                              ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Gallery error: $e'), backgroundColor: Colors.redAccent));
                                            }
                                          },
                                    icon: const Icon(Icons.photo_library, size: 16),
                                    label: Text(vpsBoardPhotoBase64 == null && vpsBoardPhotoBytes == null ? "Gallery" : "Gallery (OK)", style: const TextStyle(fontSize: 12)),
                                    style: OutlinedButton.styleFrom(
                                      padding: const EdgeInsets.symmetric(vertical: 10),
                                      shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                      side: BorderSide(color: _borderColor),
                                    ),
                                  ),
                                ),
                                const SizedBox(width: 8),
                                Expanded(
                                  child: OutlinedButton.icon(
                                    onPressed: isProcessingVpsPhoto
                                        ? null
                                        : () async {
                                            final url = await showDialog<String>(
                                              context: context,
                                              builder: (ctx) {
                                                final ctrl = TextEditingController(text: vpsBoardPhotoBase64?.startsWith('http') == true ? vpsBoardPhotoBase64 : '');
                                                return AlertDialog(
                                                  backgroundColor: _cardBgColor,
                                                  title: Text('Paste VPS Photo Web Link', style: TextStyle(color: _textColor, fontWeight: FontWeight.bold, fontSize: 16)),
                                                  content: Column(
                                                    mainAxisSize: MainAxisSize.min,
                                                    crossAxisAlignment: CrossAxisAlignment.start,
                                                    children: [
                                                      Text('Enter any Cloudinary URL or Web photo link:', style: TextStyle(color: _textColor, fontSize: 12)),
                                                      const SizedBox(height: 8),
                                                      TextField(
                                                        controller: ctrl,
                                                        style: TextStyle(color: _textColor, fontSize: 13),
                                                        decoration: InputDecoration(
                                                          hintText: 'https://res.cloudinary.com/...',
                                                          hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.5)),
                                                          border: OutlineInputBorder(borderRadius: BorderRadius.circular(8)),
                                                        ),
                                                      ),
                                                    ],
                                                  ),
                                                  actions: [
                                                    TextButton(onPressed: () => Navigator.pop(ctx, null), child: const Text('Cancel')),
                                                    TextButton(onPressed: () => Navigator.pop(ctx, ctrl.text.trim()), child: const Text('Apply Link')),
                                                  ],
                                                );
                                              },
                                            );
                                            if (url != null && url.isNotEmpty) {
                                              setModalState(() {
                                                vpsBoardPhotoBase64 = url;
                                                vpsBoardPhotoBytes = safeBase64Decode(url);
                                              });
                                            }
                                          },
                                    icon: const Icon(Icons.link, size: 16),
                                    label: Text(vpsBoardPhotoBase64?.startsWith('http') == true ? "Link (OK)" : "Web Link", style: const TextStyle(fontSize: 11)),
                                    style: OutlinedButton.styleFrom(
                                      padding: const EdgeInsets.symmetric(vertical: 10, horizontal: 2),
                                      shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                      side: BorderSide(color: _borderColor),
                                    ),
                                  ),
                                ),
                              ],
                            ),
                            if (isProcessingVpsPhoto) ...[
                              const SizedBox(height: 12),
                              Container(
                                padding: const EdgeInsets.all(12),
                                decoration: BoxDecoration(
                                  color: Colors.black.withValues(alpha: 0.05),
                                  borderRadius: BorderRadius.circular(12),
                                  border: Border.all(color: _borderColor),
                                ),
                                child: Row(
                                  mainAxisAlignment: MainAxisAlignment.center,
                                  children: [
                                    const SizedBox(width: 16, height: 16, child: CircularProgressIndicator(strokeWidth: 2)),
                                    const SizedBox(width: 10),
                                    Text("Processing signboard photo...", style: TextStyle(color: _textColor, fontSize: 12)),
                                  ],
                                ),
                              ),
                            ] else if (vpsBoardPhotoBytes != null || (vpsBoardPhotoBase64 != null && vpsBoardPhotoBase64!.isNotEmpty)) ...[
                              const SizedBox(height: 12),
                              Stack(
                                children: [
                                  ClipRRect(
                                    borderRadius: BorderRadius.circular(12),
                                    child: vpsBoardPhotoBytes != null
                                        ? Image.memory(
                                            vpsBoardPhotoBytes!,
                                            height: 80,
                                            width: double.infinity,
                                            fit: BoxFit.cover,
                                          )
                                        : Image.memory(
                                            safeBase64Decode(vpsBoardPhotoBase64!) ?? Uint8List(0),
                                            height: 80,
                                            width: double.infinity,
                                            fit: BoxFit.cover,
                                          ),
                                  ),
                                  Positioned(
                                    top: 6,
                                    right: 6,
                                    child: GestureDetector(
                                      onTap: () {
                                        setModalState(() {
                                          vpsBoardPhotoBase64 = null;
                                          vpsBoardPhotoBytes = null;
                                        });
                                      },
                                      child: Container(
                                        padding: const EdgeInsets.all(4),
                                        decoration: BoxDecoration(color: Colors.black.withValues(alpha: 0.6), shape: BoxShape.circle),
                                        child: const Icon(Icons.close, color: Colors.white, size: 14),
                                      ),
                                    ),
                                  ),
                                ],
                              ),
                            ],
                            const SizedBox(height: 16),
                            Text(
                              "Floor Map Layout (Camera scan):",
                              style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.w500),
                            ),
                            const SizedBox(height: 8),
                            SizedBox(
                              width: double.infinity,
                              child: OutlinedButton.icon(
                                onPressed: () async {
                                  final name = nameController.text.trim().isNotEmpty
                                      ? nameController.text.trim()
                                      : "This Place";
                                  final result = await Navigator.push<Map<String, String>>(
                                    context,
                                    MaterialPageRoute(
                                      builder: (context) => FloorMappingScreen(placeName: name),
                                    ),
                                  );
                                  if (result != null) {
                                    if (!context.mounted) return;
                                    setModalState(() {
                                      floorMapData = result;
                                    });
                                    ScaffoldMessenger.of(context).showSnackBar(
                                      const SnackBar(
                                        content: Text("Floor layout mapped successfully!"),
                                        backgroundColor: Color(0xFF10B981),
                                      ),
                                    );
                                  }
                                },
                                icon: const Icon(Icons.photo_camera_back, size: 18),
                                label: Text(
                                  floorMapData == null
                                      ? "Scan & Map Floor Layout"
                                      : "Re-scan Floor Layout (OK)",
                                  style: const TextStyle(fontSize: 12),
                                ),
                                style: OutlinedButton.styleFrom(
                                  padding: const EdgeInsets.symmetric(vertical: 12),
                                  shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                  side: BorderSide(color: _borderColor),
                                ),
                              ),
                            ),
                            if (floorMapData != null) ...[
                              const SizedBox(height: 8),
                              Container(
                                padding: const EdgeInsets.all(10),
                                decoration: BoxDecoration(
                                  color: const Color(0xFF10B981).withValues(alpha: 0.1),
                                  borderRadius: BorderRadius.circular(10),
                                  border: Border.all(color: const Color(0xFF10B981).withValues(alpha: 0.3)),
                                ),
                                child: Row(
                                  children: [
                                    const Icon(Icons.check_circle, color: Color(0xFF10B981), size: 16),
                                    const SizedBox(width: 8),
                                    Expanded(
                                      child: Text(
                                        "Mesh signature: ${floorMapData!['signature']} (${floorMapData!['anchors']} anchors)",
                                        style: const TextStyle(color: Color(0xFF10B981), fontSize: 11, fontWeight: FontWeight.w500),
                                      ),
                                    ),
                                  ],
                                ),
                              ),
                            ],
                          ],
                        ],
                      ),
                    ),
                    const SizedBox(height: 16),
                    
                    // Add Photo Buttons (Camera / Gallery)
                    Column(
                      crossAxisAlignment: CrossAxisAlignment.start,
                      children: [
                        Text("Add Place Image / Capture:", style: TextStyle(color: _textColor.withValues(alpha: 0.8), fontSize: 13, fontWeight: FontWeight.bold)),
                        const SizedBox(height: 8),
                        Row(
                          children: [
                            Expanded(
                              child: OutlinedButton.icon(
                                onPressed: isProcessingPhoto
                                    ? null
                                    : () async {
                                        setModalState(() {
                                          isProcessingPhoto = true;
                                        });
                                        try {
                                          final XFile? image = await picker.pickImage(
                                            source: ImageSource.camera,
                                            imageQuality: 40,
                                            maxWidth: 600,
                                            maxHeight: 600,
                                          );
                                          if (image != null) {
                                            final bytes = await image.readAsBytes();
                                            final b64 = base64Encode(bytes);
                                            setModalState(() {
                                              photoBase64 = b64;
                                              mainPhotoBytes = bytes;
                                              isProcessingPhoto = false;
                                            });
                                          } else {
                                            setModalState(() {
                                              isProcessingPhoto = false;
                                            });
                                          }
                                        } catch (e) {
                                          setModalState(() {
                                            isProcessingPhoto = false;
                                          });
                                          if (!context.mounted) return;
                                          ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Camera error: $e'), backgroundColor: Colors.redAccent));
                                        }
                                      },
                                icon: const Icon(Icons.camera_alt, size: 18),
                                label: Text(photoBase64 == null && mainPhotoBytes == null ? "Camera" : "Camera (OK)", style: const TextStyle(fontSize: 12)),
                                style: OutlinedButton.styleFrom(
                                  padding: const EdgeInsets.symmetric(vertical: 12),
                                  shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                  side: BorderSide(color: _borderColor),
                                ),
                              ),
                            ),
                            const SizedBox(width: 12),
                            Expanded(
                              child: OutlinedButton.icon(
                                onPressed: isProcessingPhoto
                                    ? null
                                    : () async {
                                        setModalState(() {
                                          isProcessingPhoto = true;
                                        });
                                        try {
                                          final XFile? image = await picker.pickImage(
                                            source: ImageSource.gallery,
                                            imageQuality: 40,
                                            maxWidth: 600,
                                            maxHeight: 600,
                                          );
                                          if (image != null) {
                                            final bytes = await image.readAsBytes();
                                            final b64 = base64Encode(bytes);
                                            setModalState(() {
                                              photoBase64 = b64;
                                              mainPhotoBytes = bytes;
                                              isProcessingPhoto = false;
                                            });
                                          } else {
                                            setModalState(() {
                                              isProcessingPhoto = false;
                                            });
                                          }
                                        } catch (e) {
                                          setModalState(() {
                                            isProcessingPhoto = false;
                                          });
                                          if (!context.mounted) return;
                                          ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Gallery error: $e'), backgroundColor: Colors.redAccent));
                                        }
                                      },
                                icon: const Icon(Icons.photo_library, size: 18),
                                label: Text(photoBase64 == null && mainPhotoBytes == null ? "Gallery" : "Gallery (OK)", style: const TextStyle(fontSize: 12)),
                                style: OutlinedButton.styleFrom(
                                  padding: const EdgeInsets.symmetric(vertical: 12),
                                  shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                  side: BorderSide(color: _borderColor),
                                ),
                              ),
                            ),
                            const SizedBox(width: 8),
                            Expanded(
                              child: OutlinedButton.icon(
                                onPressed: isProcessingPhoto
                                    ? null
                                    : () async {
                                        final url = await showDialog<String>(
                                          context: context,
                                          builder: (ctx) {
                                            final ctrl = TextEditingController(text: photoBase64?.startsWith('http') == true ? photoBase64 : '');
                                            return AlertDialog(
                                              backgroundColor: _cardBgColor,
                                              title: Text('Paste Photo Web Link', style: TextStyle(color: _textColor, fontWeight: FontWeight.bold, fontSize: 16)),
                                              content: Column(
                                                mainAxisSize: MainAxisSize.min,
                                                crossAxisAlignment: CrossAxisAlignment.start,
                                                children: [
                                                  Text('Enter any Cloudinary URL, Gist link, or Web photo link:', style: TextStyle(color: _textColor, fontSize: 12)),
                                                  const SizedBox(height: 8),
                                                  TextField(
                                                    controller: ctrl,
                                                    style: TextStyle(color: _textColor, fontSize: 13),
                                                    decoration: InputDecoration(
                                                      hintText: 'https://res.cloudinary.com/...',
                                                      hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.5)),
                                                      border: OutlineInputBorder(borderRadius: BorderRadius.circular(8)),
                                                    ),
                                                  ),
                                                ],
                                              ),
                                              actions: [
                                                TextButton(onPressed: () => Navigator.pop(ctx, null), child: const Text('Cancel')),
                                                TextButton(onPressed: () => Navigator.pop(ctx, ctrl.text.trim()), child: const Text('Apply Link')),
                                              ],
                                            );
                                          },
                                        );
                                        if (url != null && url.isNotEmpty) {
                                          setModalState(() {
                                            photoBase64 = url;
                                            mainPhotoBytes = safeBase64Decode(url);
                                          });
                                        }
                                      },
                                icon: const Icon(Icons.link, size: 18),
                                label: Text(photoBase64?.startsWith('http') == true ? "Link (OK)" : "Web Link", style: const TextStyle(fontSize: 11)),
                                style: OutlinedButton.styleFrom(
                                  padding: const EdgeInsets.symmetric(vertical: 12, horizontal: 2),
                                  shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                  side: BorderSide(color: _borderColor),
                                ),
                              ),
                            ),
                          ],
                        ),
                        if (isProcessingPhoto) ...[
                          const SizedBox(height: 12),
                          Container(
                            padding: const EdgeInsets.all(16),
                            decoration: BoxDecoration(
                              color: Colors.black.withValues(alpha: 0.05),
                              borderRadius: BorderRadius.circular(12),
                              border: Border.all(color: _borderColor),
                            ),
                            child: Row(
                              mainAxisAlignment: MainAxisAlignment.center,
                              children: [
                                const SizedBox(
                                  width: 20,
                                  height: 20,
                                  child: CircularProgressIndicator(strokeWidth: 2.5, valueColor: AlwaysStoppedAnimation<Color>(Color(0xFF3B82F6))),
                                ),
                                const SizedBox(width: 12),
                                Text(
                                  "Processing & compressing photo...",
                                  style: TextStyle(color: _textColor, fontSize: 13, fontWeight: FontWeight.w500),
                                ),
                              ],
                            ),
                          ),
                        ] else if (mainPhotoBytes != null || (photoBase64 != null && photoBase64!.isNotEmpty)) ...[
                          const SizedBox(height: 12),
                          Stack(
                            children: [
                              ClipRRect(
                                borderRadius: BorderRadius.circular(12),
                                child: (() {
                                  final src = (photoBase64 ?? '').trim();
                                  if (src.startsWith('http://') || src.startsWith('https://')) {
                                    return Image.network(
                                      src,
                                      height: 120,
                                      width: double.infinity,
                                      fit: BoxFit.cover,
                                      errorBuilder: (_, __, ___) => const Center(child: Icon(Icons.broken_image, color: Colors.grey)),
                                    );
                                  }
                                  final bytes = mainPhotoBytes ?? safeBase64Decode(src);
                                  if (bytes != null && bytes.isNotEmpty) {
                                    return Image.memory(
                                      bytes,
                                      height: 120,
                                      width: double.infinity,
                                      fit: BoxFit.cover,
                                      errorBuilder: (_, __, ___) => const Center(child: Icon(Icons.broken_image, color: Colors.grey)),
                                    );
                                  }
                                  return const SizedBox.shrink();
                                })(),
                              ),
                              Positioned(
                                top: 8,
                                right: 8,
                                child: GestureDetector(
                                  onTap: () {
                                    setModalState(() {
                                      photoBase64 = null;
                                      mainPhotoBytes = null;
                                    });
                                  },
                                  child: Container(
                                    padding: const EdgeInsets.all(6),
                                    decoration: BoxDecoration(
                                      color: Colors.black.withValues(alpha: 0.6),
                                      shape: BoxShape.circle,
                                    ),
                                    child: const Icon(Icons.close, color: Colors.white, size: 16),
                                  ),
                                ),
                              ),
                            ],
                          ),
                        ]
                      ],
                    ),
                    const SizedBox(height: 28),

                    SizedBox(
                      width: double.infinity,
                      child: ElevatedButton.icon(
                        onPressed: isSaving
                            ? null
                            : () async {
                                if (nameController.text.trim().isEmpty) {
                                  ScaffoldMessenger.of(context).showSnackBar(const SnackBar(content: Text('Please enter a name.'), backgroundColor: Colors.redAccent));
                                  return;
                                }
                                if (location == null) {
                                  ScaffoldMessenger.of(context).showSnackBar(const SnackBar(content: Text('Please assign GPS location coordinates.'), backgroundColor: Colors.redAccent));
                                  return;
                                }
                                
                                setModalState(() {
                                  isSaving = true;
                                });
                                
                                final newBuilding = Building(
                                  id: 'custom_${DateTime.now().millisecondsSinceEpoch}',
                                  name: nameController.text.trim(),
                                  lat: location!.latitude,
                                  lng: location!.longitude,
                                  photoBase64: photoBase64,
                                  photoUrl: photoBase64,
                                  vpsBoardPhotoBase64: enableVPS ? vpsBoardPhotoBase64 : null,
                                  vpsBoardPhotoUrl: enableVPS ? vpsBoardPhotoBase64 : null,
                                  tags: {
                                    'custom': true,
                                    if (searchTagsController.text.trim().isNotEmpty) 'search_tags': searchTagsController.text.trim(),
                                    'place_type': selectedPlaceType,
                                    'type': selectedPlaceType,
                                    if (selectedPlaceType == 'Washrooms') 'amenity': 'toilets',
                                    if (selectedPlaceType == 'Entrance Gate') 'barrier': 'gate',
                                    if (openTimeController.text.trim().isNotEmpty) 'opening_time': openTimeController.text.trim(),
                                    if (closeTimeController.text.trim().isNotEmpty) 'closing_time': closeTimeController.text.trim(),
                                    if (openTimeController.text.trim().isNotEmpty && closeTimeController.text.trim().isNotEmpty)
                                      'opening_hours': "${openTimeController.text.trim()} - ${closeTimeController.text.trim()}", 
                                    if (isClassroom || selectedPlaceType == 'Rooms/Labs') 'room': 'yes',
                                    if ((isClassroom || selectedPlaceType == 'Rooms/Labs') && selectedParent != null) 'parent_id': selectedParent!.id,
                                    if (floorController.text.isNotEmpty) 'floor': floorController.text.trim(),
                                    if (roomController.text.isNotEmpty) 'ref': roomController.text.trim(),
                                    'vps_enabled': enableVPS ? 'yes' : 'no',
                                    if (enableVPS && vpsTextController.text.isNotEmpty) 'vps_text': vpsTextController.text.trim(),
                                    if (enableVPS && floorMapData != null) ...{
                                      'vps_mapped': 'yes',
                                      'vps_anchors_count': floorMapData!['anchors']!,
                                      'vps_mesh_signature': floorMapData!['signature']!,
                                    },
                                  },
                                );
                                
                                try {
                                  final savedBuilding = await _dataService.saveCustomBuilding(newBuilding);
                                   
                                   _mapController.move(location!, 18.5);

                                   setState(() {
                                     _buildings.add(savedBuilding);
                                     _selectedBuilding = savedBuilding;
                                     _lastBuildingCount = -1;
                                     _cachedFilteredBuildings = null;
                                   });
                                   
                                   if (context.mounted) {
                                     Navigator.pop(context);
                                     ScaffoldMessenger.of(context).showSnackBar(
                                       const SnackBar(
                                         content: Text('Place saved globally to cloud database!'),
                                         backgroundColor: Color(0xFF10B981),
                                       )
                                     );
                                   }
                                } catch (e) {
                                  if (context.mounted) {
                                    ScaffoldMessenger.of(context).showSnackBar(
                                      SnackBar(
                                        content: Text('Failed to save: $e'),
                                        backgroundColor: Colors.redAccent,
                                      )
                                    );
                                  }
                                } finally {
                                  if (mounted) {
                                    setModalState(() {
                                      isSaving = false;
                                    });
                                  }
                                }
                              },
                        icon: isSaving
                            ? const SizedBox(
                                width: 20,
                                height: 20,
                                child: CircularProgressIndicator(
                                  strokeWidth: 2,
                                  valueColor: AlwaysStoppedAnimation<Color>(Colors.white),
                                ),
                              )
                            : const Icon(Icons.check, color: Colors.white),
                        label: Text(
                          isSaving ? "Saving..." : "Save Place Globally",
                          style: const TextStyle(color: Colors.white, fontSize: 16, fontWeight: FontWeight.bold)
                        ),
                        style: ElevatedButton.styleFrom(
                          backgroundColor: const Color(0xFF3B82F6),
                          padding: const EdgeInsets.symmetric(vertical: 16),
                          shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(16)),
                        ),
                      ),
                    ),
                  ],
                ),
              ),
            ),
          ),
        ),
      );
    },
  ),
).then((_) {
      nameController.dispose();
      searchTagsController.dispose();
      floorController.dispose();
      roomController.dispose();
      vpsTextController.dispose();
    });
  }

  void _showEditPlaceModal(Building building) {
    final nameController = TextEditingController(text: building.name);
    final searchTagsController = TextEditingController(text: building.tags['search_tags']?.toString() ?? building.tags['tags']?.toString() ?? '');
    final floorController = TextEditingController(text: building.tags['floor']?.toString() ?? '');
    final roomController = TextEditingController(text: building.tags['ref']?.toString() ?? '');
    final vpsTextController = TextEditingController(text: building.tags['vps_text']?.toString() ?? '');
    final openTimeController = TextEditingController(text: building.tags['opening_time']?.toString() ?? '06:00 AM');
    final closeTimeController = TextEditingController(text: building.tags['closing_time']?.toString() ?? '10:00 PM');
    const validPlaceTypes = [
      'Departments',
      'Workshops',
      'Hostels',
      'Cafes/ATMs',
      'Rooms/Labs',
      'Washrooms',
      'Entrance Gate',
      'Other',
    ];

    String selectedPlaceType = 'Departments';
    final existingPlaceType = building.tags['place_type']?.toString() ?? building.tags['type']?.toString();
    if (existingPlaceType != null && validPlaceTypes.contains(existingPlaceType)) {
      selectedPlaceType = existingPlaceType;
    } else if (building.tags['barrier'] == 'gate' || (existingPlaceType != null && existingPlaceType.toLowerCase().contains('gate')) || building.name.toLowerCase().contains('gate')) {
      selectedPlaceType = 'Entrance Gate';
    } else if (building.tags['amenity'] == 'toilets' || (existingPlaceType != null && (existingPlaceType == 'Wash room' || existingPlaceType.toLowerCase().contains('washroom') || existingPlaceType.toLowerCase().contains('toilet'))) || building.name.toLowerCase().contains('washroom') || building.name.toLowerCase().contains('toilet')) {
      selectedPlaceType = 'Washrooms';
    } else if (building.tags['room'] == 'yes' || (existingPlaceType != null && existingPlaceType.toLowerCase().contains('room'))) {
      selectedPlaceType = 'Rooms/Labs';
    } else if (building.tags['tourism'] == 'hostel' || building.name.toLowerCase().contains('hostel') || (existingPlaceType != null && existingPlaceType.toLowerCase().contains('hostel'))) {
      selectedPlaceType = 'Hostels';
    } else if (['restaurant', 'cafe', 'food_court', 'atm', 'bank'].contains(building.tags['amenity']) || building.name.toLowerCase().contains('cafe') || building.name.toLowerCase().contains('canteen') || building.name.toLowerCase().contains('atm')) {
      selectedPlaceType = 'Cafes/ATMs';
    } else if (building.name.toLowerCase().contains('workshop')) {
      selectedPlaceType = 'Workshops';
    } else if (existingPlaceType != null && existingPlaceType.isNotEmpty) {
      selectedPlaceType = 'Other';
    }
    
    bool isClassroom = (selectedPlaceType == 'Rooms/Labs') || (building.tags['room'] == 'yes');
    Building? selectedParent;
    try {
      final parentId = building.tags['parent_id'];
      if (parentId != null) {
        selectedParent = _buildings.firstWhere((b) => b.id == parentId);
      }
    } catch (_) {}

    LatLng? location = LatLng(building.lat, building.lng);
    bool isFetchingLocation = false;
    String? photoBase64 = building.photoBase64;
    Uint8List? mainPhotoBytes;
    bool isProcessingPhoto = false;
    bool enableVPS = building.tags['vps_enabled'] == 'yes';
    String? vpsBoardPhotoBase64 = building.vpsBoardPhotoBase64;
    Uint8List? vpsBoardPhotoBytes;
    bool isProcessingVpsPhoto = false;
    Map<String, String>? floorMapData;
    if (building.tags['vps_mapped'] == 'yes') {
      floorMapData = {
        'mapped': 'yes',
        'anchors': building.tags['vps_anchors_count']?.toString() ?? '0',
        'signature': building.tags['vps_mesh_signature']?.toString() ?? '',
      };
    }
    final ImagePicker picker = ImagePicker();
    bool isSaving = false;

    showModalBottomSheet(
      context: context,
      backgroundColor: Colors.transparent,
      isScrollControlled: true,
      builder: (context) => StatefulBuilder(
        builder: (context, setModalState) {
          return Padding(
            padding: EdgeInsets.only(bottom: MediaQuery.of(context).viewInsets.bottom),
            child: ClipRRect(
              borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
              child: BackdropFilter(
                filter: ImageFilter.blur(sigmaX: 12, sigmaY: 12),
                child: Container(
                  height: MediaQuery.of(context).size.height * 0.85,
                  decoration: BoxDecoration(
                    color: _cardBgColor.withValues(alpha: 0.85),
                    borderRadius: const BorderRadius.vertical(top: Radius.circular(28)),
                    border: Border.all(color: _borderColor),
                  ),
                  padding: const EdgeInsets.all(24),
              child: SingleChildScrollView(
                child: Column(
                  mainAxisSize: MainAxisSize.min,
                  crossAxisAlignment: CrossAxisAlignment.start,
                  children: [
                    Center(
                      child: Container(
                        width: 40,
                        height: 4,
                        decoration: BoxDecoration(
                          color: _textColor.withValues(alpha: 0.2),
                          borderRadius: BorderRadius.circular(2),
                        ),
                      ),
                    ),
                    const SizedBox(height: 24),
                    Text(
                      "Edit Place Details",
                      style: TextStyle(fontSize: 22, fontWeight: FontWeight.bold, color: _textColor),
                    ),
                    const SizedBox(height: 6),
                    Text(
                      "Modify coordinates, details, or upload/change the photographic capture.",
                      style: TextStyle(color: _subTextColor, fontSize: 13),
                    ),
                    const SizedBox(height: 20),
                    
                    // Place Type / Category Selection for Sorting & Filtering
                    Text(
                      "Place Type (Used for Sorting & Filtering):",
                      style: TextStyle(color: _textColor, fontSize: 13.5, fontWeight: FontWeight.bold),
                    ),
                    const SizedBox(height: 8),
                    DropdownButtonFormField<String>(
                      initialValue: selectedPlaceType,
                      decoration: InputDecoration(
                        filled: true,
                        fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                        contentPadding: const EdgeInsets.symmetric(horizontal: 16, vertical: 12),
                        border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                      ),
                      dropdownColor: _cardBgColor,
                      items: const [
                        DropdownMenuItem(value: 'Departments', child: Text("🏛️ Department / Academic Block")),
                        DropdownMenuItem(value: 'Workshops', child: Text("🛠️ Workshop / Lab Facility")),
                        DropdownMenuItem(value: 'Hostels', child: Text("🏢 Hostel (Student / Staff)")),
                        DropdownMenuItem(value: 'Cafes/ATMs', child: Text("☕ Cafe / ATM / Canteen")),
                        DropdownMenuItem(value: 'Rooms/Labs', child: Text("🔬 Room / Classroom / Lab")),
                        DropdownMenuItem(value: 'Washrooms', child: Text("🚻 Washroom / Restroom / Toilet")),
                        DropdownMenuItem(value: 'Entrance Gate', child: Text("🚪 Entrance Gate / Campus Boundary")),
                        DropdownMenuItem(value: 'Other', child: Text("📌 Other / Campus Landmark")),
                      ],
                      onChanged: (val) {
                        if (val != null) {
                          setModalState(() {
                            selectedPlaceType = val;
                            isClassroom = (val == 'Rooms/Labs');
                          });
                        }
                      },
                    ),
                    const SizedBox(height: 20),

                    // Name Input
                    TextField(
                      controller: nameController,
                      style: TextStyle(color: _textColor),
                      decoration: InputDecoration(
                        labelText: "Place Name",
                        labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 14),
                        filled: true,
                        fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                        border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                      ),
                    ),
                    const SizedBox(height: 16),

                    // Search Tags Input for Search Optimization
                    TextField(
                      controller: searchTagsController,
                      style: TextStyle(color: _textColor),
                      decoration: InputDecoration(
                        labelText: "Search Tags / Keywords (comma separated)",
                        hintText: "e.g. ECE, Microprocessor, Lab, Electronics",
                        hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.35), fontSize: 13),
                        labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 14),
                        prefixIcon: Icon(Icons.style_outlined, color: _textColor.withValues(alpha: 0.5), size: 20),
                        filled: true,
                        fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                        border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                      ),
                    ),
                    const SizedBox(height: 16),

                    // Gate Operating Schedule & Timing
                    if (selectedPlaceType == 'Entrance Gate' || selectedPlaceType == 'Cafes/ATMs' || (building.tags['opening_time'] != null && building.tags['opening_time'].toString().isNotEmpty)) ...[
                      Container(
                        padding: const EdgeInsets.all(16),
                        decoration: BoxDecoration(
                          color: _scaffoldBgColor.withValues(alpha: 0.5),
                          borderRadius: BorderRadius.circular(16),
                          border: Border.all(color: _borderColor),
                        ),
                        child: Column(
                          crossAxisAlignment: CrossAxisAlignment.start,
                          children: [
                            Row(
                              children: [
                                const Icon(Icons.access_time_filled_rounded, color: Color(0xFF3B82F6), size: 18),
                                const SizedBox(width: 8),
                                Text(
                                  "Operating Schedule / Gate Timing",
                                  style: TextStyle(color: _textColor, fontSize: 14, fontWeight: FontWeight.bold),
                                ),
                              ],
                            ),
                            const SizedBox(height: 12),
                            Row(
                              children: [
                                Expanded(
                                  child: TextField(
                                    controller: openTimeController,
                                    style: TextStyle(color: _textColor, fontSize: 13),
                                    decoration: InputDecoration(
                                      labelText: "Opening Time",
                                      hintText: "06:00 AM",
                                      prefixIcon: const Icon(Icons.wb_sunny_outlined, size: 16, color: Color(0xFFF59E0B)),
                                      filled: true,
                                      fillColor: _cardBgColor,
                                      border: OutlineInputBorder(borderRadius: BorderRadius.circular(12), borderSide: BorderSide.none),
                                    ),
                                    onChanged: (_) => setModalState(() {}),
                                  ),
                                ),
                                const SizedBox(width: 12),
                                Expanded(
                                  child: TextField(
                                    controller: closeTimeController,
                                    style: TextStyle(color: _textColor, fontSize: 13),
                                    decoration: InputDecoration(
                                      labelText: "Closing Time",
                                      hintText: "10:00 PM",
                                      prefixIcon: const Icon(Icons.nightlight_outlined, size: 16, color: Color(0xFF8B5CF6)),
                                      filled: true,
                                      fillColor: _cardBgColor,
                                      border: OutlineInputBorder(borderRadius: BorderRadius.circular(12), borderSide: BorderSide.none),
                                    ),
                                    onChanged: (_) => setModalState(() {}),
                                  ),
                                ),
                              ],
                            ),
                            const SizedBox(height: 10),
                            Wrap(
                              spacing: 8,
                              children: [
                                ActionChip(
                                  label: const Text("24/7 Open", style: TextStyle(fontSize: 11)),
                                  onPressed: () {
                                    setModalState(() {
                                      openTimeController.text = "24/7";
                                      closeTimeController.text = "24/7";
                                    });
                                  },
                                ),
                                ActionChip(
                                  label: const Text("06:00 AM - 10:30 PM", style: TextStyle(fontSize: 11)),
                                  onPressed: () {
                                    setModalState(() {
                                      openTimeController.text = "06:00 AM";
                                      closeTimeController.text = "10:30 PM";
                                    });
                                  },
                                ),
                                ActionChip(
                                  label: const Text("06:00 AM - 09:00 PM", style: TextStyle(fontSize: 11)),
                                  onPressed: () {
                                    setModalState(() {
                                      openTimeController.text = "06:00 AM";
                                      closeTimeController.text = "09:00 PM";
                                    });
                                  },
                                ),
                              ],
                            ),
                          ],
                        ),
                      ),
                      const SizedBox(height: 16),
                    ],

                    // Parent Building Search Selector (if room)
                    if (isClassroom || selectedPlaceType == 'Rooms/Labs') ...[
                      Autocomplete<Building>(
                        initialValue: TextEditingValue(text: selectedParent?.name ?? ''),
                        optionsBuilder: (TextEditingValue textEditingValue) {
                          final candidateBuildings = _buildings.where((b) =>
                            b.id != building.id && (b.tags['building'] == 'college' || !b.tags.containsKey('room'))
                          );
                          if (textEditingValue.text.isEmpty) {
                            return candidateBuildings;
                          }
                          return candidateBuildings.where((b) =>
                            b.name.toLowerCase().contains(textEditingValue.text.toLowerCase().trim())
                          );
                        },
                        displayStringForOption: (Building option) => option.name,
                        onSelected: (Building selection) {
                          setModalState(() {
                            selectedParent = selection;
                          });
                        },
                        fieldViewBuilder: (context, controller, focusNode, onSubmitted) {
                          return TextField(
                            controller: controller,
                            focusNode: focusNode,
                            style: TextStyle(color: _textColor),
                            decoration: InputDecoration(
                              labelText: "Located In (Building)",
                              hintText: "Type building name to search...",
                              hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.35), fontSize: 13),
                              labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 14),
                              prefixIcon: Icon(Icons.search_rounded, color: _textColor.withValues(alpha: 0.5), size: 20),
                              suffixIcon: selectedParent != null
                                  ? IconButton(
                                      icon: const Icon(Icons.clear, size: 18),
                                      onPressed: () {
                                        setModalState(() {
                                          selectedParent = null;
                                          controller.clear();
                                        });
                                      },
                                    )
                                  : const Icon(Icons.arrow_drop_down),
                              filled: true,
                              fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                              border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                            ),
                          );
                        },
                      ),
                      const SizedBox(height: 16),
                    ],

                    // Floor & Room number inputs
                    Row(
                      children: [
                        Expanded(
                          child: TextField(
                            controller: floorController,
                            keyboardType: TextInputType.number,
                            style: TextStyle(color: _textColor),
                            decoration: InputDecoration(
                              labelText: "Floor",
                              labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 13),
                              filled: true,
                              fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                              border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                            ),
                          ),
                        ),
                        const SizedBox(width: 16),
                        Expanded(
                          child: TextField(
                            controller: roomController,
                            style: TextStyle(color: _textColor),
                            decoration: InputDecoration(
                              labelText: "Room ID / Number",
                              labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 13),
                              filled: true,
                              fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                              border: OutlineInputBorder(borderRadius: BorderRadius.circular(16), borderSide: BorderSide.none),
                            ),
                          ),
                        ),
                      ],
                    ),
                    const SizedBox(height: 20),

                    // Location Card
                    Container(
                      padding: const EdgeInsets.all(18),
                      decoration: BoxDecoration(
                        color: _scaffoldBgColor.withValues(alpha: 0.5),
                        borderRadius: BorderRadius.circular(18),
                        border: Border.all(color: _borderColor),
                      ),
                      child: Column(
                        crossAxisAlignment: CrossAxisAlignment.start,
                        children: [
                          Text("Geographical Coordinates", style: TextStyle(color: _textColor, fontWeight: FontWeight.bold, fontSize: 14)),
                          const SizedBox(height: 8),
                          if (location != null)
                            Row(
                              children: [
                                const Icon(Icons.check_circle, color: Color(0xFF10B981), size: 16),
                                const SizedBox(width: 8),
                                Text(
                                  "Lat: ${location!.latitude.toStringAsFixed(6)}, Lng: ${location!.longitude.toStringAsFixed(6)}",
                                  style: const TextStyle(color: Color(0xFF10B981), fontSize: 13, fontWeight: FontWeight.bold),
                                ),
                              ],
                            )
                          else
                            Text("No coordinate assigned yet", style: TextStyle(color: _textColor.withValues(alpha: 0.4), fontSize: 13)),
                          const SizedBox(height: 14),
                          SizedBox(
                            width: double.infinity,
                            child: ElevatedButton.icon(
                              onPressed: isFetchingLocation ? null : () async {
                                setModalState(() { isFetchingLocation = true; });
                                try {
                                  bool serviceEnabled = await Geolocator.isLocationServiceEnabled();
                                  if (!serviceEnabled) throw Exception("Location services disabled.");
                                  
                                  LocationPermission permission = await Geolocator.checkPermission();
                                  if (permission == LocationPermission.denied) {
                                    permission = await Geolocator.requestPermission();
                                  }
                                  if (permission == LocationPermission.denied || permission == LocationPermission.deniedForever) {
                                    throw Exception("Location permission denied.");
                                  }
                                  
                                  final pos = await Geolocator.getCurrentPosition(
                                    locationSettings: const LocationSettings(accuracy: LocationAccuracy.bestForNavigation, timeLimit: Duration(seconds: 8)),
                                  );
                                  setModalState(() { location = LatLng(pos.latitude, pos.longitude); });
                                } catch (e) {
                                  if (!context.mounted) return;
                                  ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Error: $e'), backgroundColor: Colors.redAccent));
                                } finally {
                                  setModalState(() { isFetchingLocation = false; });
                                }
                              },
                              icon: isFetchingLocation 
                                ? const GradientSpinner(size: 18, strokeWidth: 2.2) 
                                : const Icon(Icons.gps_fixed, size: 18),
                              label: Text(isFetchingLocation ? "Acquiring satellites..." : "Update to Current GPS Location"),
                              style: ElevatedButton.styleFrom(
                                backgroundColor: _scaffoldBgColor,
                                shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                              ),
                            ),
                          ),
                        ],
                      ),
                    ),
                    const SizedBox(height: 16),

                    // VPS Settings Card
                    Container(
                      padding: const EdgeInsets.all(18),
                      decoration: BoxDecoration(
                        color: _scaffoldBgColor.withValues(alpha: 0.5),
                        borderRadius: BorderRadius.circular(18),
                        border: Border.all(color: _borderColor),
                      ),
                      child: Column(
                        crossAxisAlignment: CrossAxisAlignment.start,
                        children: [
                          Row(
                            mainAxisAlignment: MainAxisAlignment.spaceBetween,
                            children: [
                              Text(
                                "VPS Positioning System",
                                style: TextStyle(color: _textColor, fontWeight: FontWeight.bold, fontSize: 14),
                              ),
                              Switch(
                                value: enableVPS,
                                activeThumbColor: const Color(0xFF3B82F6),
                                onChanged: (val) {
                                  setModalState(() {
                                    enableVPS = val;
                                  });
                                },
                              ),
                            ],
                          ),
                          const SizedBox(height: 8),
                          Text(
                            "Enable camera-based indoor navigation and sign calibration for this place.",
                            style: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 12),
                          ),
                          if (enableVPS) ...[
                            const SizedBox(height: 16),
                            Text(
                              "Room Board / Signboard Text (for OCR calibration):",
                              style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.w500),
                            ),
                            const SizedBox(height: 6),
                            TextField(
                              controller: vpsTextController,
                              style: TextStyle(color: _textColor),
                              decoration: InputDecoration(
                                labelText: "Signboard text (e.g. LAB 105)",
                                labelStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 13),
                                filled: true,
                                fillColor: _scaffoldBgColor.withValues(alpha: 0.5),
                                border: OutlineInputBorder(borderRadius: BorderRadius.circular(12), borderSide: BorderSide.none),
                              ),
                            ),
                            const SizedBox(height: 16),
                            Text(
                              "Signboard / Room Front Photo (for Visual Alignment):",
                              style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.w500),
                            ),
                            const SizedBox(height: 8),
                            Row(
                              children: [
                                Expanded(
                                  child: OutlinedButton.icon(
                                    onPressed: isProcessingVpsPhoto
                                        ? null
                                        : () async {
                                            setModalState(() {
                                              isProcessingVpsPhoto = true;
                                            });
                                            try {
                                              final XFile? image = await picker.pickImage(
                                                source: ImageSource.camera,
                                                imageQuality: 40,
                                                maxWidth: 600,
                                                maxHeight: 600,
                                              );
                                              if (image != null) {
                                                final bytes = await image.readAsBytes();
                                                final b64 = base64Encode(bytes);
                                                setModalState(() {
                                                  vpsBoardPhotoBase64 = b64;
                                                  vpsBoardPhotoBytes = bytes;
                                                  isProcessingVpsPhoto = false;
                                                });
                                              } else {
                                                setModalState(() {
                                                  isProcessingVpsPhoto = false;
                                                });
                                              }
                                            } catch (e) {
                                              setModalState(() {
                                                isProcessingVpsPhoto = false;
                                              });
                                              if (!context.mounted) return;
                                              ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Camera error: $e'), backgroundColor: Colors.redAccent));
                                            }
                                          },
                                    icon: const Icon(Icons.camera_alt, size: 16),
                                    label: Text(vpsBoardPhotoBase64 == null && vpsBoardPhotoBytes == null ? "Camera" : "Camera (OK)", style: const TextStyle(fontSize: 12)),
                                    style: OutlinedButton.styleFrom(
                                      padding: const EdgeInsets.symmetric(vertical: 10),
                                      shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                      side: BorderSide(color: _borderColor),
                                    ),
                                  ),
                                ),
                                const SizedBox(width: 8),
                                Expanded(
                                  child: OutlinedButton.icon(
                                    onPressed: isProcessingVpsPhoto
                                        ? null
                                        : () async {
                                            setModalState(() {
                                              isProcessingVpsPhoto = true;
                                            });
                                            try {
                                              final XFile? image = await picker.pickImage(
                                                source: ImageSource.gallery,
                                                imageQuality: 40,
                                                maxWidth: 600,
                                                maxHeight: 600,
                                              );
                                              if (image != null) {
                                                final bytes = await image.readAsBytes();
                                                final b64 = base64Encode(bytes);
                                                setModalState(() {
                                                  vpsBoardPhotoBase64 = b64;
                                                  vpsBoardPhotoBytes = bytes;
                                                  isProcessingVpsPhoto = false;
                                                });
                                              } else {
                                                setModalState(() {
                                                  isProcessingVpsPhoto = false;
                                                });
                                              }
                                            } catch (e) {
                                              setModalState(() {
                                                isProcessingVpsPhoto = false;
                                              });
                                              if (!context.mounted) return;
                                              ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Gallery error: $e'), backgroundColor: Colors.redAccent));
                                            }
                                          },
                                    icon: const Icon(Icons.photo_library, size: 16),
                                    label: Text(vpsBoardPhotoBase64 == null && vpsBoardPhotoBytes == null ? "Gallery" : "Gallery (OK)", style: const TextStyle(fontSize: 12)),
                                    style: OutlinedButton.styleFrom(
                                      padding: const EdgeInsets.symmetric(vertical: 10),
                                      shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                      side: BorderSide(color: _borderColor),
                                    ),
                                  ),
                                ),
                              ],
                            ),
                            if (isProcessingVpsPhoto) ...[
                              const SizedBox(height: 12),
                              Container(
                                padding: const EdgeInsets.all(12),
                                decoration: BoxDecoration(
                                  color: Colors.black.withValues(alpha: 0.05),
                                  borderRadius: BorderRadius.circular(12),
                                  border: Border.all(color: _borderColor),
                                ),
                                child: Row(
                                  mainAxisAlignment: MainAxisAlignment.center,
                                  children: [
                                    const SizedBox(width: 16, height: 16, child: CircularProgressIndicator(strokeWidth: 2)),
                                    const SizedBox(width: 10),
                                    Text("Processing signboard photo...", style: TextStyle(color: _textColor, fontSize: 12)),
                                  ],
                                ),
                              ),
                            ] else if (vpsBoardPhotoBytes != null || (vpsBoardPhotoBase64 != null && vpsBoardPhotoBase64!.isNotEmpty)) ...[
                              const SizedBox(height: 12),
                              Stack(
                                children: [
                                  ClipRRect(
                                    borderRadius: BorderRadius.circular(12),
                                    child: vpsBoardPhotoBytes != null
                                        ? Image.memory(
                                            vpsBoardPhotoBytes!,
                                            height: 80,
                                            width: double.infinity,
                                            fit: BoxFit.cover,
                                          )
                                        : Image.memory(
                                            safeBase64Decode(vpsBoardPhotoBase64!) ?? Uint8List(0),
                                            height: 80,
                                            width: double.infinity,
                                            fit: BoxFit.cover,
                                          ),
                                  ),
                                  Positioned(
                                    top: 6,
                                    right: 6,
                                    child: GestureDetector(
                                      onTap: () {
                                        setModalState(() {
                                          vpsBoardPhotoBase64 = null;
                                          vpsBoardPhotoBytes = null;
                                        });
                                      },
                                      child: Container(
                                        padding: const EdgeInsets.all(4),
                                        decoration: BoxDecoration(color: Colors.black.withValues(alpha: 0.6), shape: BoxShape.circle),
                                        child: const Icon(Icons.close, color: Colors.white, size: 14),
                                      ),
                                    ),
                                  ),
                                ],
                              ),
                            ] else if (building.vpsBoardPhotoUrl != null && building.vpsBoardPhotoUrl!.isNotEmpty) ...[
                              const SizedBox(height: 12),
                              ClipRRect(
                                borderRadius: BorderRadius.circular(12),
                                child: Image.network(
                                  building.vpsBoardPhotoUrl!,
                                  height: 80,
                                  width: double.infinity,
                                  fit: BoxFit.cover,
                                  errorBuilder: (_, __, ___) => const SizedBox.shrink(),
                                ),
                              ),
                            ],
                            const SizedBox(height: 16),
                            Text(
                              "Floor Map Layout (Camera scan):",
                              style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.w500),
                            ),
                            const SizedBox(height: 8),
                            SizedBox(
                              width: double.infinity,
                              child: OutlinedButton.icon(
                                onPressed: () async {
                                  final name = nameController.text.trim().isNotEmpty
                                      ? nameController.text.trim()
                                      : "This Place";
                                  final result = await Navigator.push<Map<String, String>>(
                                    context,
                                    MaterialPageRoute(
                                      builder: (context) => FloorMappingScreen(placeName: name),
                                    ),
                                  );
                                  if (result != null) {
                                    if (!context.mounted) return;
                                    setModalState(() {
                                      floorMapData = result;
                                    });
                                    ScaffoldMessenger.of(context).showSnackBar(
                                      const SnackBar(
                                        content: Text("Floor layout mapped successfully!"),
                                        backgroundColor: Color(0xFF10B981),
                                      ),
                                    );
                                  }
                                },
                                icon: const Icon(Icons.photo_camera_back, size: 18),
                                label: Text(
                                  floorMapData == null
                                      ? "Scan & Map Floor Layout"
                                      : "Re-scan Floor Layout (OK)",
                                  style: const TextStyle(fontSize: 12),
                                ),
                                style: OutlinedButton.styleFrom(
                                  padding: const EdgeInsets.symmetric(vertical: 12),
                                  shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                  side: BorderSide(color: _borderColor),
                                ),
                              ),
                            ),
                            if (floorMapData != null) ...[
                              const SizedBox(height: 8),
                              Container(
                                padding: const EdgeInsets.all(10),
                                decoration: BoxDecoration(
                                  color: const Color(0xFF10B981).withValues(alpha: 0.1),
                                  borderRadius: BorderRadius.circular(10),
                                  border: Border.all(color: const Color(0xFF10B981).withValues(alpha: 0.3)),
                                ),
                                child: Row(
                                  children: [
                                    const Icon(Icons.check_circle, color: Color(0xFF10B981), size: 16),
                                    const SizedBox(width: 8),
                                    Expanded(
                                      child: Text(
                                        "Mesh signature: ${floorMapData!['signature']} (${floorMapData!['anchors']} anchors)",
                                        style: const TextStyle(color: Color(0xFF10B981), fontSize: 11, fontWeight: FontWeight.w500),
                                      ),
                                    ),
                                  ],
                                ),
                              ),
                            ],
                          ],
                        ],
                      ),
                    ),
                    const SizedBox(height: 16),
                    
                    // Add Photo Buttons (Camera / Gallery)
                    Column(
                      crossAxisAlignment: CrossAxisAlignment.start,
                      children: [
                        Text("Add / Update Photo:", style: TextStyle(color: _textColor.withValues(alpha: 0.8), fontSize: 13, fontWeight: FontWeight.bold)),
                        const SizedBox(height: 8),
                        Row(
                          children: [
                            Expanded(
                              child: OutlinedButton.icon(
                                onPressed: isProcessingPhoto
                                    ? null
                                    : () async {
                                        setModalState(() {
                                          isProcessingPhoto = true;
                                        });
                                        try {
                                          final XFile? image = await picker.pickImage(
                                            source: ImageSource.camera,
                                            imageQuality: 40,
                                            maxWidth: 600,
                                            maxHeight: 600,
                                          );
                                          if (image != null) {
                                            final bytes = await image.readAsBytes();
                                            final b64 = base64Encode(bytes);
                                            setModalState(() {
                                              photoBase64 = b64;
                                              mainPhotoBytes = bytes;
                                              isProcessingPhoto = false;
                                            });
                                          } else {
                                            setModalState(() {
                                              isProcessingPhoto = false;
                                            });
                                          }
                                        } catch (e) {
                                          setModalState(() {
                                            isProcessingPhoto = false;
                                          });
                                          if (!context.mounted) return;
                                          ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Camera error: $e'), backgroundColor: Colors.redAccent));
                                        }
                                      },
                                icon: const Icon(Icons.camera_alt, size: 18),
                                label: Text(photoBase64 == null && mainPhotoBytes == null ? "Camera" : "Camera (OK)", style: const TextStyle(fontSize: 12)),
                                style: OutlinedButton.styleFrom(
                                  padding: const EdgeInsets.symmetric(vertical: 12),
                                  shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                  side: BorderSide(color: _borderColor),
                                ),
                              ),
                            ),
                            const SizedBox(width: 12),
                            Expanded(
                              child: OutlinedButton.icon(
                                onPressed: isProcessingPhoto
                                    ? null
                                    : () async {
                                        setModalState(() {
                                          isProcessingPhoto = true;
                                        });
                                        try {
                                          final XFile? image = await picker.pickImage(
                                            source: ImageSource.gallery,
                                            imageQuality: 40,
                                            maxWidth: 600,
                                            maxHeight: 600,
                                          );
                                          if (image != null) {
                                            final bytes = await image.readAsBytes();
                                            final b64 = base64Encode(bytes);
                                            setModalState(() {
                                              photoBase64 = b64;
                                              mainPhotoBytes = bytes;
                                              isProcessingPhoto = false;
                                            });
                                          } else {
                                            setModalState(() {
                                              isProcessingPhoto = false;
                                            });
                                          }
                                        } catch (e) {
                                          setModalState(() {
                                            isProcessingPhoto = false;
                                          });
                                          if (!context.mounted) return;
                                          ScaffoldMessenger.of(context).showSnackBar(SnackBar(content: Text('Gallery error: $e'), backgroundColor: Colors.redAccent));
                                        }
                                      },
                                icon: const Icon(Icons.photo_library, size: 18),
                                label: Text(photoBase64 == null && mainPhotoBytes == null ? "Gallery" : "Gallery (OK)", style: const TextStyle(fontSize: 12)),
                                style: OutlinedButton.styleFrom(
                                  padding: const EdgeInsets.symmetric(vertical: 12),
                                  shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                  side: BorderSide(color: _borderColor),
                                ),
                              ),
                            ),
                            const SizedBox(width: 8),
                            Expanded(
                              child: OutlinedButton.icon(
                                onPressed: isProcessingPhoto
                                    ? null
                                    : () async {
                                        final url = await showDialog<String>(
                                          context: context,
                                          builder: (ctx) {
                                            final ctrl = TextEditingController(text: photoBase64?.startsWith('http') == true ? photoBase64 : '');
                                            return AlertDialog(
                                              backgroundColor: _cardBgColor,
                                              title: Text('Paste Photo Web Link', style: TextStyle(color: _textColor, fontWeight: FontWeight.bold, fontSize: 16)),
                                              content: Column(
                                                mainAxisSize: MainAxisSize.min,
                                                crossAxisAlignment: CrossAxisAlignment.start,
                                                children: [
                                                  Text('Enter any Cloudinary URL, Gist link, or Web photo link:', style: TextStyle(color: _textColor, fontSize: 12)),
                                                  const SizedBox(height: 8),
                                                  TextField(
                                                    controller: ctrl,
                                                    style: TextStyle(color: _textColor, fontSize: 13),
                                                    decoration: InputDecoration(
                                                      hintText: 'https://res.cloudinary.com/...',
                                                      hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.5)),
                                                      border: OutlineInputBorder(borderRadius: BorderRadius.circular(8)),
                                                    ),
                                                  ),
                                                ],
                                              ),
                                              actions: [
                                                TextButton(onPressed: () => Navigator.pop(ctx, null), child: const Text('Cancel')),
                                                TextButton(onPressed: () => Navigator.pop(ctx, ctrl.text.trim()), child: const Text('Apply Link')),
                                              ],
                                            );
                                          },
                                        );
                                        if (url != null && url.isNotEmpty) {
                                          setModalState(() {
                                            photoBase64 = url;
                                            mainPhotoBytes = safeBase64Decode(url);
                                          });
                                        }
                                      },
                                icon: const Icon(Icons.link, size: 18),
                                label: Text(photoBase64?.startsWith('http') == true ? "Link (OK)" : "Web Link", style: const TextStyle(fontSize: 11)),
                                style: OutlinedButton.styleFrom(
                                  padding: const EdgeInsets.symmetric(vertical: 12, horizontal: 2),
                                  shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(12)),
                                  side: BorderSide(color: _borderColor),
                                ),
                              ),
                            ),
                          ],
                        ),
                        if (isProcessingPhoto) ...[
                          const SizedBox(height: 12),
                          Container(
                            padding: const EdgeInsets.all(16),
                            decoration: BoxDecoration(
                              color: Colors.black.withValues(alpha: 0.05),
                              borderRadius: BorderRadius.circular(12),
                              border: Border.all(color: _borderColor),
                            ),
                            child: Row(
                              mainAxisAlignment: MainAxisAlignment.center,
                              children: [
                                const SizedBox(
                                  width: 20,
                                  height: 20,
                                  child: CircularProgressIndicator(strokeWidth: 2.5, valueColor: AlwaysStoppedAnimation<Color>(Color(0xFF3B82F6))),
                                ),
                                const SizedBox(width: 12),
                                Text(
                                  "Processing & compressing photo...",
                                  style: TextStyle(color: _textColor, fontSize: 13, fontWeight: FontWeight.w500),
                                ),
                              ],
                            ),
                          ),
                        ] else if (mainPhotoBytes != null || (photoBase64 != null && photoBase64!.isNotEmpty)) ...[
                          const SizedBox(height: 12),
                          Stack(
                            children: [
                              ClipRRect(
                                borderRadius: BorderRadius.circular(12),
                                child: (() {
                                  final src = (photoBase64 ?? '').trim();
                                  if (src.startsWith('http://') || src.startsWith('https://')) {
                                    return Image.network(
                                      src,
                                      height: 120,
                                      width: double.infinity,
                                      fit: BoxFit.cover,
                                      errorBuilder: (_, __, ___) => const Center(child: Icon(Icons.broken_image, color: Colors.grey)),
                                    );
                                  }
                                  final bytes = mainPhotoBytes ?? safeBase64Decode(src);
                                  if (bytes != null && bytes.isNotEmpty) {
                                    return Image.memory(
                                      bytes,
                                      height: 120,
                                      width: double.infinity,
                                      fit: BoxFit.cover,
                                      errorBuilder: (_, __, ___) => const Center(child: Icon(Icons.broken_image, color: Colors.grey)),
                                    );
                                  }
                                  return const SizedBox.shrink();
                                })(),
                              ),
                              Positioned(
                                top: 8,
                                right: 8,
                                child: GestureDetector(
                                  onTap: () {
                                    setModalState(() {
                                      photoBase64 = null;
                                      mainPhotoBytes = null;
                                    });
                                  },
                                  child: Container(
                                    padding: const EdgeInsets.all(6),
                                    decoration: BoxDecoration(
                                      color: Colors.black.withValues(alpha: 0.6),
                                      shape: BoxShape.circle,
                                    ),
                                    child: const Icon(Icons.close, color: Colors.white, size: 16),
                                  ),
                                ),
                              ),
                            ],
                          ),
                        ] else if (building.photoUrl != null && building.photoUrl!.isNotEmpty) ...[
                          const SizedBox(height: 12),
                          ClipRRect(
                            borderRadius: BorderRadius.circular(12),
                            child: Image.network(
                              building.photoUrl!,
                              height: 120,
                              width: double.infinity,
                              fit: BoxFit.cover,
                              errorBuilder: (_, __, ___) => const SizedBox.shrink(),
                            ),
                          ),
                        ]
                      ],
                    ),
                    const SizedBox(height: 28),

                    // Submit Button
                    SizedBox(
                      width: double.infinity,
                      child: ElevatedButton.icon(
                        onPressed: isSaving
                            ? null
                            : () async {
                                if (nameController.text.trim().isEmpty) {
                                  ScaffoldMessenger.of(context).showSnackBar(const SnackBar(content: Text('Please enter a name.'), backgroundColor: Colors.redAccent));
                                  return;
                                }
                                if (location == null) {
                                  ScaffoldMessenger.of(context).showSnackBar(const SnackBar(content: Text('Please assign GPS location coordinates.'), backgroundColor: Colors.redAccent));
                                  return;
                                }
                                
                                setModalState(() {
                                  isSaving = true;
                                });
                                
                                 final updatedBuilding = Building(
                                  id: building.id,
                                  name: nameController.text.trim(),
                                  lat: location!.latitude,
                                  lng: location!.longitude,
                                  photoBase64: photoBase64,
                                  vpsBoardPhotoBase64: enableVPS ? vpsBoardPhotoBase64 : null,
                                  photoUrl: photoBase64 != null ? null : building.photoUrl,
                                  vpsBoardPhotoUrl: (enableVPS && vpsBoardPhotoBase64 != null) ? null : building.vpsBoardPhotoUrl,
                                  tags: {
                                    ...building.tags,
                                    'custom': true,
                                    'place_type': selectedPlaceType,
                                    'type': selectedPlaceType,
                                    if (selectedPlaceType == 'Washrooms') 'amenity': 'toilets',
                                    if (selectedPlaceType != 'Washrooms' && building.tags['amenity'] == 'toilets') 'amenity': null,
                                    if (selectedPlaceType == 'Entrance Gate') 'barrier': 'gate',
                                    if (selectedPlaceType != 'Entrance Gate' && building.tags['barrier'] == 'gate') 'barrier': null,
                                    if (selectedPlaceType == 'Rooms/Labs' || isClassroom) 'room': 'yes',
                                    if (selectedPlaceType != 'Rooms/Labs' && !isClassroom && building.tags['room'] == 'yes') 'room': null,
                                    if (selectedPlaceType == 'Hostels') 'tourism': 'hostel',
                                    'opening_time': openTimeController.text.trim().isNotEmpty ? openTimeController.text.trim() : null,
                                    'closing_time': closeTimeController.text.trim().isNotEmpty ? closeTimeController.text.trim() : null,
                                    'opening_hours': (openTimeController.text.trim().isNotEmpty && closeTimeController.text.trim().isNotEmpty) ? "${openTimeController.text.trim()} - ${closeTimeController.text.trim()}" : null,
                                    'search_tags': searchTagsController.text.trim().isNotEmpty ? searchTagsController.text.trim() : null,
                                    'parent_id': (isClassroom || selectedPlaceType == 'Rooms/Labs') && selectedParent != null ? selectedParent!.id : null,
                                    'floor': floorController.text.isNotEmpty ? floorController.text.trim() : null,
                                    'ref': roomController.text.isNotEmpty ? roomController.text.trim() : null,
                                    'vps_enabled': enableVPS ? 'yes' : 'no',
                                    'vps_text': enableVPS && vpsTextController.text.isNotEmpty ? vpsTextController.text.trim() : null,
                                    'vps_mapped': enableVPS && floorMapData != null ? 'yes' : null,
                                    'vps_anchors_count': enableVPS && floorMapData != null ? floorMapData!['anchors'] : null,
                                    'vps_mesh_signature': enableVPS && floorMapData != null ? floorMapData!['signature'] : null,
                                  }..removeWhere((k, v) => v == null),
                                );
                                
                                try {
                                  final savedBuilding = await _dataService.saveCustomBuilding(updatedBuilding);
                                  
                                  setState(() {
                                    final index = _buildings.indexWhere((b) => b.id == building.id);
                                    if (index != -1) {
                                      _buildings[index] = savedBuilding;
                                    } else {
                                      _buildings.add(savedBuilding);
                                    }
                                    _selectedBuilding = savedBuilding;
                                    _lastBuildingCount = -1;
                                    _cachedFilteredBuildings = null;
                                  });
                                  
                                  if (context.mounted) {
                                    Navigator.pop(context);
                                    ScaffoldMessenger.of(context).showSnackBar(
                                      const SnackBar(
                                        content: Text('Place updated globally in cloud database!'),
                                        backgroundColor: Color(0xFF10B981),
                                      )
                                    );
                                  }
                                } catch (e) {
                                  if (context.mounted) {
                                    ScaffoldMessenger.of(context).showSnackBar(
                                      SnackBar(
                                        content: Text('Failed to update: $e'),
                                        backgroundColor: Colors.redAccent,
                                      )
                                    );
                                  }
                                } finally {
                                  if (mounted) {
                                    setModalState(() {
                                      isSaving = false;
                                    });
                                  }
                                }
                              },
                        icon: isSaving
                            ? const SizedBox(
                                width: 20,
                                height: 20,
                                child: CircularProgressIndicator(
                                  strokeWidth: 2,
                                  valueColor: AlwaysStoppedAnimation<Color>(Colors.white),
                                ),
                              )
                            : const Icon(Icons.check, color: Colors.white),
                        label: Text(
                          isSaving ? "Saving..." : "Save Changes Globally",
                          style: const TextStyle(color: Colors.white, fontSize: 16, fontWeight: FontWeight.bold)
                        ),
                        style: ElevatedButton.styleFrom(
                          backgroundColor: const Color(0xFF10B981),
                          padding: const EdgeInsets.symmetric(vertical: 16),
                          shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(16)),
                        ),
                      ),
                    ),
                    const SizedBox(height: 12),
                    SizedBox(
                      width: double.infinity,
                      child: OutlinedButton.icon(
                        onPressed: isSaving
                            ? null
                            : () async {
                                 final String? enteredCode = await showDialog<String>(
                                   context: context,
                                   builder: (ctx) {
                                     final controller = TextEditingController(text: '');
                                     bool obscureCode = true;
                                     return StatefulBuilder(
                                       builder: (ctx, setDialogState) {
                                         return AlertDialog(
                                           backgroundColor: _cardBgColor,
                                           title: Text('Delete Place', style: TextStyle(color: _textColor, fontWeight: FontWeight.bold)),
                                           content: Column(
                                             mainAxisSize: MainAxisSize.min,
                                             crossAxisAlignment: CrossAxisAlignment.start,
                                             children: [
                                               Text('Are you sure you want to delete "${building.name}" permanently?', style: TextStyle(color: _textColor, fontSize: 14)),
                                               const SizedBox(height: 16),
                                               Text('Security verification code (Required):', style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.bold)),
                                               const SizedBox(height: 6),
                                               TextField(
                                                 controller: controller,
                                                 obscureText: obscureCode,
                                                 style: TextStyle(color: _textColor),
                                                 decoration: InputDecoration(
                                                   hintText: 'Enter Security Code',
                                                   hintStyle: TextStyle(color: _textColor.withValues(alpha: 0.5), fontSize: 13),
                                                   enabledBorder: OutlineInputBorder(
                                                     borderSide: BorderSide(color: _borderColor),
                                                     borderRadius: BorderRadius.circular(8),
                                                   ),
                                                   focusedBorder: OutlineInputBorder(
                                                     borderSide: const BorderSide(color: Colors.redAccent),
                                                     borderRadius: BorderRadius.circular(8),
                                                   ),
                                                   contentPadding: const EdgeInsets.symmetric(horizontal: 12, vertical: 10),
                                                   suffixIcon: IconButton(
                                                     icon: Icon(
                                                       obscureCode ? Icons.visibility_off : Icons.visibility,
                                                       color: _textColor.withValues(alpha: 0.6),
                                                       size: 20,
                                                     ),
                                                     onPressed: () {
                                                       setDialogState(() {
                                                         obscureCode = !obscureCode;
                                                       });
                                                     },
                                                   ),
                                                 ),
                                               ),
                                             ],
                                           ),
                                           actions: [
                                             TextButton(
                                               onPressed: () => Navigator.pop(ctx, null),
                                               child: const Text('Cancel', style: TextStyle(color: Colors.grey)),
                                             ),
                                             TextButton(
                                               onPressed: () {
                                                 final code = controller.text.trim();
                                                 if (code.isEmpty) {
                                                   ScaffoldMessenger.of(context).showSnackBar(
                                                     const SnackBar(
                                                       content: Text('Security code is required to delete a place.'),
                                                       backgroundColor: Colors.redAccent,
                                                     ),
                                                   );
                                                   return;
                                                 }
                                                 Navigator.pop(ctx, code);
                                               },
                                               child: const Text('Confirm Delete', style: TextStyle(color: Colors.redAccent, fontWeight: FontWeight.bold)),
                                             ),
                                           ],
                                         );
                                       },
                                     );
                                   },
                                 );
                                
                                if (enteredCode != null && enteredCode.isNotEmpty) {
                                  if (!context.mounted) return;

                                  setModalState(() {
                                    isSaving = true;
                                  });
                                  try {
                                    await _dataService.deleteCustomBuilding(building.id, enteredCode);
                                    
                                    setState(() {
                                      _buildings.removeWhere((b) => b.id.toString().trim() == building.id.toString().trim());
                                      _selectedBuilding = null;
                                      _lastBuildingCount = -1;
                                      _cachedFilteredBuildings = null;
                                    });
                                    
                                    if (context.mounted) {
                                      Navigator.pop(context); // close modal
                                      ScaffoldMessenger.of(context).showSnackBar(
                                        SnackBar(
                                          content: Text('"${building.name}" deleted successfully!'),
                                          backgroundColor: const Color(0xFF10B981),
                                        )
                                      );
                                    }
                                  } catch (e) {
                                    final cleanError = e.toString().replaceAll('Exception: ', '');
                                    if (context.mounted) {
                                      ScaffoldMessenger.of(context).showSnackBar(
                                        SnackBar(
                                          content: Text('Failed to delete: $cleanError'),
                                          backgroundColor: Colors.redAccent,
                                        )
                                      );
                                    }
                                  } finally {
                                    if (mounted) {
                                      setModalState(() {
                                        isSaving = false;
                                      });
                                    }
                                  }
                                }
                              },
                        icon: const Icon(Icons.delete_forever, color: Colors.redAccent),
                        label: const Text(
                          "Delete Place",
                          style: TextStyle(color: Colors.redAccent, fontSize: 16, fontWeight: FontWeight.bold),
                        ),
                        style: OutlinedButton.styleFrom(
                          padding: const EdgeInsets.symmetric(vertical: 16),
                          side: const BorderSide(color: Colors.redAccent, width: 2),
                          shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(16)),
                        ),
                      ),
                    ),
                  ],
                ),
              ),
            ),
          ),
        ),
      );
    },
  ),
).then((_) {
      nameController.dispose();
      searchTagsController.dispose();
      floorController.dispose();
      roomController.dispose();
      vpsTextController.dispose();
    });
  }

  // --- Glassmorphic Telemetry Dashboard Widgets & Helpers ---
  Widget _buildSensorDashboardWidget(BuildContext context, TelemetryData telemetry) {
    final double panelWidth = min(MediaQuery.of(context).size.width - 32, 320);

    return ClipRRect(
      borderRadius: BorderRadius.circular(24),
      child: BackdropFilter(
        filter: ImageFilter.blur(sigmaX: 16, sigmaY: 16),
        child: Container(
          width: panelWidth,
          padding: const EdgeInsets.all(16),
          decoration: BoxDecoration(
            color: _appThemeMode == 'light'
                ? Colors.white.withValues(alpha: 0.82)
                : const Color(0xFF0F172A).withValues(alpha: 0.55),
            borderRadius: BorderRadius.circular(24),
            border: Border.all(
              color: _appThemeMode == 'light'
                  ? Colors.black.withValues(alpha: 0.12)
                  : Colors.white.withValues(alpha: 0.18),
              width: 1.5,
            ),
            boxShadow: [
              BoxShadow(
                color: Colors.black.withValues(alpha: 0.3),
                blurRadius: 20,
                spreadRadius: 1,
              )
            ],
          ),
          child: Column(
            mainAxisSize: MainAxisSize.min,
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              // Header
              Row(
                mainAxisAlignment: MainAxisAlignment.spaceBetween,
                children: [
                  Row(
                    children: [
                      _buildTelemetryDot(),
                      const SizedBox(width: 8),
                      Text(
                        "TELEMETRY",
                        style: TextStyle(
                          color: _textColor,
                          fontSize: 13,
                          fontWeight: FontWeight.bold,
                          letterSpacing: 2.0,
                        ),
                      ),
                    ],
                  ),
                  GestureDetector(
                    onTap: () {
                      setState(() {
                        _showSensorDashboard = false;
                        if (!_isNavigating) {
                          _stopTelemetryListening();
                        }
                      });
                    },
                    child: Container(
                      padding: const EdgeInsets.all(4),
                      decoration: BoxDecoration(
                        color: _textColor.withValues(alpha: 0.08),
                        shape: BoxShape.circle,
                      ),
                      child: Icon(Icons.close, color: _textColor.withValues(alpha: 0.7), size: 16),
                    ),
                  ),
                ],
              ),
              const SizedBox(height: 10),

              // Status Badges
              SingleChildScrollView(
                scrollDirection: Axis.horizontal,
                child: Row(
                  children: [
                    _buildStatusBadge("ACCEL", telemetry.accelMag == 0.0 ? "STANDBY" : "LIVE", Colors.cyanAccent),
                    const SizedBox(width: 6),
                    _buildStatusBadge("COMPASS", telemetry.heading == 0.0 ? "SIM" : "LIVE", Colors.amberAccent),
                    const SizedBox(width: 6),
                    _buildStatusBadge("PDR", _isNavigating ? "ACTIVE" : "STANDBY", Colors.greenAccent),
                    const SizedBox(width: 6),
                    _buildStatusBadge("ALT", "${telemetry.altitude.toStringAsFixed(1)}m", Colors.purpleAccent),
                  ],
                ),
              ),
              const SizedBox(height: 12),

              // Rotating Compass
              Center(
                child: Column(
                  children: [
                    Stack(
                      alignment: Alignment.center,
                      children: [
                        Container(
                          width: 110,
                          height: 110,
                          decoration: BoxDecoration(
                            shape: BoxShape.circle,
                            border: Border.all(
                              color: _textColor.withValues(alpha: 0.12),
                              width: 3.5,
                            ),
                          ),
                        ),
                        // Rotating dial
                        Transform.rotate(
                          angle: -telemetry.heading * pi / 180,
                          child: CustomPaint(
                            size: const Size(100, 100),
                            painter: CompassDialPainter(textColor: _textColor),
                          ),
                        ),
                        // Fixed pointer pointing north
                        const Positioned(
                          top: 2,
                          child: Icon(
                            Icons.arrow_drop_up,
                            color: Colors.redAccent,
                            size: 24,
                          ),
                        ),
                        // Center readout bubble
                        Container(
                          width: 36,
                          height: 36,
                          decoration: BoxDecoration(
                            shape: BoxShape.circle,
                            color: _cardBgColor.withValues(alpha: 0.85),
                            border: Border.all(
                              color: Colors.white.withValues(alpha: 0.2),
                              width: 1.0,
                            ),
                          ),
                          child: Center(
                            child: Text(
                              "${telemetry.heading.toStringAsFixed(0)}°",
                              style: TextStyle(
                                color: _textColor,
                                fontSize: 10.5,
                                fontWeight: FontWeight.bold,
                              ),
                            ),
                          ),
                        ),
                      ],
                    ),
                    const SizedBox(height: 6),
                    Text(
                      _getHeadingDirectionText(telemetry.heading),
                      style: TextStyle(
                        color: _textColor.withValues(alpha: 0.85),
                        fontSize: 12,
                        fontWeight: FontWeight.w600,
                      ),
                    ),
                  ],
                ),
              ),
              const SizedBox(height: 12),

              // Accelerometer physical meters
              Text(
                "ACCELEROMETER SENSOR (m/s²)",
                style: TextStyle(
                  color: _textColor.withValues(alpha: 0.55),
                  fontSize: 9,
                  fontWeight: FontWeight.bold,
                  letterSpacing: 1.0,
                ),
              ),
              const SizedBox(height: 6),
              _buildAccelAxisIndicator("X", telemetry.accelX, Colors.redAccent),
              const SizedBox(height: 4),
              _buildAccelAxisIndicator("Y", telemetry.accelY, Colors.greenAccent),
              const SizedBox(height: 4),
              _buildAccelAxisIndicator("Z", telemetry.accelZ, Colors.blueAccent),
              
              // Sparkline graph
              const SizedBox(height: 10),
              Row(
                mainAxisAlignment: MainAxisAlignment.spaceBetween,
                children: [
                  Text(
                    "VIBRATION TELEMETRY",
                    style: TextStyle(
                      color: _textColor.withValues(alpha: 0.55),
                      fontSize: 9,
                      fontWeight: FontWeight.bold,
                      letterSpacing: 1.0,
                    ),
                  ),
                  Text(
                    "Mag: ${telemetry.accelMag.toStringAsFixed(2)}",
                    style: TextStyle(
                      color: _textColor.withValues(alpha: 0.8),
                      fontSize: 9,
                      fontFamily: 'monospace',
                    ),
                  ),
                ],
              ),
              const SizedBox(height: 6),
              Container(
                height: 32,
                padding: const EdgeInsets.symmetric(vertical: 3, horizontal: 4),
                decoration: BoxDecoration(
                  color: _textColor.withValues(alpha: 0.04),
                  borderRadius: BorderRadius.circular(8),
                  border: Border.all(color: _borderColor),
                ),
                child: Row(
                  mainAxisAlignment: MainAxisAlignment.spaceEvenly,
                  crossAxisAlignment: CrossAxisAlignment.end,
                  children: telemetry.magHistory.map((val) {
                    final heightFactor = (val / 10.0).clamp(0.08, 1.0);
                    return Container(
                      width: 8,
                      height: 24 * heightFactor,
                      decoration: BoxDecoration(
                        color: Color.lerp(Colors.cyan, Colors.redAccent, (val / 6.0).clamp(0.0, 1.0)),
                        borderRadius: BorderRadius.circular(1.5),
                      ),
                    );
                  }).toList(),
                ),
              ),

              // PDR Step engine details
              const SizedBox(height: 12),
              Text(
                "PEDESTRIAN DEAD RECKONING (PDR)",
                style: TextStyle(
                  color: _textColor.withValues(alpha: 0.55),
                  fontSize: 9,
                  fontWeight: FontWeight.bold,
                  letterSpacing: 1.0,
                ),
              ),
              const SizedBox(height: 6),
              Row(
                mainAxisAlignment: MainAxisAlignment.spaceBetween,
                children: [
                  Row(
                    children: [
                      Icon(Icons.directions_walk, color: const Color(0xFF10B981), size: 14),
                      const SizedBox(width: 4),
                      ValueListenableBuilder<int>(
                        valueListenable: _stepCountNotifier,
                        builder: (context, steps, _) => Text(
                          "$steps steps",
                          style: TextStyle(color: _textColor, fontSize: 12, fontWeight: FontWeight.bold),
                        ),
                      ),
                    ],
                  ),
                  ValueListenableBuilder<int>(
                    valueListenable: _stepCountNotifier,
                    builder: (context, steps, _) => Text(
                      "Dist: ${(steps * 0.7).toStringAsFixed(1)} m",
                      style: TextStyle(color: _subTextColor, fontSize: 11),
                    ),
                  ),
                ],
              ),

              // Compass Offset Calibration slider
              const SizedBox(height: 10),
              Row(
                mainAxisAlignment: MainAxisAlignment.spaceBetween,
                children: [
                  Text(
                    "CALIBRATE COMPASS BIAS",
                    style: TextStyle(
                      color: _textColor.withValues(alpha: 0.55),
                      fontSize: 9,
                      fontWeight: FontWeight.bold,
                      letterSpacing: 0.5,
                    ),
                  ),
                  Text(
                    "${_compassOffset >= 0 ? '+' : ''}${_compassOffset.toStringAsFixed(0)}°",
                    style: TextStyle(color: _textColor, fontSize: 9, fontWeight: FontWeight.bold),
                  ),
                ],
              ),
              SliderTheme(
                data: SliderTheme.of(context).copyWith(
                  trackHeight: 1.5,
                  thumbShape: const RoundSliderThumbShape(enabledThumbRadius: 5),
                  overlayShape: const RoundSliderOverlayShape(overlayRadius: 10),
                ),
                child: Slider(
                  value: _compassOffset,
                  min: -180.0,
                  max: 180.0,
                  onChanged: (val) {
                    setState(() {
                      _compassOffset = val;
                      _telemetryHeading = (_pdrService.rawHeading + _compassOffset + 360) % 360;
                    });
                    _telemetryNotifier.value = TelemetryData(
                      heading: _telemetryHeading,
                      accelX: telemetry.accelX,
                      accelY: telemetry.accelY,
                      accelZ: telemetry.accelZ,
                      accelMag: telemetry.accelMag,
                      magHistory: telemetry.magHistory,
                      altitude: _currentAltitude,
                    );
                  },
                ),
              ),
            ],
          ),
        ),
      ),
    );
  }

  Widget _buildTelemetryDot() {
    return AnimatedBuilder(
      animation: _pulseController,
      builder: (context, child) {
        return Container(
          width: 7,
          height: 7,
          decoration: BoxDecoration(
            shape: BoxShape.circle,
            color: Colors.greenAccent,
            boxShadow: [
              BoxShadow(
                color: Colors.greenAccent.withValues(alpha: 0.6 * (1.0 - _pulseController.value)),
                blurRadius: 3 + _pulseController.value * 5,
                spreadRadius: _pulseController.value * 2.5,
              )
            ],
          ),
        );
      },
    );
  }

  Widget _buildStatusBadge(String name, String status, Color activeColor) {
    final isLive = status == "LIVE" || status == "ACTIVE";
    return Container(
      padding: const EdgeInsets.symmetric(horizontal: 6, vertical: 2),
      decoration: BoxDecoration(
        color: (isLive ? activeColor : Colors.blueAccent).withValues(alpha: 0.12),
        borderRadius: BorderRadius.circular(8),
        border: Border.all(
          color: (isLive ? activeColor : Colors.blueAccent).withValues(alpha: 0.25),
          width: 0.8,
        ),
      ),
      child: Text(
        "$name: $status",
        style: TextStyle(
          color: isLive ? activeColor : Colors.blueAccent,
          fontSize: 8.5,
          fontWeight: FontWeight.bold,
        ),
      ),
    );
  }

  Widget _buildAccelAxisIndicator(String axis, double val, Color color) {
    final double clamped = val.clamp(-8.0, 8.0);
    final double percentage = (clamped + 8.0) / 16.0;

    return Row(
      children: [
        SizedBox(
          width: 10,
          child: Text(
            axis,
            style: TextStyle(
              color: _textColor.withValues(alpha: 0.6),
              fontSize: 10,
              fontWeight: FontWeight.bold,
            ),
          ),
        ),
        const SizedBox(width: 6),
        Expanded(
          child: ClipRRect(
            borderRadius: BorderRadius.circular(3),
            child: Container(
              height: 6,
              color: _textColor.withValues(alpha: 0.08),
              child: FractionallySizedBox(
                alignment: Alignment.centerLeft,
                widthFactor: percentage,
                child: Container(
                  decoration: BoxDecoration(
                    color: color,
                    borderRadius: BorderRadius.circular(3),
                  ),
                ),
              ),
            ),
          ),
        ),
        const SizedBox(width: 6),
        SizedBox(
          width: 38,
          child: Text(
            "${val >= 0 ? '+' : ''}${val.toStringAsFixed(2)}",
            textAlign: TextAlign.right,
            style: TextStyle(
              color: _textColor,
              fontFamily: 'monospace',
              fontSize: 9,
            ),
          ),
        ),
      ],
    );
  }

  String _getHeadingDirectionText(double heading) {
    final deg = (heading + 360) % 360;
    if (deg >= 337.5 || deg < 22.5) return "North (N)";
    if (deg >= 22.5 && deg < 67.5) return "North-East (NE)";
    if (deg >= 67.5 && deg < 112.5) return "East (E)";
    if (deg >= 112.5 && deg < 157.5) return "South-East (SE)";
    if (deg >= 157.5 && deg < 202.5) return "South (S)";
    if (deg >= 202.5 && deg < 247.5) return "South-West (SW)";
    if (deg >= 247.5 && deg < 292.5) return "West (W)";
    return "North-West (NW)";
  }
}

class CompassDialPainter extends CustomPainter {
  final Color textColor;
  CompassDialPainter({required this.textColor});

  @override
  void paint(Canvas canvas, Size size) {
    final paint = Paint()
      ..color = textColor.withValues(alpha: 0.2)
      ..style = PaintingStyle.stroke
      ..strokeWidth = 1.0;

    final center = Offset(size.width / 2, size.height / 2);
    final radius = size.width / 2;

    canvas.drawCircle(center, radius, paint);

    final textPainter = TextPainter(
      textDirection: TextDirection.ltr,
    );

    for (int i = 0; i < 360; i += 15) {
      final angle = i * pi / 180;
      final isCardinal = i % 90 == 0;
      final tickLength = isCardinal ? 8.0 : 4.0;

      final start = Offset(
        center.dx + (radius - tickLength) * sin(angle),
        center.dy - (radius - tickLength) * cos(angle),
      );
      final end = Offset(
        center.dx + radius * sin(angle),
        center.dy - radius * cos(angle),
      );

      canvas.drawLine(start, end, paint);

      if (isCardinal) {
        String label = "";
        switch (i) {
          case 0:
            label = "N";
            break;
          case 90:
            label = "E";
            break;
          case 180:
            label = "S";
            break;
          case 270:
            label = "W";
            break;
        }

        textPainter.text = TextSpan(
          text: label,
          style: TextStyle(
            color: label == "N" ? Colors.redAccent : textColor.withValues(alpha: 0.7),
            fontSize: 9,
            fontWeight: FontWeight.bold,
          ),
        );
        textPainter.layout();
        textPainter.paint(
          canvas,
          Offset(
            center.dx + (radius - 16) * sin(angle) - textPainter.width / 2,
            center.dy - (radius - 16) * cos(angle) - textPainter.height / 2,
          ),
        );
      }
    }
  }

  @override
  bool shouldRepaint(covariant CompassDialPainter oldDelegate) =>
      oldDelegate.textColor != textColor;
}

class DirectionBeamPainter extends CustomPainter {
  @override
  void paint(Canvas canvas, Size size) {
    final paint = Paint()
      ..shader = RadialGradient(
        colors: [
          const Color(0xFF3B82F6).withValues(alpha: 0.4),
          const Color(0xFF3B82F6).withValues(alpha: 0.0),
        ],
        stops: const [0.25, 1.0],
      ).createShader(Rect.fromCircle(center: Offset(size.width / 2, size.height / 2), radius: size.width / 2))
      ..style = PaintingStyle.fill;

    final path = Path();
    final center = Offset(size.width / 2, size.height / 2);
    final radius = size.width / 2;

    // A 40-degree wide field-of-view cone pointing UP (-90 degrees / -pi/2)
    const double coneAngleRad = 40.0 * (pi / 180.0);
    const double startAngle = -pi / 2.0 - coneAngleRad / 2.0;

    path.moveTo(center.dx, center.dy);
    path.arcTo(
      Rect.fromCircle(center: center, radius: radius),
      startAngle,
      coneAngleRad,
      false,
    );
    path.close();

    canvas.drawPath(path, paint);
  }

  @override
  bool shouldRepaint(covariant CustomPainter oldDelegate) => false;
}

class FullScreenImagePage extends StatelessWidget {
  final String photoBase64;
  final String placeName;
  final String buildingId;

  const FullScreenImagePage({
    super.key,
    required this.photoBase64,
    required this.placeName,
    required this.buildingId,
  });

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      backgroundColor: Colors.black,
      extendBodyBehindAppBar: true,
      appBar: AppBar(
        backgroundColor: Colors.transparent,
        elevation: 0,
        leading: Container(
          margin: const EdgeInsets.all(8),
          decoration: BoxDecoration(
            color: Colors.black.withValues(alpha: 0.5),
            shape: BoxShape.circle,
          ),
          child: IconButton(
            icon: const Icon(Icons.close, color: Colors.white),
            onPressed: () => Navigator.pop(context),
          ),
        ),
        title: Text(
          placeName,
          style: const TextStyle(
            color: Colors.white,
            fontSize: 18,
            fontWeight: FontWeight.bold,
            shadows: [
              Shadow(
                blurRadius: 4.0,
                color: Colors.black54,
                offset: Offset(0, 2),
              ),
            ],
          ),
        ),
      ),
      body: Center(
        child: InteractiveViewer(
          minScale: 0.5,
          maxScale: 4.0,
          child: Hero(
            tag: 'building_photo_$buildingId',
            child: (() {
              final raw = photoBase64.trim();
              if (raw.startsWith('http://') || raw.startsWith('https://')) {
                return Image.network(
                  raw,
                  fit: BoxFit.contain,
                  width: double.infinity,
                  height: double.infinity,
                  errorBuilder: (_, __, ___) => const Center(
                    child: Icon(Icons.broken_image, color: Colors.white54, size: 48),
                  ),
                );
              }
              final bytes = safeBase64Decode(raw);
              if (bytes == null || bytes.isEmpty) {
                return const Center(
                  child: Icon(Icons.broken_image, color: Colors.white54, size: 48),
                );
              }
              return Image.memory(
                bytes,
                fit: BoxFit.contain,
                width: double.infinity,
                height: double.infinity,
              );
            })(),
          ),
        ),
      ),
    );
  }
}

final Map<String, Uint8List?> _base64DecodeCache = {};

Uint8List? safeBase64Decode(String? base64Str) {
  if (base64Str == null || base64Str.isEmpty) return null;

  var cleanStr = base64Str.trim();
  if (cleanStr.startsWith('"') && cleanStr.endsWith('"')) {
    cleanStr = cleanStr.substring(1, cleanStr.length - 1).trim();
  }
  if (cleanStr.startsWith("'") && cleanStr.endsWith("'")) {
    cleanStr = cleanStr.substring(1, cleanStr.length - 1).trim();
  }

  // Handle data URI prefix e.g. "data:image/jpeg;base64,/9j/4AAQSk..."
  if (cleanStr.contains(';base64,')) {
    cleanStr = cleanStr.split(';base64,').last.trim();
  } else if (cleanStr.startsWith('data:image')) {
    final commaIndex = cleanStr.indexOf(',');
    if (commaIndex != -1) {
      cleanStr = cleanStr.substring(commaIndex + 1).trim();
    }
  }

  // Remove potential whitespace or newlines inside base64 string
  cleanStr = cleanStr.replaceAll(RegExp(r'\s+'), '');

  if (cleanStr.isEmpty) return null;

  // Add missing base64 padding if required
  final mod = cleanStr.length % 4;
  if (mod > 0) {
    cleanStr += '=' * (4 - mod);
  }

  return _base64DecodeCache.putIfAbsent(cleanStr, () {
    try {
      return base64Decode(cleanStr);
    } catch (e) {
      debugPrint("Failed to decode base64: $e");
      return null;
    }
  });
}

class TtsHelper {
  static final FlutterTts _flutterTts = FlutterTts();
  static bool _initialized = false;

  static Future<void> _init() async {
    if (_initialized) return;
    try {
      await _flutterTts.setLanguage("en-US");

      // Platform-specific speech rate normalization
      // Android TTS scale: 0.0–2.0 (1.0 = normal)
      // iOS AVSpeech scale: 0.0–1.0 (0.5 = normal)
      // Web Speech API: 0.1–10.0 (1.0 = normal)
      if (kIsWeb) {
        await _flutterTts.setSpeechRate(1.0);
      } else if (defaultTargetPlatform == TargetPlatform.iOS) {
        await _flutterTts.setSpeechRate(0.5);
        // iOS audio session: enables TTS over music, ducks other audio
        await _flutterTts.setSharedInstance(true);
        await _flutterTts.setIosAudioCategory(
          IosTextToSpeechAudioCategory.playback,
          [
            IosTextToSpeechAudioCategoryOptions.mixWithOthers,
            IosTextToSpeechAudioCategoryOptions.duckOthers,
          ],
          IosTextToSpeechAudioMode.voicePrompt,
        );
      } else {
        // Android
        await _flutterTts.setSpeechRate(0.52);
      }

      await _flutterTts.setVolume(1.0);
      // Slightly higher pitch cuts through outdoor ambient noise
      await _flutterTts.setPitch(1.1);
      _initialized = true;
    } catch (e) {
      debugPrint("TTS init error: $e");
    }
  }

  static Future<void> speak(String text) async {
    try {
      await _init();
      await _flutterTts.speak(text);
    } catch (e) {
      debugPrint("TTS speak error: $e");
    }
  }

  static Future<void> stop() async {
    try {
      await _flutterTts.stop();
    } catch (e) {
      debugPrint("TTS stop error: $e");
    }
  }
}


