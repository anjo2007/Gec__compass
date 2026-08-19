import 'dart:convert';
import 'package:flutter/foundation.dart';
import 'package:flutter/services.dart' show rootBundle;
import 'package:shared_preferences/shared_preferences.dart';
import 'package:http/http.dart' as http;
import '../models/building.dart';

/// Top-level function for compute() isolate — parses campus JSON off main thread
List<Building> _parseBuildings(String jsonString) {
  final List<dynamic> jsonList = json.decode(jsonString);
  final all = jsonList.map((j) => Building.fromJson(j)).toList();
  return all.where((b) => b.name != 'Unnamed Location').toList();
}

class DataService {
  static const String _customBuildingsKey = 'custom_buildings';
  static const String _apiUrlCacheKey = 'cached_api_url';

  // Default Vercel API URL — used as fallback if dynamic config fetch fails
  static const String _defaultApiUrl = 'https://gecmaps.vercel.app/api/places';

  // GitHub raw URL for the config.json file in the repository (main branch)
  static const String _configUrl =
      'https://raw.githubusercontent.com/anjo2007/Gec__compass/main/config.json';
  static const String _fallbackConfigUrl =
      'https://raw.githubusercontent.com/anjo2007/GECMAPS/main/config.json';

  // Cached resolved API URL (in-memory for the session)
  String? _resolvedApiUrl;

  // Cached base campus buildings parsed from JSON asset
  List<Building>? _cachedBaseBuildings;

  /// Resolves the API URL dynamically.
  /// On Web, uses the current domain origin + '/api/places' to ensure same-origin consistency.
  /// On Mobile, reads from config.json on GitHub, falling back to local cache or default.
  Future<String> _getApiUrl() async {
    if (kIsWeb) {
      final baseUri = Uri.base;
      if ((baseUri.scheme == 'http' || baseUri.scheme == 'https') &&
          baseUri.host != 'localhost' &&
          baseUri.host != '127.0.0.1' &&
          !baseUri.host.startsWith('192.168.') &&
          !baseUri.host.startsWith('10.')) {
        final hasPort = baseUri.hasPort && baseUri.port != 80 && baseUri.port != 443;
        final portStr = hasPort ? ':${baseUri.port}' : '';
        return '${baseUri.scheme}://${baseUri.host}$portStr/api/places';
      }
    }

    // Return already-resolved URL if available this session
    if (_resolvedApiUrl != null) return _resolvedApiUrl!;

    // 1. Try reading locally cached URL from SharedPreferences first for sub-millisecond response
    try {
      final prefs = await SharedPreferences.getInstance();
      final cached = prefs.getString(_apiUrlCacheKey);
      if (cached != null && cached.isNotEmpty) {
        _resolvedApiUrl = cached;
        _checkGitHubConfigInBackground();
        return cached;
      }
    } catch (_) {}

    // 2. Fast-timeout check to GitHub config (1.5s max to prevent startup hang)
    try {
      final response = await http
          .get(Uri.parse(_configUrl))
          .timeout(const Duration(milliseconds: 1500));
      if (response.statusCode == 200) {
        final config = json.decode(response.body);
        final url = config['vercel_api_url'] as String?;
        if (url != null && url.isNotEmpty) {
          _resolvedApiUrl = url;
          final prefs = await SharedPreferences.getInstance();
          await prefs.setString(_apiUrlCacheKey, url);
          return url;
        }
      }
    } catch (e) {
      debugPrint('GitHub config quick-check skipped/failed: $e');
    }

    // 3. Fall back to hardcoded default
    _resolvedApiUrl = _defaultApiUrl;
    return _defaultApiUrl;
  }

  void _checkGitHubConfigInBackground() {
    http.get(Uri.parse(_configUrl)).timeout(const Duration(seconds: 4)).then((response) async {
      if (response.statusCode == 200) {
        final config = json.decode(response.body);
        final url = config['vercel_api_url'] as String?;
        if (url != null && url.isNotEmpty && url != _resolvedApiUrl) {
          _resolvedApiUrl = url;
          final prefs = await SharedPreferences.getInstance();
          await prefs.setString(_apiUrlCacheKey, url);
          debugPrint('Updated API URL in background: $url');
        }
      }
    }).catchError((_) {
      http.get(Uri.parse(_fallbackConfigUrl)).timeout(const Duration(seconds: 4)).then((fallbackRes) async {
        if (fallbackRes.statusCode == 200) {
          final config = json.decode(fallbackRes.body);
          final url = config['vercel_api_url'] as String?;
          if (url != null && url.isNotEmpty && url != _resolvedApiUrl) {
            _resolvedApiUrl = url;
            final prefs = await SharedPreferences.getInstance();
            await prefs.setString(_apiUrlCacheKey, url);
          }
        }
      }).catchError((_) {});
    });
  }

  /// Instant local building loader (asset + SharedPreferences cache)
  Future<List<Building>> loadLocalBuildings() async {
    try {
      if (_cachedBaseBuildings == null) {
        final String jsonString =
            await rootBundle.loadString('assets/campus_buildings.json');
        // On Web, synchronous parsing avoids Web Worker spin-up latency (~200ms) for small JSON
        if (kIsWeb) {
          _cachedBaseBuildings = _parseBuildings(jsonString);
        } else {
          _cachedBaseBuildings = await compute(_parseBuildings, jsonString);
        }
      }

      final localCustom = await _loadCustomBuildingsLocal();
      if (localCustom.isEmpty) {
        // Fast path: no custom buildings, return cached base directly (zero-copy)
        return List<Building>.from(_cachedBaseBuildings!);
      }

      final deletedIds = localCustom.where((b) => b.isDeleted).map((b) => b.id.toString().trim()).toSet();
      final activeCustom = localCustom.where((b) => !b.isDeleted).toList();
      final customIds = activeCustom.map((b) => b.id.toString().trim()).toSet();

      final result = <Building>[];
      for (final b in _cachedBaseBuildings!) {
        final id = b.id.toString().trim();
        if (!customIds.contains(id) && !deletedIds.contains(id)) {
          result.add(b);
        }
      }
      result.addAll(activeCustom);
      return result;
    } catch (e) {
      debugPrint('Error loading local buildings: $e');
      return [];
    }
  }

  /// Fast load method: returns local buildings instantly, while optionally starting a background cloud sync.
  Future<List<Building>> loadBuildings({bool syncCloudAsync = true, Function(List<Building>)? onCloudSynced}) async {
    // 1. Get instant local data
    final localList = await loadLocalBuildings();

    // 2. Fetch cloud buildings asynchronously in background if requested
    if (syncCloudAsync) {
      fetchCloudBuildings().then((updatedList) {
        if (onCloudSynced != null && updatedList.isNotEmpty) {
          onCloudSynced(updatedList);
        }
      }).catchError((e) {
        debugPrint('Async cloud sync error: $e');
      });
    }

    return localList;
  }

  static const String _lastKnownCloudIdsKey = 'last_known_cloud_ids';

  /// Fetches latest custom buildings from cloud API and merges with local data.
  Future<List<Building>> fetchCloudBuildings() async {
    try {
      final apiUrl = await _getApiUrl();
      final response = await http
          .get(Uri.parse(apiUrl))
          .timeout(const Duration(seconds: 4));
      
      if (response.statusCode == 200) {
        final decoded = json.decode(response.body);
        final List<dynamic> apiList = decoded is List ? decoded : [];
        List<Building> customBuildings =
            apiList.map((j) => Building.fromJson(j)).toList();

        final persistenceHeader = response.headers['x-storage-persistence'];
        if (persistenceHeader == 'none') {
          final localPlaces = await _loadCustomBuildingsLocal();
          final Map<String, Building> merged = {
            for (var b in localPlaces) b.id: b,
            for (var b in customBuildings) b.id: b,
          };
          customBuildings = merged.values.toList();
        } else {
          // isFromCloud: true — enables remote-deletion detection
          await _syncLocalCache(customBuildings, isFromCloud: true);
        }

        final deletedIds = customBuildings.where((b) => b.isDeleted).map((b) => b.id.toString().trim()).toSet();
        final activeCustom = customBuildings.where((b) => !b.isDeleted).toList();
        final customIds = activeCustom.map((b) => b.id.toString().trim()).toSet();

        final baseBuildings = await loadLocalBuildings();
        baseBuildings.removeWhere((b) => customIds.contains(b.id.toString().trim()) || deletedIds.contains(b.id.toString().trim()));
        baseBuildings.addAll(activeCustom);
        return baseBuildings;
      }
    } catch (e) {
      debugPrint('Cloud API fetch failed: $e');
    }
    return [];
  }

  /// Syncs buildings list into local SharedPreferences cache.
  ///
  /// When [isFromCloud] is true, compares the incoming cloud IDs against the
  /// previously-seen cloud IDs. Any ID that vanished from the cloud was deleted
  /// on another device — a local tombstone is created for it so that this device
  /// also stops showing the pin. This propagates cross-device deletions without
  /// needing the server to expose tombstones in its GET response.
  Future<void> _syncLocalCache(List<Building> buildings, {bool isFromCloud = false}) async {
    try {
      final prefs = await SharedPreferences.getInstance();
      final existingLocal = await _loadCustomBuildingsLocal();

      if (isFromCloud) {
        // Detect IDs that existed in cloud before but are gone now (deleted remotely)
        final lastKnownJson = prefs.getString(_lastKnownCloudIdsKey);
        final Set<String> lastKnownCloudIds = lastKnownJson != null
            ? Set<String>.from((json.decode(lastKnownJson) as List).cast<String>())
            : <String>{};

        final currentCloudIds = buildings.map((b) => b.id.toString().trim()).toSet();

        // IDs present in last known cloud snapshot but absent now → remote deletion
        final remotelyDeletedIds = lastKnownCloudIds.difference(currentCloudIds);

        // Persist the updated snapshot for next sync comparison
        await prefs.setString(_lastKnownCloudIdsKey, json.encode(currentCloudIds.toList()));

        // Standard merge: local first, cloud overrides
        final Map<String, Building> merged = {
          for (var b in existingLocal) b.id.toString().trim(): b,
          for (var b in buildings) b.id.toString().trim(): b,
        };

        // Create tombstones for remotely deleted IDs so this device hides them
        for (final deletedId in remotelyDeletedIds) {
          merged[deletedId] = Building(
            id: deletedId,
            name: 'Deleted Place',
            lat: 0.0,
            lng: 0.0,
            tags: {'deleted': true},
            isDeleted: true,
          );
        }

        final String customJsonString =
            json.encode(merged.values.map((b) => b.toJson()).toList());
        await prefs.setString(_customBuildingsKey, customJsonString);
      } else {
        // Local-only operation (save/delete): simple merge, no remote-deletion detection
        final Map<String, Building> merged = {
          for (var b in existingLocal) b.id.toString().trim(): b,
          for (var b in buildings) b.id.toString().trim(): b,
        };
        final String customJsonString =
            json.encode(merged.values.map((b) => b.toJson()).toList());
        await prefs.setString(_customBuildingsKey, customJsonString);
      }
    } catch (e) {
      debugPrint('Error syncing local cache: $e');
    }
  }

  Future<List<Building>> _loadCustomBuildingsLocal() async {
    try {
      final prefs = await SharedPreferences.getInstance();
      final String? customJsonString = prefs.getString(_customBuildingsKey);
      if (customJsonString != null) {
        final List<dynamic> customJsonList = json.decode(customJsonString);
        return customJsonList.map((json) => Building.fromJson(json)).toList();
      }
    } catch (e) {
      debugPrint(
          'Error loading custom buildings from SharedPreferences: $e');
    }
    return [];
  }

  Future<Building> saveCustomBuilding(Building building) async {
    // 1. Local-first save so data is never lost offline
    try {
      final customBuildings = await _loadCustomBuildingsLocal();
      customBuildings.removeWhere((b) => b.id == building.id);
      customBuildings.add(building);
      await _syncLocalCache(customBuildings);
      debugPrint('Saved custom building locally first: ${building.name}');
    } catch (e) {
      debugPrint('Error saving custom building locally first: $e');
    }

    // 2. Sync to cloud API
    try {
      final apiUrl = await _getApiUrl();
      final response = await http
          .post(
            Uri.parse(apiUrl),
            headers: {'Content-Type': 'application/json'},
            body: json.encode(building.toJson()),
          )
          .timeout(const Duration(seconds: 15));

      if (response.statusCode == 200) {
        debugPrint('Synced custom building to cloud: ${building.name}');
        Building savedBuilding = building;
        try {
          final decoded = json.decode(response.body);
          if (decoded is Map && decoded['place'] != null) {
            savedBuilding = Building.fromJson(decoded['place']);
            final customBuildings = await _loadCustomBuildingsLocal();
            customBuildings.removeWhere((b) => b.id == savedBuilding.id);
            customBuildings.add(savedBuilding);
            await _syncLocalCache(customBuildings);
          }
        } catch (e) {
          debugPrint('Error parsing returned cloud building: $e');
        }
        return savedBuilding;
      } else {
        debugPrint('Cloud sync response status ${response.statusCode}');
      }
    } catch (e) {
      debugPrint('Cloud sync offline / network error: $e');
    }

    // Return locally saved building if cloud sync is pending/offline
    return building;
  }

  Future<void> deleteCustomBuilding(String id, String code) async {
    final cleanCode = code.trim();
    if (cleanCode.isEmpty) {
      throw Exception('Security verification code is required to delete a place.');
    }

    final apiUrl = await _getApiUrl();
    final uri = Uri.parse(apiUrl).replace(queryParameters: {
      'id': id,
      'code': cleanCode,
    });

    final response = await http
        .delete(
          uri,
          headers: {'x-security-code': cleanCode},
        )
        .timeout(const Duration(seconds: 15));

    if (response.statusCode == 200) {
      debugPrint('Deleted custom building from cloud: $id');
      // Update local cache deletion only after verified server approval
      try {
        final customBuildings = await _loadCustomBuildingsLocal();
        customBuildings.removeWhere((b) => b.id.toString().trim() == id.toString().trim());
        customBuildings.add(Building(
          id: id,
          name: 'Deleted Place',
          lat: 0.0,
          lng: 0.0,
          tags: {'deleted': true},
          isDeleted: true,
        ));
        await _syncLocalCache(customBuildings);
        debugPrint('Recorded building deletion locally: $id');
      } catch (e) {
        debugPrint('Error removing custom building locally: $e');
      }
    } else if (response.statusCode == 403) {
      throw Exception('Unauthorized: Invalid security code');
    } else {
      String? cloudErrorMessage;
      try {
        final decoded = json.decode(response.body);
        if (decoded is Map && decoded['error'] != null) {
          cloudErrorMessage = decoded['error'].toString();
        }
      } catch (_) {}
      throw Exception(cloudErrorMessage ?? 'Failed to delete pin from server (status ${response.statusCode})');
    }
  }

  Future<String> getBaseShareUrl(String buildingId) async {
    try {
      final apiUrl = await _getApiUrl();
      final uri = Uri.parse(apiUrl);
      final hasCustomPort = uri.hasPort && uri.port != 80 && uri.port != 443;
      final portStr = hasCustomPort ? ':${uri.port}' : '';
      return '${uri.scheme}://${uri.host}$portStr/api/share?id=$buildingId';
    } catch (e) {
      debugPrint('Error generating share URL: $e');
      return 'https://gecmaps.vercel.app/api/share?id=$buildingId';
    }
  }
}
