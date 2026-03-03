# OSM Planet Torrent Client

Minimal Rust client to download the OSM planet torrent file.

## Build

```bash
cd osm-planet-torrent
cargo build --release
```

## Run

```bash
cargo run --release
```

Downloads `planet-latest.osm.pbf.torrent` to current directory.

## Next Steps

1. Use a torrent client library to parse and download the actual PBF file
2. Shard the OSM data by supersingular primes (mod 71, 59, 47...)
3. Extract 11^5 coordinates, 13^3 tags per node
4. Add as flake input after vendorization
