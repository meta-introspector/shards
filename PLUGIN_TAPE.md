# Plugin Tape System

Each plugin = tape = ZK-RDF compressed blob = 71 shards

## Minimal Implementation

```rust
PluginTape {
    name: String,
    shards: [TapeShard; 71],
    merkle_root: [u8; 32],
}

TapeShard {
    id: u8,
    blob: Vec<u8>,  // gzip(RDF)
    hash: [u8; 32],
}
```

## Flow

```
Binary → 71 chunks → RDF → gzip → hash → Merkle tree
```

## Usage

```rust
// Create tape
let tape = PluginTape::from_binary("bbs".into(), &binary);
tape.save("plugins/bbs")?;

// Load tape
let tape = PluginTape::load("plugins/bbs")?;
let binary = tape.reconstruct();
```

## Storage

```
plugins/bbs/
├── manifest.json
├── shard00.tape
├── shard01.tape
...
└── shard70.tape
```

Done.
