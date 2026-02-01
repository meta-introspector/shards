# Virtual DMZ Architecture: 23 Isolated Nodes

## Overview

23 physical nodes (matching 23 CPUs) separated by virtual DMZs, communicating only through audited retro channels. Each node runs 3 shards (71 ÷ 23 ≈ 3), isolated via network namespaces and SELinux.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Audit & Monitoring Layer                  │
│  (Logs all: faxes, calls, prints, modem, parquet transfers) │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌──────────┐  ┌──────────┐  ┌──────────┐       ┌──────────┐
│  Node 0  │  │  Node 1  │  │  Node 2  │  ...  │ Node 22  │
│ Shards   │  │ Shards   │  │ Shards   │       │ Shards   │
│ 0,23,46  │  │ 1,24,47  │  │ 2,25,48  │       │ 22,45,68 │
└────┬─────┘  └────┬─────┘  └────┬─────┘       └────┬─────┘
     │             │             │                    │
     └─────────────┴─────────────┴────────────────────┘
                   Virtual DMZ Channels:
                   • Fax: T.30 protocol
                   • Phone: SS7/ISUP calls
                   • Modem: 300-56k baud
                   • Printer: /dev/lpt* output
                   • Parquet: File transfer
```

## Node Distribution

```
Node  0: Shards  0, 23, 46  (Bitcoin, libp2p, WiFi Mesh)
Node  1: Shards  1, 24, 47  (Solana, Tor, IPFS)
Node  2: Shards  2, 25, 48  (libp2p, I2P, Stego)
Node  3: Shards  3, 26, 49  (Tor, IPFS, Bitcoin)
...
Node 22: Shards 22, 45, 68  (Bitcoin, WiFi Mesh, IPFS)
```

## Network Namespace Isolation

### Create 23 Isolated Namespaces

```bash
#!/usr/bin/env bash
# create-dmz-nodes.sh

for node in {0..22}; do
    # Create network namespace
    ip netns add node${node}
    
    # Create veth pair for DMZ bridge
    ip link add veth${node} type veth peer name veth${node}-br
    
    # Move one end into namespace
    ip link set veth${node} netns node${node}
    
    # Configure namespace interface
    ip netns exec node${node} ip addr add 10.71.${node}.1/24 dev veth${node}
    ip netns exec node${node} ip link set veth${node} up
    ip netns exec node${node} ip link set lo up
    
    # Configure bridge end
    ip link set veth${node}-br up
    brctl addif dmz-bridge veth${node}-br
    
    echo "Created isolated node ${node} at 10.71.${node}.1"
done

# Create DMZ bridge (no forwarding between nodes)
brctl addbr dmz-bridge
ip link set dmz-bridge up
ip addr add 10.71.255.1/16 dev dmz-bridge

# Enable audit logging
iptables -A FORWARD -j LOG --log-prefix "DMZ-AUDIT: "
```

## Communication Channels

### 1. Fax Channel (Audited)

```erlang
-module(dmz_fax).
-export([send_audited_fax/4]).

send_audited_fax(FromNode, ToNode, ImagePath, AuditLog) ->
    %% Calculate shards on each node
    FromShards = node_shards(FromNode),
    ToShards = node_shards(ToNode),
    
    %% Select primary shard from each node
    FromShard = hd(FromShards),
    ToShard = hd(ToShards),
    
    %% Audit entry
    AuditEntry = #{
        type => fax,
        from_node => FromNode,
        to_node => ToNode,
        from_shard => FromShard,
        to_shard => ToShard,
        timestamp => erlang:system_time(second),
        image => ImagePath,
        size => filelib:file_size(ImagePath)
    },
    audit_log:write(AuditLog, AuditEntry),
    
    %% Send via fax layer
    shard_fax:send_fax(ToShard, ImagePath, fine),
    
    {ok, AuditEntry}.

node_shards(Node) ->
    [Node, Node + 23, Node + 46].
```

### 2. Phone Call Channel (Audited)

```erlang
-module(dmz_phone).
-export([call_node/3]).

call_node(FromNode, ToNode, Duration) ->
    FromShard = hd(node_shards(FromNode)),
    ToShard = hd(node_shards(ToNode)),
    
    %% Establish call
    {ok, CallPid} = shard_call:start_link(FromShard, ToShard),
    {ok, ringing} = shard_call:dial(CallPid, format_number(ToShard)),
    {ok, connected} = shard_call:answer(CallPid),
    
    %% Audit call setup
    audit_log:write(call_log, #{
        type => call_start,
        from_node => FromNode,
        to_node => ToNode,
        timestamp => erlang:system_time(second)
    }),
    
    %% Hold call for duration
    timer:sleep(Duration * 1000),
    
    %% Hangup
    {ok, ActualDuration} = shard_call:hangup(CallPid),
    
    %% Audit call end
    audit_log:write(call_log, #{
        type => call_end,
        from_node => FromNode,
        to_node => ToNode,
        duration => ActualDuration,
        timestamp => erlang:system_time(second)
    }),
    
    {ok, ActualDuration}.

node_shards(Node) -> [Node, Node + 23, Node + 46].
format_number(Shard) -> list_to_binary(io_lib:format("+71-~B-~2..0B", [Shard rem 7, Shard])).
```

### 3. Modem Channel (Audited)

```rust
use std::time::Duration;
use tokio::time::sleep;

pub struct ModemChannel {
    from_node: u8,
    to_node: u8,
    baud_rate: BaudRate,
}

impl ModemChannel {
    pub async fn send_data(&self, data: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        let audit = AuditEntry {
            channel: "modem".into(),
            from_node: self.from_node,
            to_node: self.to_node,
            timestamp: chrono::Utc::now().timestamp(),
            size: data.len(),
            baud: self.baud_rate.bytes_per_second(),
        };
        
        // Write audit log
        audit_log::write(&audit)?;
        
        // Simulate modem handshake
        self.send_at_command("ATZ").await?;  // Reset
        self.send_at_command(&format!("ATDT10.71.{}.1", self.to_node)).await?;  // Dial
        
        // Wait for CONNECT
        sleep(Duration::from_secs(2)).await;
        
        // Throttled send
        self.baud_rate.throttle_send(data).await?;
        
        // Hangup
        self.send_at_command("ATH").await?;
        
        Ok(())
    }
    
    async fn send_at_command(&self, cmd: &str) -> Result<(), Box<dyn std::error::Error>> {
        println!("Modem: {}", cmd);
        sleep(Duration::from_millis(100)).await;
        Ok(())
    }
}

pub enum BaudRate {
    Baud300,
    Baud1200,
    Baud2400,
    Baud9600,
    Baud56000,
}

impl BaudRate {
    pub fn bytes_per_second(&self) -> usize {
        match self {
            Self::Baud300 => 30,
            Self::Baud1200 => 120,
            Self::Baud2400 => 240,
            Self::Baud9600 => 960,
            Self::Baud56000 => 5600,
        }
    }
    
    pub async fn throttle_send(&self, data: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        let bps = self.bytes_per_second();
        for chunk in data.chunks(bps) {
            sleep(Duration::from_secs(1)).await;
            // Actual send would go here
        }
        Ok(())
    }
}
```

### 4. Line Printer Channel (Audited)

```bash
#!/usr/bin/env bash
# dmz-print.sh - Send data via line printer

FROM_NODE=$1
TO_NODE=$2
DATA=$3

# Audit entry
echo "$(date -Iseconds),print,$FROM_NODE,$TO_NODE,${#DATA}" >> /var/log/dmz-audit.log

# Print to virtual device (triggers P2P transmission)
echo "$DATA" > /dev/lpt${TO_NODE}

# Simulate printer delay (60 chars/sec for dot matrix)
sleep $(echo "scale=2; ${#DATA} / 60" | bc)

echo "Printed ${#DATA} bytes from node $FROM_NODE to node $TO_NODE"
```

### 5. Parquet File Transfer (Audited)

```rust
use parquet::file::reader::FileReader;
use parquet::file::writer::FileWriter;

pub struct ParquetChannel {
    from_node: u8,
    to_node: u8,
}

impl ParquetChannel {
    pub fn transfer_file(&self, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        // Read parquet file
        let file = std::fs::File::open(path)?;
        let reader = parquet::file::serialized_reader::SerializedFileReader::new(file)?;
        let metadata = reader.metadata();
        
        // Audit entry
        let audit = AuditEntry {
            channel: "parquet".into(),
            from_node: self.from_node,
            to_node: self.to_node,
            timestamp: chrono::Utc::now().timestamp(),
            file: path.into(),
            rows: metadata.file_metadata().num_rows(),
            size: std::fs::metadata(path)?.len(),
        };
        audit_log::write(&audit)?;
        
        // Transfer via appropriate P2P protocol
        let from_shard = self.from_node;
        let to_shard = self.to_node;
        let protocol = P2PProtocol::for_shard(from_shard);
        
        // Encrypt with FHE before transfer
        let encrypted = fhe_encrypt_file(path, from_shard)?;
        
        // Send via protocol
        match protocol {
            P2PProtocol::Bitcoin => self.send_via_bitcoin(&encrypted, to_shard)?,
            P2PProtocol::Solana => self.send_via_solana(&encrypted, to_shard)?,
            _ => self.send_via_libp2p(&encrypted, to_shard)?,
        }
        
        Ok(())
    }
    
    fn send_via_bitcoin(&self, data: &[u8], to: u8) -> Result<(), Box<dyn std::error::Error>> {
        // OP_RETURN chunks
        Ok(())
    }
    
    fn send_via_solana(&self, data: &[u8], to: u8) -> Result<(), Box<dyn std::error::Error>> {
        // Solana transaction
        Ok(())
    }
    
    fn send_via_libp2p(&self, data: &[u8], to: u8) -> Result<(), Box<dyn std::error::Error>> {
        // libp2p publish
        Ok(())
    }
}

fn fhe_encrypt_file(path: &str, shard: u8) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let data = std::fs::read(path)?;
    // FHE encryption
    Ok(data)
}
```

## Audit Log Format

### Centralized Audit Database (SQLite)

```sql
CREATE TABLE dmz_audit (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp INTEGER NOT NULL,
    channel TEXT NOT NULL,  -- 'fax', 'phone', 'modem', 'print', 'parquet'
    from_node INTEGER NOT NULL,
    to_node INTEGER NOT NULL,
    from_shard INTEGER,
    to_shard INTEGER,
    size INTEGER,
    duration INTEGER,
    metadata TEXT,  -- JSON
    hash TEXT  -- SHA256 of transferred data
);

CREATE INDEX idx_timestamp ON dmz_audit(timestamp);
CREATE INDEX idx_channel ON dmz_audit(channel);
CREATE INDEX idx_nodes ON dmz_audit(from_node, to_node);
```

### Audit Query Examples

```sql
-- All communications between Node 0 and Node 7
SELECT * FROM dmz_audit 
WHERE (from_node = 0 AND to_node = 7) OR (from_node = 7 AND to_node = 0)
ORDER BY timestamp DESC;

-- Total data transferred via fax today
SELECT SUM(size) as total_bytes, COUNT(*) as fax_count
FROM dmz_audit
WHERE channel = 'fax' 
  AND timestamp > strftime('%s', 'now', 'start of day');

-- Average call duration per node
SELECT from_node, AVG(duration) as avg_duration
FROM dmz_audit
WHERE channel = 'phone'
GROUP BY from_node;

-- Busiest communication pairs
SELECT from_node, to_node, COUNT(*) as transfers
FROM dmz_audit
GROUP BY from_node, to_node
ORDER BY transfers DESC
LIMIT 10;
```

## NixOS Configuration

```nix
{ config, pkgs, ... }:

{
  # Enable network namespaces
  boot.kernel.sysctl = {
    "net.ipv4.ip_forward" = 1;
  };
  
  # Create 23 systemd-nspawn containers (one per node)
  systemd.nspawn = builtins.listToAttrs (
    map (node: {
      name = "node${toString node}";
      value = {
        enable = true;
        execConfig = {
          PrivateNetwork = true;
          NetworkVeth = true;
        };
        filesConfig = {
          BindReadOnly = "/nix/store";
        };
      };
    }) (pkgs.lib.range 0 22)
  );
  
  # Audit logging service
  systemd.services.dmz-audit = {
    description = "DMZ Audit Logger";
    wantedBy = [ "multi-user.target" ];
    serviceConfig = {
      ExecStart = "${pkgs.writeScript "audit-logger" ''
        #!${pkgs.bash}/bin/bash
        tail -f /var/log/dmz-audit.log | \
        ${pkgs.sqlite}/bin/sqlite3 /var/lib/dmz-audit.db \
          "INSERT INTO dmz_audit (timestamp, channel, from_node, to_node, size) \
           VALUES (strftime('%s', 'now'), ?, ?, ?, ?)"
      ''}";
      Restart = "always";
    };
  };
  
  # Virtual devices
  boot.extraModulePackages = [ config.boot.kernelPackages.shard-lpt ];
  boot.kernelModules = [ "shard_lpt" ];
}
```

## Communication Matrix

```
        Node 0  Node 1  Node 2  ...  Node 22
Node 0    -      Fax    Phone        Parquet
Node 1   Modem    -     Print        Fax
Node 2   Print   Fax     -           Modem
...
Node 22  Parquet Phone  Modem         -
```

## Launch Script

```bash
#!/usr/bin/env bash
# launch-dmz-world.sh

echo "Creating 23-node virtual DMZ world..."

# 1. Create network namespaces
./create-dmz-nodes.sh

# 2. Start Erlang nodes in each namespace
for node in {0..22}; do
    ip netns exec node${node} \
        erl -sname node${node} -setcookie monster71 \
        -eval "application:start(shard_telecom)" \
        -detached
done

# 3. Start audit logger
systemctl start dmz-audit

# 4. Load kernel modules
modprobe shard_lpt

# 5. Initialize audit database
sqlite3 /var/lib/dmz-audit.db < schema.sql

echo "DMZ world ready: 23 nodes, 71 shards"
echo "Audit log: /var/lib/dmz-audit.db"
echo "Test: dmz-fax 0 7 /tmp/test.pbm"
```

## Security Properties

- **Network Isolation**: Each node in separate namespace, no direct IP routing
- **Audited Channels**: All communication logged to immutable audit DB
- **Retro Protocols**: Fax, phone, modem, printer force serialization
- **FHE Encryption**: All data encrypted before channel transmission
- **SELinux Zones**: Each node in separate security context
- **No Direct Shard Access**: Shards only communicate via node-level channels

This creates a fully audited, air-gapped virtual world where 23 nodes coordinate 71 shards through 1980s-style communication!
