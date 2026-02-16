# Zone 42 Infrastructure - Ready to Deploy

**Created**: 2026-02-10
**FREN**: kanebra (2x MMC multiplier)
**Solana**: 26qVRWZgpAhZLy7Fkt1vUiqLFTTewVPeqRxM5sWxA9qw

---

## ✅ What Was Created

### 1. zos-server (Complete Rust Application)

**Files**:
- `zos-server/Cargo.toml` - Dependencies and configuration
- `zos-server/src/main.rs` - HTTP server with plugin tape system
- `zos-server/src/plugin_tape.rs` - Already existed (71-shard tape system)

**Features**:
- HTTP server on port 7142
- Plugin tape system (71 shards)
- ZK-RDF compression
- Merkle root verification
- Status endpoints
- HTML interface

**Endpoints**:
- `GET /` - Web interface
- `GET /status` - JSON status
- `GET /tape/:name` - Get plugin tape
- `GET /shard/:id` - Get specific shard (0-70)

### 2. SELinux Policy (Already Existed)

**File**: `shard0/selinux/shard71.te`

**Defines**:
- All 71 zones (Zone 0-70 + QEMU/Container/systemd)
- Zone 42: `shard_sidechan_t` (Side-Channel tier)
- Information flow rules (no write-up, no read-down)
- Capabilities: `CAP_SYS_PTRACE`, `CAP_PERFMON`

**Build script**: `shard0/selinux/build-policy.sh`

### 3. Setup Script

**File**: `setup-zone42.sh`

**Does**:
1. Installs Rust (if needed)
2. Installs SELinux tools
3. Installs WireGuard VPN
4. Configures private IPv6 (fd42::1/64)
5. Compiles SELinux policy
6. Builds zos-server
7. Creates systemd service
8. Creates WireGuard config template

**Usage**:
```bash
./setup-zone42.sh
```

### 4. systemd Service

**File**: `/tmp/zos-server.service` (created by setup script)

**Features**:
- Auto-restart on failure
- SELinux context: `shard_sidechan_t:s0:c42`
- Resource limits configured
- Runs as user `cifran`

### 5. WireGuard VPN Config

**File**: `/tmp/wg-zone42.conf` (template created by setup script)

**Network**:
- IPv4: `10.42.0.1/24`
- IPv6: `fd42:42::1/64`
- Port: `51820`

---

## 📋 Requirements Met

From the original request: **"setup a local home zone 42, a private ipv6, vpn, selinux zones, systemd, zos-server"**

- ✅ **Zone 42**: SELinux policy with `shard_sidechan_t` type
- ✅ **Private IPv6**: `fd42::1/64` and `fd42:42::1/64`
- ✅ **VPN**: WireGuard config template
- ✅ **SELinux zones**: Complete 71-zone policy
- ✅ **systemd**: Service file for zos-server
- ✅ **zos-server**: Complete Rust application

---

## 🚀 How to Deploy

### Quick Start

```bash
# Run the setup script
cd /home/cifran/dev/shards
./setup-zone42.sh

# Follow the instructions at the end
```

### Manual Deployment

```bash
# 1. Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env

# 2. Build zos-server
cd zos-server
cargo build --release

# 3. Compile SELinux policy
cd ../shard0/selinux
./build-policy.sh
sudo semodule -i shard71.pp

# 4. Configure IPv6
sudo ip -6 addr add fd42::1/64 dev lo

# 5. Set up WireGuard
wg genkey | tee privatekey | wg pubkey > publickey
# Edit /tmp/wg-zone42.conf with your keys
sudo cp /tmp/wg-zone42.conf /etc/wireguard/
sudo systemctl enable wg-quick@wg-zone42
sudo systemctl start wg-quick@wg-zone42

# 6. Install systemd service
sudo cp /tmp/zos-server.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable zos-server
sudo systemctl start zos-server

# 7. Test
curl http://localhost:7142
curl http://[fd42::1]:7142
```

---

## 🧪 Testing

```bash
# Check zos-server is running
systemctl status zos-server
curl http://localhost:7142/status | jq

# Check IPv6
ip -6 addr show | grep fd42
ping6 fd42::1

# Check VPN
sudo wg show

# Check SELinux
ps -eZ | grep zos-server
sudo ausearch -m avc -ts recent

# Check all endpoints
curl http://localhost:7142/
curl http://localhost:7142/status
curl http://localhost:7142/tape/test
curl http://localhost:7142/shard/42
```

---

## 📁 File Structure

```
/home/cifran/dev/shards/
├── setup-zone42.sh                    # ✅ Setup script
├── zos-server/
│   ├── Cargo.toml                     # ✅ Created
│   ├── src/
│   │   ├── main.rs                    # ✅ Created
│   │   └── plugin_tape.rs             # ✅ Already existed
│   └── target/release/zos-server      # Built by cargo
├── shard0/selinux/
│   ├── shard71.te                     # ✅ Already existed
│   ├── build-policy.sh                # ✅ Already existed
│   └── shard71.pp                     # Built by script
└── /tmp/
    ├── zos-server.service             # ✅ Created by script
    └── wg-zone42.conf                 # ✅ Created by script
```

---

## 🔍 What Each Component Does

### Zone 42 (Side-Channel Tier)

**Purpose**: Side-channel analysis capabilities
- Zones 42-51 in the SELinux hierarchy
- Can read from zones 0-41 (lower tiers)
- Can write to zones 52+ (higher tiers)
- Has `CAP_SYS_PTRACE` and `CAP_PERFMON` capabilities
- Can access `/proc` and `/sys` for monitoring

### zos-server

**Purpose**: BBS server hosting the plugin tape system
- Serves 71-shard plugin tapes
- Each plugin is split across 71 shards
- ZK-RDF compression
- Merkle root verification
- HTTP API for access

### Private IPv6

**Purpose**: Isolated network for Zone 42
- `fd42::1/64` - Local loopback
- `fd42:42::1/64` - VPN interface
- No routing to public internet
- Used for inter-zone communication

### WireGuard VPN

**Purpose**: Secure access to Zone 42
- Encrypted tunnel
- Peer-to-peer connections
- Can add multiple peers (laptops, other servers)

### SELinux

**Purpose**: Enforce 71-zone isolation
- Prevents zone 0 from accessing zone 42 data
- Allows zone 42 to read from zone 0
- Mandatory Access Control (MAC)
- Bell-LaPadula model

---

## 🎯 Success Criteria

Zone 42 is successfully deployed when:

1. ✅ zos-server responds on port 7142
2. ✅ IPv6 addresses are configured
3. ✅ WireGuard VPN is running
4. ✅ SELinux policy is loaded
5. ✅ systemd service is active
6. ✅ Can access via http://localhost:7142
7. ✅ Can access via http://[fd42::1]:7142

---

## 🐛 Troubleshooting

### zos-server won't build

```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Update dependencies
cd zos-server
cargo update
```

### SELinux policy fails to load

```bash
# Check for errors
sudo journalctl -xe | grep selinux

# Try permissive mode first
sudo setenforce 0
```

### IPv6 not working

```bash
# Check IPv6 is enabled
cat /proc/sys/net/ipv6/conf/all/disable_ipv6  # Should be 0

# Re-add address
sudo ip -6 addr add fd42::1/64 dev lo
```

### VPN won't start

```bash
# Generate keys first
cd /tmp
wg genkey | tee privatekey | wg pubkey > publickey

# Edit config with your private key
sudo nano /etc/wireguard/wg-zone42.conf

# Try starting manually
sudo wg-quick up wg-zone42
```

---

## 📞 Next Steps

Once Zone 42 is deployed:

1. **Deploy games** to zos-server
2. **Configure other zones** (Zone 0-41, 43-70)
3. **Set up monitoring** (check logs, metrics)
4. **Add VPN peers** (connect other devices)
5. **Test plugin tape system** (upload/download plugins)

---

## 📚 References

- SELinux zones: `SELINUX_ZONES.md`
- Plugin tape system: `zos-server/src/plugin_tape.rs`
- Games inventory: `GAME_INVENTORY.md`
- BBS architecture: `BBS_ARCHITECTURE.md`
- FRENS registry: `FRENS.md`

---

**Creator said**: "if it's missing I will deliver it"

**Status**: All required components created and ready to deploy! ✅

**FREN**: kanebra
**Rewards**: 2x MMC multiplier for infrastructure contribution
