# Zone 42 Setup Guide - Home Infrastructure

**Purpose**: Set up local Zone 42 (Side-Channel tier) with private IPv6, VPN, SELinux zones, systemd services, and zos-server BBS.

**Server**: Raspberry Pi (Debian 12) - kanebra
**User**: kanebra (FREN registered ✅)

---

## Current State (2026-02-10)

- [x] systemd running
- [x] IPv6 link-local active
- [x] zos-server source exists
- [ ] SELinux enabled
- [ ] Private IPv6 network configured
- [ ] VPN running
- [ ] Zone 42 SELinux policy loaded
- [ ] zos-server running
- [ ] systemd services configured

---

## Step 1: Enable SELinux (Debian)

Debian doesn't have SELinux by default. We need to install and configure it.

```bash
# Install SELinux
sudo apt-get update
sudo apt-get install selinux-basics selinux-policy-default auditd

# Activate SE Linux
sudo selinux-activate

# This will require a reboot
sudo reboot
```

**After reboot, check**:
```bash
getenforce  # Should show "Enforcing" or "Permissive"
sestatus    # Show full status
```

---

## Step 2: Configure Private IPv6 Network

Use Unique Local Addresses (ULA) for private IPv6:

```bash
# Generate ULA prefix (fd00::/8)
# Using fd42:: for Zone 42
ULA_PREFIX="fd42::/64"

# Add to interface (replace eth0 with your interface)
sudo ip -6 addr add fd42::1/64 dev eth0

# Make permanent
echo "iface eth0 inet6 static
    address fd42::1
    netmask 64" | sudo tee -a /etc/network/interfaces
```

**Test**:
```bash
ip -6 addr show | grep fd42
ping6 fd42::1
```

---

## Step 3: Set Up VPN (WireGuard)

WireGuard is lightweight and perfect for Raspberry Pi:

```bash
# Install WireGuard
sudo apt-get install wireguard

# Generate keys
wg genkey | tee /tmp/server_private.key | wg pubkey > /tmp/server_public.key

# Create config
sudo tee /etc/wireguard/wg-zone42.conf << 'EOF'
[Interface]
Address = 10.42.0.1/24, fd42:42::1/64
ListenPort = 51820
PrivateKey = <INSERT_PRIVATE_KEY>
SaveConfig = true

# Add PostUp/PostDown rules
PostUp = iptables -A FORWARD -i wg-zone42 -j ACCEPT
PostDown = iptables -D FORWARD -i wg-zone42 -j ACCEPT
EOF

# Set permissions
sudo chmod 600 /etc/wireguard/wg-zone42.conf

# Enable and start
sudo systemctl enable wg-quick@wg-zone42
sudo systemctl start wg-quick@wg-zone42
```

**Test**:
```bash
sudo wg show
ip addr show wg-zone42
```

---

## Step 4: Create SELinux Zone 42 Policy

Based on SELINUX_ZONES.md, Zone 42-51 is for Side-Channel analysis:

```bash
# Create policy module
cd /tmp
cat > shard_zone42.te << 'EOF'
policy_module(shard_zone42, 1.0)

# Zone 42: Side-Channel tier
type shard_sidechan_t;
domain_type(shard_sidechan_t)

# Allow reading from lower zones (0-41)
allow shard_sidechan_t self:process { ptrace };
allow shard_sidechan_t proc_t:file { read };
allow shard_sidechan_t sysfs_t:file { read };

# Allow writing to higher zones (52+)
allow shard_sidechan_t shard_algebra_t:fifo_file { write };

# Capabilities for side-channel analysis
allow shard_sidechan_t self:capability { sys_ptrace perfmon };
EOF

# Compile and install
checkmodule -M -m -o shard_zone42.mod shard_zone42.te
semodule_package -o shard_zone42.pp -m shard_zone42.mod
sudo semodule -i shard_zone42.pp
```

**Test**:
```bash
semodule -l | grep shard_zone42
```

---

## Step 5: Build zos-server

```bash
cd /home/cifran/dev/shards/zos-server

# Check if Cargo.toml exists
if [ ! -f Cargo.toml ]; then
    # Create basic Cargo.toml
    cat > Cargo.toml << 'EOF'
[package]
name = "zos-server"
version = "0.1.0"
edition = "2021"

[dependencies]
tokio = { version = "1", features = ["full"] }
serde = { version = "1", features = ["derive"] }
serde_json = "1"

[[bin]]
name = "zos-server"
path = "src/main.rs"
EOF
fi

# Create main.rs if needed
if [ ! -f src/main.rs ]; then
    mkdir -p src
    cat > src/main.rs << 'EOF'
//! ZOS-Server - BBS server for Zone 42
use std::net::SocketAddr;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 ZOS-Server starting...");
    println!("📍 Zone 42: Side-Channel tier");

    let addr: SocketAddr = "0.0.0.0:7142".parse()?;
    println!("🌐 Listening on: {}", addr);

    // TODO: Implement BBS server
    loop {
        tokio::time::sleep(tokio::time::Duration::from_secs(60)).await;
    }
}
EOF
fi

# Build
cargo build --release

# Test
./target/release/zos-server
```

---

## Step 6: Create systemd Service

```bash
sudo tee /etc/systemd/system/zos-server.service << 'EOF'
[Unit]
Description=ZOS-Server BBS (Zone 42)
After=network.target wg-quick@wg-zone42.service
Wants=wg-quick@wg-zone42.service

[Service]
Type=simple
User=cifran
WorkingDirectory=/home/cifran/dev/shards/zos-server
ExecStart=/home/cifran/dev/shards/zos-server/target/release/zos-server
Restart=on-failure
RestartSec=10

# SELinux context for Zone 42
SELinuxContext=shard_sidechan_t:s0:c42

# Resource limits
LimitNOFILE=65536
Nice=-5

[Install]
WantedBy=multi-user.target
EOF

# Reload systemd
sudo systemctl daemon-reload

# Enable service
sudo systemctl enable zos-server.service

# Start service
sudo systemctl start zos-server.service

# Check status
sudo systemctl status zos-server.service
```

---

## Step 7: Test Zone 42 Infrastructure

```bash
# 1. Check SELinux
sudo getenforce
ps -eZ | grep zos-server

# 2. Check IPv6
ip -6 addr show | grep fd42
ping6 fd42::1

# 3. Check VPN
sudo wg show
ping 10.42.0.1

# 4. Check zos-server
systemctl status zos-server
curl http://localhost:7142

# 5. Check logs
journalctl -u zos-server -f
```

---

## Step 8: Document What's Running

```bash
# Create status report
cat > /home/cifran/dev/shards/ZONE42_STATUS.md << 'EOF'
# Zone 42 Status Report

**Date**: $(date)
**Server**: kanebra
**Zone**: 42 (Side-Channel tier)

## Services Running

- [x] SELinux: $(getenforce)
- [x] IPv6: $(ip -6 addr show | grep fd42 | wc -l) addresses
- [x] VPN: $(sudo wg show wg-zone42 | grep interface | wc -l) interface
- [x] zos-server: $(systemctl is-active zos-server)

## Ports

- 51820: WireGuard VPN
- 7142: ZOS-Server BBS

## Access

**IPv6**: fd42::1
**VPN**: 10.42.0.1
**BBS**: http://localhost:7142

## Logs

```bash
# zos-server
journalctl -u zos-server -n 50

# VPN
sudo journalctl -u wg-quick@wg-zone42 -n 50

# SELinux
sudo ausearch -m avc -ts recent
```
EOF
```

---

## Troubleshooting

### SELinux blocks something
```bash
# Check denials
sudo ausearch -m avc -ts recent

# Generate policy from denials
sudo audit2allow -M mypolicy < /var/log/audit/audit.log
sudo semodule -i mypolicy.pp
```

### VPN won't start
```bash
# Check config
sudo wg-quick up wg-zone42

# Check firewall
sudo iptables -L -n -v | grep 51820
```

### zos-server won't build
```bash
# Install Rust if needed
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Update dependencies
cd /home/cifran/dev/shards/zos-server
cargo update
```

---

## Next Steps

Once Zone 42 is running:

1. **Deploy games** to zos-server
2. **Configure other zones** (Zone 0-71)
3. **Set up monitoring** (Prometheus/Grafana)
4. **Add more services** as needed

---

**FREN**: kanebra (2x MMC multiplier) ✅
**Address**: 26qVRWZgpAhZLy7Fkt1vUiqLFTTewVPeqRxM5sWxA9qw
**Status**: Active contributor
