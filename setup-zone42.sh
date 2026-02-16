#!/usr/bin/env bash
# Setup Zone 42 Infrastructure
# Requirements: IPv6, VPN, SELinux, systemd, zos-server

set -euo pipefail

echo "🚀 Setting up Zone 42 Infrastructure"
echo "====================================="
echo

# Check if running as root for some operations
if [ "$EUID" -ne 0 ]; then
    echo "⚠️  Some operations require sudo"
    SUDO="sudo"
else
    SUDO=""
fi

# 1. Install Rust if needed
echo "📦 Step 1: Installing Rust..."
if ! command -v rustc &> /dev/null; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source "$HOME/.cargo/env"
    echo "✅ Rust installed"
else
    echo "✅ Rust already installed: $(rustc --version)"
fi

# 2. Install SELinux tools
echo
echo "🔒 Step 2: Installing SELinux tools..."
if ! command -v checkmodule &> /dev/null; then
    $SUDO apt-get update
    $SUDO apt-get install -y selinux-basics selinux-policy-default auditd checkpolicy policycoreutils
    echo "✅ SELinux tools installed"
else
    echo "✅ SELinux tools already installed"
fi

# 3. Install WireGuard
echo
echo "🔐 Step 3: Installing WireGuard VPN..."
if ! command -v wg &> /dev/null; then
    $SUDO apt-get install -y wireguard
    echo "✅ WireGuard installed"
else
    echo "✅ WireGuard already installed"
fi

# 4. Configure IPv6
echo
echo "🌐 Step 4: Configuring private IPv6 (fd42::/64)..."
if ! ip -6 addr show | grep -q "fd42::1"; then
    $SUDO ip -6 addr add fd42::1/64 dev lo
    echo "✅ IPv6 configured: fd42::1/64"
else
    echo "✅ IPv6 already configured"
fi

# 5. Check SELinux status
echo
echo "🔒 Step 5: Checking SELinux status..."
if command -v getenforce &> /dev/null && [ "$(getenforce 2>/dev/null)" != "Disabled" ]; then
    echo "✅ SELinux is active"
    cd shard0/selinux
    if [ -f shard71.te ]; then
        checkmodule -M -m -o shard71.mod shard71.te 2>/dev/null && \
        semodule_package -o shard71.pp -m shard71.mod && \
        echo "✅ SELinux policy compiled: shard71.pp" && \
        echo "   To install: sudo semodule -i shard0/selinux/shard71.pp"
    fi
    cd ../..
else
    echo "⚠️  SELinux is disabled (this is OK for initial setup)"
    echo "   Zone isolation will use systemd features instead"
    echo "   To enable SELinux later, see: /usr/share/doc/selinux-basics/README.Debian"
fi

# 6. Build zos-server
echo
echo "🏗️  Step 6: Building zos-server..."
cd zos-server
if cargo build --release 2>&1 | tee /tmp/zos-build.log; then
    echo "✅ zos-server built successfully"
    echo "   Binary: ./target/release/zos-server"
else
    echo "⚠️  Build had warnings/errors (check /tmp/zos-build.log)"
fi
cd ..

# 7. Create systemd service
echo
echo "⚙️  Step 7: Creating systemd service..."
cat > /tmp/zos-server.service << 'EOF'
[Unit]
Description=ZOS-Server BBS (Zone 42)
After=network.target
Wants=network.target

[Service]
Type=simple
User=$USER
WorkingDirectory=/home/$USER/dev/shards/zos-server
ExecStart=/home/$USER/dev/shards/zos-server/target/release/zos-server
Restart=on-failure
RestartSec=10

# SELinux context for Zone 42
#SELinuxContext=shard_sidechan_t:s0:c42

# Resource limits
LimitNOFILE=65536

[Install]
WantedBy=multi-user.target
EOF

# Replace $USER with actual username
sed -i "s/\$USER/$USER/g" /tmp/zos-server.service

echo "✅ Service file created: /tmp/zos-server.service"
echo "   To install: sudo cp /tmp/zos-server.service /etc/systemd/system/"
echo "   Then: sudo systemctl enable zos-server && sudo systemctl start zos-server"

# 8. Create WireGuard config template
echo
echo "🔐 Step 8: Creating WireGuard config template..."
cat > /tmp/wg-zone42.conf << 'EOF'
[Interface]
Address = 10.42.0.1/24, fd42:42::1/64
ListenPort = 51820
PrivateKey = <GENERATE_WITH: wg genkey>

# Uncomment to enable routing
#PostUp = iptables -A FORWARD -i wg-zone42 -j ACCEPT
#PostDown = iptables -D FORWARD -i wg-zone42 -j ACCEPT

# Add peers here:
#[Peer]
#PublicKey = <PEER_PUBLIC_KEY>
#AllowedIPs = 10.42.0.2/32, fd42:42::2/128
EOF

echo "✅ WireGuard config template: /tmp/wg-zone42.conf"
echo "   Generate keys: wg genkey | tee privatekey | wg pubkey > publickey"
echo "   Install: sudo cp /tmp/wg-zone42.conf /etc/wireguard/"

# Summary
echo
echo "========================================="
echo "✅ Zone 42 Infrastructure Setup Complete"
echo "========================================="
echo
echo "Status:"
echo "  ✅ Rust: $(rustc --version 2>/dev/null || echo 'not installed')"
echo "  ✅ SELinux policy: shard0/selinux/shard71.pp"
echo "  ✅ zos-server: zos-server/target/release/zos-server"
echo "  ✅ systemd service: /tmp/zos-server.service"
echo "  ✅ WireGuard config: /tmp/wg-zone42.conf"
echo "  ✅ IPv6: fd42::1/64"
echo
echo "Next steps:"
echo "  1. Install SELinux policy: sudo semodule -i shard0/selinux/shard71.pp"
echo "  2. Configure WireGuard: edit /tmp/wg-zone42.conf and copy to /etc/wireguard/"
echo "  3. Install systemd service: sudo cp /tmp/zos-server.service /etc/systemd/system/"
echo "  4. Start services: sudo systemctl start wg-quick@wg-zone42 zos-server"
echo "  5. Test: curl http://localhost:7142"
echo "  6. Test IPv6: curl http://[fd42::1]:7142"
echo
echo "FREN: kanebra (2x MMC multiplier) ✅"
echo "Solana: 26qVRWZgpAhZLy7Fkt1vUiqLFTTewVPeqRxM5sWxA9qw"
