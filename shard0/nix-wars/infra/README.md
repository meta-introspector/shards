# Nix-Wars Infrastructure: DNS/VPN/Nginx/SELinux

**Complete infrastructure setup for 71-zone distributed game**

## Architecture

```
Internet
    ↓
[Nginx] (reverse proxy, rate limiting)
    ↓
[WireGuard VPN] (10.71.0.0/16)
    ↓
[71 DNS Zones] (zone0-70.nixwars.local)
    ↓
[SELinux] (mandatory access control)
    ↓
[Game States] (/nix/store)
```

## Components

### 1. DNS (71 Zones)

**Zones**: `zone0.nixwars.local` through `zone70.nixwars.local`

**IP Range**: `10.71.0.0/16`

**Configuration**:
```
zone0.nixwars.local  → 10.71.0.0
zone1.nixwars.local  → 10.71.0.1
...
zone70.nixwars.local → 10.71.0.70
```

### 2. Nginx (Reverse Proxy)

**Features**:
- Rate limiting (10 req/s)
- Static file serving
- Proxy to 71 zones
- SELinux context enforcement

**Endpoints**:
- `/` - Static game files
- `/states/` - Read-only Nix store
- `/witnesses/` - zkPerf witnesses
- `/uucp/` - Denied (sneakernet only)

### 3. WireGuard VPN

**Network**: `10.71.0.0/16`

**Peers**: 71 zones (one per sector)

**Port**: 51820

**Features**:
- Encrypted tunnel
- Peer-to-peer
- NAT traversal

### 4. SELinux

**Policy**: `nixwars.te`

**Rules**:
- Allow nginx → Nix store (read-only)
- Allow nginx → game states
- Deny direct UUCP access

## Installation

### Build Infrastructure

```bash
cd infra
nix build
```

### Install

```bash
cd result
sudo ./install.sh
```

This will:
1. Configure DNS (bind9)
2. Setup Nginx
3. Start WireGuard VPN
4. Load SELinux policy

### Manual Setup

#### DNS
```bash
sudo cp dns/zones.conf /etc/bind/
sudo systemctl restart bind9
```

#### Nginx
```bash
sudo cp nginx/nixwars.conf /etc/nginx/sites-available/
sudo ln -s /etc/nginx/sites-available/nixwars.conf /etc/nginx/sites-enabled/
sudo nginx -t
sudo systemctl restart nginx
```

#### WireGuard
```bash
# Generate keys
wg genkey | tee private.key | wg pubkey > public.key

# Edit wg0.conf with your keys
sudo cp vpn/wg0.conf /etc/wireguard/
sudo systemctl enable wg-quick@wg0
sudo systemctl start wg-quick@wg0
```

#### SELinux
```bash
sudo checkmodule -M -m -o nixwars.mod selinux/nixwars.te
sudo semodule_package -o nixwars.pp -m nixwars.mod
sudo semodule -i nixwars.pp
```

## NixOS Integration

Add to `configuration.nix`:

```nix
{
  imports = [ ./nix-wars/infra ];
  
  services.nixwars = {
    enable = true;
    zones = 71;
    vpnNetwork = "10.71.0.0/16";
  };
}
```

## Testing

### DNS
```bash
dig @localhost zone42.nixwars.local
```

### Nginx
```bash
curl http://localhost/
curl http://zone42.nixwars.local/
```

### VPN
```bash
sudo wg show
ping 10.71.0.42
```

### SELinux
```bash
sudo semodule -l | grep nixwars
sudo ausearch -m avc -ts recent
```

## Security

### Rate Limiting
- 10 requests/second per IP
- Burst of 20 allowed
- Prevents DoS

### SELinux
- Mandatory access control
- Read-only Nix store
- No direct UUCP access

### VPN
- Encrypted WireGuard tunnel
- Peer authentication
- Network isolation

### Nginx
- Reverse proxy (hides backend)
- Header sanitization
- MIME type enforcement

## Topology

```
Zone 0  (10.71.0.0)   ←→ VPN ←→ Nginx ←→ Internet
Zone 1  (10.71.0.1)   ←→ VPN ←→ Nginx ←→ Internet
...
Zone 70 (10.71.0.70)  ←→ VPN ←→ Nginx ←→ Internet
```

## Monitoring

```bash
# Nginx logs
sudo tail -f /var/log/nginx/access.log

# VPN status
sudo wg show wg0

# DNS queries
sudo tail -f /var/log/bind/query.log

# SELinux denials
sudo ausearch -m avc -ts recent
```

## Scaling

### Add More Zones
```nix
# In flake.nix, change:
builtins.genList (x: x) 71  # to 142, 213, etc.
```

### Load Balancing
```nginx
upstream nixwars {
  server 10.71.0.0:8080;
  server 10.71.0.1:8080;
  # ...
}
```

### Geographic Distribution
```
US-East:  zone0-23.nixwars.local
US-West:  zone24-47.nixwars.local
EU:       zone48-70.nixwars.local
```

## Integration with Game

### DNS Resolution
```javascript
// In browser
fetch('http://zone42.nixwars.local/states/state-4')
  .then(r => r.json())
  .then(state => console.log(state));
```

### VPN Access
```bash
# Connect to VPN
sudo wg-quick up wg0

# Access zone directly
curl http://10.71.0.42:8080/
```

### Sneakernet Bypass
```bash
# UUCP doesn't use network
cp /var/spool/uucp/tradewars/alpha/out/*.txn /media/usb/
# Physical transport
cp /media/usb/*.txn /var/spool/uucp/tradewars/gateway/incoming/
```

**Complete infrastructure for distributed, secure, air-gapped gaming.** 🌐🔐
