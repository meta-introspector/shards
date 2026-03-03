# Connect Your Laptop to Zone 42 VPN

**Security note:** Do this yourself so private keys stay private!

---

## Info You Need

**Server Public Key:** `vwi3p25GTcHDpykpNmX3TuXyRyLdWgjSWd6RJxqCCDM=`
**Pi IP Address:** `192.168.0.170`

---

## On Your Pi (Server Side)

### Step 1: Generate Laptop Keys (ON LAPTOP, not Pi!)

**On your laptop terminal:**
```bash
# Install WireGuard first
# Ubuntu/Debian:
sudo apt install wireguard

# macOS:
brew install wireguard-tools

# Generate keys (DO THIS ON LAPTOP)
wg genkey | tee laptop-private.key | wg pubkey > laptop-public.key

# Show public key only (safe to share)
cat laptop-public.key
```

Copy the public key output.

### Step 2: Add Laptop as Peer (ON PI)

**On your Pi:**
```bash
# Edit WireGuard config
sudo nano /etc/wireguard/wg-zone42.conf

# Add at the end:
[Peer]
PublicKey = <PASTE_LAPTOP_PUBLIC_KEY_HERE>
AllowedIPs = 10.42.0.2/32, fd42:42::2/128

# Save and exit (Ctrl+X, Y, Enter)

# Restart VPN
sudo systemctl restart wg-quick@wg-zone42

# Verify peer was added
sudo wg show
```

---

## On Your Laptop (Client Side)

### Step 3: Create Client Config (ON LAPTOP)

**On your laptop:**
```bash
# Create config file
sudo nano /etc/wireguard/zone42.conf

# Paste this (fill in YOUR laptop private key):
[Interface]
Address = 10.42.0.2/24, fd42:42::2/64
PrivateKey = <PASTE_YOUR_LAPTOP_PRIVATE_KEY>
DNS = 1.1.1.1

[Peer]
PublicKey = vwi3p25GTcHDpykpNmX3TuXyRyLdWgjSWd6RJxqCCDM=
Endpoint = 192.168.0.170:51820
AllowedIPs = 10.42.0.0/24, fd42:42::0/64
PersistentKeepalive = 25

# Save and exit
```

### Step 4: Connect! (ON LAPTOP)

```bash
# Start VPN
sudo wg-quick up zone42

# Test connection
ping 10.42.0.1

# Access zos-server in your browser!
firefox http://10.42.0.1:7142
# or
google-chrome http://10.42.0.1:7142
```

### Stop VPN When Done

```bash
sudo wg-quick down zone42
```

---

## Troubleshooting

**Can't connect?**

Check Pi firewall:
```bash
# On Pi
sudo ufw status | grep 51820
```

Should show: `51820/udp ALLOW Anywhere`

**Still can't ping?**

Check VPN is running:
```bash
# On Pi
sudo wg show

# On Laptop
sudo wg show
```

Both should show the peer.

---

## Once Connected

**Open browser on laptop:**
- http://10.42.0.1:7142 - Zone 42 BBS
- http://10.42.0.1:7142/status - Server status
- http://10.42.0.1:7142/tape/test - Try plugin tapes

**You'll see the retro BBS interface in your browser!** 🎮

---

## Summary

1. **Laptop**: Generate keys → copy PUBLIC key
2. **Pi**: Add laptop public key to WireGuard config
3. **Laptop**: Create client config with YOUR private key
4. **Laptop**: Connect with `sudo wg-quick up zone42`
5. **Laptop**: Open browser to http://10.42.0.1:7142

**Private keys never leave your devices!** 🔐
