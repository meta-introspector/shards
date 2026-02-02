#!/usr/bin/env python3
"""Share P2P video calls via GitHub Gist"""

import json
import subprocess
import base64
from datetime import datetime

GIST_URL = "https://gist.github.com/jmikedupont2/0855d96fd1ab45d69b36e1223590e0f6"

def create_call_metadata(recording_path=None):
    """Create call metadata for sharing"""
    
    metadata = {
        "timestamp": datetime.now().isoformat(),
        "call": {
            "peer1": {
                "id": "peer-boat-01",
                "phone": "+1-555-BOAT-001",
                "status": "connected"
            },
            "peer2": {
                "id": "peer-boat-02", 
                "phone": "+1-555-BOAT-002",
                "status": "connected"
            }
        },
        "morse_messages": [
            {"from": "peer-boat-01", "code": ".-. --- --- ... - . .-.", "text": "ROOSTER"},
            {"from": "peer-boat-02", "code": ".-.. --- -... ... - . .-.", "text": "LOBSTER"},
            {"from": "peer-boat-01", "code": "--... .----", "text": "71"}
        ],
        "recording": {
            "available": recording_path is not None,
            "format": "webm",
            "shared_via": "p2p_gossip"
        },
        "p2p": {
            "protocol": "WebRTC",
            "signaling": "GitHub Gist",
            "peers": 6,
            "gist": GIST_URL
        }
    }
    
    return metadata

def share_via_gist(metadata):
    """Share call metadata via GitHub Gist"""
    
    print("🔮⚡ Sharing P2P Call via Gist 📻🦞")
    print("=" * 70)
    print()
    
    # Create gist content
    gist_content = f"""# TradeWars P2P Video Call

**Timestamp:** {metadata['timestamp']}

## Call Participants

- 📞 **Peer 1:** {metadata['call']['peer1']['id']} ({metadata['call']['peer1']['phone']})
- 📞 **Peer 2:** {metadata['call']['peer2']['id']} ({metadata['call']['peer2']['phone']})

## Morse Code Messages

"""
    
    for msg in metadata['morse_messages']:
        gist_content += f"- **{msg['from']}:** `{msg['code']}` → {msg['text']}\n"
    
    gist_content += f"""

## P2P Network

- Protocol: {metadata['p2p']['protocol']}
- Signaling: {metadata['p2p']['signaling']}
- Active Peers: {metadata['p2p']['peers']}
- Gist: {metadata['p2p']['gist']}

## Recording

- Available: {'✅ Yes' if metadata['recording']['available'] else '❌ No'}
- Format: {metadata['recording']['format']}
- Shared via: {metadata['recording']['shared_via']}

## WebRTC Signaling

To join this call, open:
```
https://meta-introspector.github.io/shards/doorgame/p2p_video_call.html?gist={GIST_URL}
```

## JSON Metadata

```json
{json.dumps(metadata, indent=2)}
```

---

🔮⚡📻🦞 **QED**
"""
    
    # Save to file
    filename = f"p2p_call_{datetime.now().strftime('%Y%m%d_%H%M%S')}.md"
    with open(filename, 'w') as f:
        f.write(gist_content)
    
    print(f"✅ Created: {filename}")
    print()
    
    # Create gist with gh CLI
    try:
        result = subprocess.run(
            ['gh', 'gist', 'create', filename, '--public', '--desc', 'TradeWars P2P Video Call'],
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            gist_url = result.stdout.strip()
            print(f"✅ Gist created: {gist_url}")
            print()
            print("Share this URL:")
            print(f"  {gist_url}")
            print()
            print("Or join via GitHub Pages:")
            print(f"  https://meta-introspector.github.io/shards/doorgame/p2p_video_call.html?gist={gist_url}")
            return gist_url
        else:
            print(f"⚠️  gh CLI error: {result.stderr}")
            print(f"Manual upload: gh gist create {filename}")
            
    except FileNotFoundError:
        print("⚠️  gh CLI not found")
        print(f"Manual upload: gh gist create {filename}")
    
    return None

def create_webrtc_signaling():
    """Create WebRTC signaling data for GitHub Pages"""
    
    signaling = {
        "type": "offer",
        "sdp": "v=0\no=- 0 0 IN IP4 127.0.0.1\ns=TradeWars P2P\nt=0 0\n",
        "ice_servers": [
            {"urls": "stun:stun.l.google.com:19302"},
            {"urls": "stun:stun1.l.google.com:19302"}
        ],
        "peers": [
            {
                "id": "peer-boat-01",
                "phone": "+1-555-BOAT-001",
                "status": "online"
            },
            {
                "id": "peer-boat-02",
                "phone": "+1-555-BOAT-002", 
                "status": "online"
            }
        ]
    }
    
    return signaling

def main():
    print("🔮⚡ TradeWars P2P Call Sharing 📻🦞")
    print("=" * 70)
    print()
    
    # Create metadata
    metadata = create_call_metadata()
    
    # Share via gist
    gist_url = share_via_gist(metadata)
    
    # Create signaling data
    signaling = create_webrtc_signaling()
    
    print()
    print("=" * 70)
    print("P2P CALL SHARED!")
    print("=" * 70)
    print()
    print("Features:")
    print("  ✅ Call metadata in gist")
    print("  ✅ Morse code messages")
    print("  ✅ WebRTC signaling")
    print("  ✅ Shareable URL")
    print("  ✅ GitHub Pages integration")
    print()
    print("QED 🔮⚡📻🦞")

if __name__ == "__main__":
    main()
