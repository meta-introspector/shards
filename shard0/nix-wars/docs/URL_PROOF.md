# Nix-Wars: URL-Only Gameplay Proof

**Proof that the entire game can be played using only URL parameters**

## The Proof

Open: `url-only.html`

The game state is **entirely encoded in the URL hash**.

## Example URLs

### Genesis State
```
url-only.html#
```

### After Move 1 (Alpha → 42)
```
url-only.html#%7B%22round%22%3A1%2C%22ships%22%3A%7B%22alpha%22%3A%7B%22sector%22%3A42%2C%22credits%22%3A1000000%7D%2C%22beta%22%3A%7B%22sector%22%3A1%2C%22credits%22%3A1000000%7D%2C%22gamma%22%3A%7B%22sector%22%3A2%2C%22credits%22%3A1000000%7D%7D%2C%22moves%22%3A%5B%7B%22player%22%3A%22alpha%22%2C%22from%22%3A0%2C%22to%22%3A42%7D%5D%7D
```

Decoded:
```json
{
  "round": 1,
  "ships": {
    "alpha": {"sector": 42, "credits": 1000000},
    "beta": {"sector": 1, "credits": 1000000},
    "gamma": {"sector": 2, "credits": 1000000}
  },
  "moves": [
    {"player": "alpha", "from": 0, "to": 42}
  ]
}
```

## Properties Proven

### ✅ No Server Required
- Game state lives in URL
- No backend
- No database
- No API calls

### ✅ Shareable
- Copy URL
- Send via email
- Post on forum
- QR code
- UUCP sneakernet

### ✅ Reproducible
- Same URL = Same state
- Commitment hash computed client-side
- Deterministic

### ✅ Verifiable
- Anyone can decode URL
- Anyone can verify commitment
- Anyone can replay moves

### ✅ Air-Gapped Compatible
- Save URL to file
- Transport via USB
- Load in offline browser
- Continue playing

## How It Works

### 1. State Encoding
```javascript
const state = { round: 1, ships: {...}, moves: [...] };
const encoded = encodeURIComponent(JSON.stringify(state));
window.location.hash = encoded;
```

### 2. State Decoding
```javascript
const hash = window.location.hash.slice(1);
const state = JSON.parse(decodeURIComponent(hash));
```

### 3. Commitment
```javascript
function computeCommitment(state) {
  const str = JSON.stringify(state);
  // Hash computation
  return hash.toString(16);
}
```

## Use Cases

### 1. Forum-Based Gaming
```
Player 1 posts: url-only.html#<state1>
Player 2 replies: url-only.html#<state2>
Player 3 replies: url-only.html#<state3>
```

### 2. Email Gaming
```
Subject: Your move!
Body: Click here to continue: url-only.html#<state>
```

### 3. QR Code Gaming
```
Generate QR code from URL
Print on paper
Scan to continue game
```

### 4. Sneakernet Gaming
```
Save URL to text file
Copy to USB drive
Transport physically
Load on air-gapped machine
```

## Integration with Nix-Wars

### From Nix State to URL
```bash
cd states/state-4
STATE=$(cat result/state.json)
ENCODED=$(echo "$STATE" | jq -c | jq -sRr @uri)
echo "url-only.html#$ENCODED"
```

### From URL to Nix State
```bash
URL="url-only.html#%7B%22round%22%3A1..."
HASH="${URL#*#}"
STATE=$(echo "$HASH" | jq -Rr @uri | jq .)
echo "$STATE" > new-state.json
```

## Proof Complete

**Q.E.D.**: The game is playable using only URL parameters.

No server. No network. No database. Just URLs.

**The entire game state fits in a URL.** 🔗✨
