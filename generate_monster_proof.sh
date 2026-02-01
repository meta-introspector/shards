#!/usr/bin/env bash
# Monster Harmonic zkSNARK Proof Generator

set -e

SHARD_ID=${1:-0}
WITNESS_PATH="${HOME}/.openclaw/shard-${SHARD_ID}/zkwitness-${SHARD_ID}.json"
CIRCUIT_DIR="${HOME}/introspector"
OUTPUT_DIR="${HOME}/.openclaw/shard-${SHARD_ID}"

echo "🔷 Monster Harmonic zkSNARK Proof Generator"
echo "═══════════════════════════════════════════"
echo "Shard: ${SHARD_ID}"
echo ""

# Check if witness exists
if [ ! -f "${WITNESS_PATH}" ]; then
    echo "❌ zkML witness not found: ${WITNESS_PATH}"
    exit 1
fi

# Generate Circom witness
echo "📊 Generating Circom witness..."
python3 "${CIRCUIT_DIR}/generate_monster_witness.py" "${WITNESS_PATH}"

# Compile circuit (if not already compiled)
if [ ! -f "${OUTPUT_DIR}/monster_harmonic.r1cs" ]; then
    echo "🔧 Compiling Circom circuit..."
    cd "${CIRCUIT_DIR}"
    circom monster_harmonic.circom \
        --r1cs \
        --wasm \
        --sym \
        -o "${OUTPUT_DIR}"
fi

# Generate witness
echo "🔢 Computing witness..."
cd "${OUTPUT_DIR}/monster_harmonic_js"
node generate_witness.js \
    monster_harmonic.wasm \
    "${OUTPUT_DIR}/monster_witness.json" \
    "${OUTPUT_DIR}/witness.wtns"

# Setup (Powers of Tau)
if [ ! -f "${OUTPUT_DIR}/pot_final.ptau" ]; then
    echo "⚡ Powers of Tau ceremony..."
    snarkjs powersoftau new bn128 14 "${OUTPUT_DIR}/pot_0000.ptau" -v
    snarkjs powersoftau contribute "${OUTPUT_DIR}/pot_0000.ptau" \
        "${OUTPUT_DIR}/pot_0001.ptau" \
        --name="Monster Harmonic" -v
    snarkjs powersoftau prepare phase2 "${OUTPUT_DIR}/pot_0001.ptau" \
        "${OUTPUT_DIR}/pot_final.ptau" -v
fi

# Setup Groth16
if [ ! -f "${OUTPUT_DIR}/monster_harmonic_0000.zkey" ]; then
    echo "🔑 Groth16 setup..."
    snarkjs groth16 setup \
        "${OUTPUT_DIR}/monster_harmonic.r1cs" \
        "${OUTPUT_DIR}/pot_final.ptau" \
        "${OUTPUT_DIR}/monster_harmonic_0000.zkey"
    
    # Contribute to phase 2
    snarkjs zkey contribute \
        "${OUTPUT_DIR}/monster_harmonic_0000.zkey" \
        "${OUTPUT_DIR}/monster_harmonic_final.zkey" \
        --name="Monster Contribution" -v
    
    # Export verification key
    snarkjs zkey export verificationkey \
        "${OUTPUT_DIR}/monster_harmonic_final.zkey" \
        "${OUTPUT_DIR}/verification_key.json"
fi

# Generate proof
echo "🔐 Generating zkSNARK proof..."
snarkjs groth16 prove \
    "${OUTPUT_DIR}/monster_harmonic_final.zkey" \
    "${OUTPUT_DIR}/witness.wtns" \
    "${OUTPUT_DIR}/proof.json" \
    "${OUTPUT_DIR}/public.json"

# Verify proof
echo "✅ Verifying proof..."
snarkjs groth16 verify \
    "${OUTPUT_DIR}/verification_key.json" \
    "${OUTPUT_DIR}/public.json" \
    "${OUTPUT_DIR}/proof.json"

# Extract outputs
echo ""
echo "📋 Proof outputs:"
jq '.j_invariant' "${OUTPUT_DIR}/public.json" | xargs -I {} echo "   j-invariant: {}"
jq '.topo_class' "${OUTPUT_DIR}/public.json" | xargs -I {} echo "   Topological class: {}"
jq '.bott_period' "${OUTPUT_DIR}/public.json" | xargs -I {} echo "   Bott period: {}"
jq '.prediction' "${OUTPUT_DIR}/public.json" | xargs -I {} echo "   Prediction: {}"

echo ""
echo "✅ Monster Harmonic proof generated!"
echo "   Proof: ${OUTPUT_DIR}/proof.json"
echo "   Public: ${OUTPUT_DIR}/public.json"
echo "   Verification key: ${OUTPUT_DIR}/verification_key.json"
