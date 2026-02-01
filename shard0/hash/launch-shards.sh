#!/usr/bin/env bash
# Launch 71 shards with CPU affinity and SELinux zones

set -euo pipefail

BINARY="./target/release/ingest"
DATA_DIR="./shard0/data/parquet"

echo "Launching 71 shards with compute partitioning and SELinux zones..."

for shard in {0..70}; do
    # Get CPU affinity
    case $shard in
        [0-9]|1[0-9]|2[0-2])  # Shards 0-22: single core
            CPUS=$shard
            ;;
        2[3-9]|3[0-9]|4[0-5])  # Shards 23-45: dual core
            base=$(( (shard - 23) * 2 ))
            core1=$(( base % 23 ))
            core2=$(( (base + 1) % 23 ))
            CPUS="$core1,$core2"
            ;;
        4[6-9]|5[0-7])  # Shards 46-57: quad core
            base=$(( (shard - 46) * 4 ))
            CPUS=$(seq -s, $base $((base + 3)) | sed 's/[0-9]\+/&%23/g' | bc | tr '\n' ',' | sed 's/,$//')
            ;;
        *)  # Shards 58-70: all cores
            CPUS="0-22"
            ;;
    esac

    # Get SELinux zone
    if [ $shard -le 9 ]; then
        ZONE="shard_stat_t"
        CAT="c$((shard + 2))"
    elif [ $shard -le 25 ]; then
        ZONE="shard_diff_t"
        CAT="c$((shard + 2))"
    elif [ $shard -le 31 ]; then
        ZONE="shard_tmto_t"
        CAT="c$((shard + 2))"
    elif [ $shard -le 39 ]; then
        ZONE="shard_attack_t"
        CAT="c$((shard + 2))"
    elif [ $shard -le 49 ]; then
        ZONE="shard_sidechan_t"
        CAT="c$((shard + 2))"
    elif [ $shard -le 56 ]; then
        ZONE="shard_algebra_t"
        CAT="c$((shard + 2))"
    elif [ $shard -le 65 ]; then
        ZONE="shard_proto_t"
        CAT="c$((shard + 2))"
    else
        ZONE="shard_coord_t"
        CAT="c$((shard + 2))"
    fi

    echo "Shard $shard -> CPUs $CPUS, Zone $ZONE:s0:$CAT"
    
    # Launch with SELinux context if available
    if command -v runcon &> /dev/null; then
        runcon -t "$ZONE" -l "s0:$CAT" taskset -c "$CPUS" "$BINARY" --shard "$shard" &
    else
        taskset -c "$CPUS" "$BINARY" --shard "$shard" &
    fi
done

wait
echo "All 71 shards completed"
