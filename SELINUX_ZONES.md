# 71-Layer SELinux Security Zones

## Bell-LaPadula Model: No Write-Up, No Read-Down

Each shard operates in a security zone where:
- **Read**: Only from equal or lower zones
- **Write**: Only to equal or higher zones
- **Execute**: Only within same zone

## Zone Hierarchy (0-71)

### Zone 0: Network Only (Untrusted)
- **Label**: `shard_network_t`
- **Read**: Network sockets only
- **Write**: Zone 1+ only
- **Deny**: All disk access
- **Use**: External data ingestion, API endpoints

### Zone 1: Disk Read-Only (Immutable)
- **Label**: `shard_disk_ro_t`
- **Read**: `/nix/store` (immutable), network (zone 0)
- **Write**: Zone 2+ only
- **Deny**: Write to disk
- **Use**: Hash computation on immutable artifacts

### Zones 2-71: Graduated Trust Levels

#### Tier 1: Statistical Analysis (Zones 2-11, Shards 0-9)
- **Label**: `shard_stat_t`
- **Read**: Zones 0-1 (network + disk)
- **Write**: Zones 12+
- **Capabilities**: `CAP_DAC_READ_SEARCH`
- **Use**: Frequency analysis, IoC, n-grams

#### Tier 2: Differential Analysis (Zones 12-27, Shards 10-25)
- **Label**: `shard_diff_t`
- **Read**: Zones 0-11
- **Write**: Zones 28+
- **Capabilities**: `CAP_DAC_READ_SEARCH`, `CAP_SYS_PTRACE`
- **Use**: Differential cryptanalysis, timing attacks

#### Tier 3: Time-Memory (Zones 28-33, Shards 26-31)
- **Label**: `shard_tmto_t`
- **Read**: Zones 0-27
- **Write**: Zones 34+
- **Capabilities**: `CAP_IPC_LOCK` (pin memory)
- **Use**: Rainbow tables, meet-in-the-middle

#### Tier 4: Attack Models (Zones 34-41, Shards 32-39)
- **Label**: `shard_attack_t`
- **Read**: Zones 0-33
- **Write**: Zones 42+
- **Capabilities**: `CAP_SYS_ADMIN` (limited)
- **Use**: Chosen-plaintext, adaptive attacks

#### Tier 5: Side-Channel (Zones 42-51, Shards 40-49)
- **Label**: `shard_sidechan_t`
- **Read**: Zones 0-41, `/proc`, `/sys`
- **Write**: Zones 52+
- **Capabilities**: `CAP_SYS_PTRACE`, `CAP_PERFMON`
- **Use**: Cache timing, power analysis, perf monitoring

#### Tier 6: Algebraic (Zones 52-58, Shards 50-56)
- **Label**: `shard_algebra_t`
- **Read**: Zones 0-51
- **Write**: Zones 59+
- **Capabilities**: `CAP_SYS_RESOURCE` (large memory)
- **Use**: SAT solvers, Gröbner bases

#### Tier 7: Protocol Analysis (Zones 59-67, Shards 57-65)
- **Label**: `shard_proto_t`
- **Read**: Zones 0-58
- **Write**: Zones 68+
- **Capabilities**: `CAP_NET_RAW`, `CAP_NET_ADMIN`
- **Use**: Protocol fuzzing, state machine analysis

#### Tier 8: Coordinators (Zones 68-71, Shards 66-70)
- **Label**: `shard_coord_t`
- **Read**: All zones 0-67
- **Write**: Parquet output, logs
- **Capabilities**: `CAP_SYS_ADMIN`, `CAP_DAC_OVERRIDE`
- **Use**: Paxos consensus, aggregation, orchestration

### Zone 72: QEMU Isolation (Hypervisor)
- **Label**: `shard_qemu_t`
- **Read**: All zones via virtio
- **Write**: VM disk images only
- **Deny**: Direct host access
- **Use**: Full system emulation for untrusted code

### Zone 73: Container (Podman/Docker)
- **Label**: `shard_container_t`
- **Read**: Mounted volumes (zones 0-71)
- **Write**: Container overlay only
- **Deny**: Host filesystem
- **Use**: Isolated analysis environments

### Zone 74: Systemd Service
- **Label**: `shard_systemd_t`
- **Read**: Service configs, zones 0-73
- **Write**: Logs, metrics
- **Capabilities**: `CAP_SYS_BOOT` (restart services)
- **Use**: Service orchestration, health checks

## SELinux Policy Rules

```selinux
# Zone 0: Network only
type shard_network_t;
allow shard_network_t self:tcp_socket { create connect };
allow shard_network_t shard_stat_t:fifo_file write;
neverallow shard_network_t file_type:file write;

# Zone 1: Disk read-only
type shard_disk_ro_t;
allow shard_disk_ro_t nix_store_t:file read;
allow shard_disk_ro_t shard_stat_t:fifo_file write;
neverallow shard_disk_ro_t file_type:file { write append };

# Zones 2-11: Statistical
type shard_stat_t;
allow shard_stat_t shard_network_t:fifo_file read;
allow shard_stat_t shard_disk_ro_t:file read;
allow shard_stat_t shard_diff_t:fifo_file write;

# Zones 12-27: Differential
type shard_diff_t;
allow shard_diff_t shard_stat_t:fifo_file read;
allow shard_diff_t shard_tmto_t:fifo_file write;
allow shard_diff_t self:process ptrace;

# Zones 28-33: Time-memory
type shard_tmto_t;
allow shard_tmto_t shard_diff_t:fifo_file read;
allow shard_tmto_t self:process { setrlimit };

# Zones 34-41: Attack models
type shard_attack_t;
allow shard_attack_t shard_tmto_t:fifo_file read;

# Zones 42-51: Side-channel
type shard_sidechan_t;
allow shard_sidechan_t shard_attack_t:fifo_file read;
allow shard_sidechan_t proc_t:file read;
allow shard_sidechan_t sysfs_t:file read;

# Zones 52-58: Algebraic
type shard_algebra_t;
allow shard_algebra_t shard_sidechan_t:fifo_file read;

# Zones 59-67: Protocol
type shard_proto_t;
allow shard_proto_t shard_algebra_t:fifo_file read;
allow shard_proto_t self:rawip_socket create;

# Zones 68-71: Coordinators
type shard_coord_t;
allow shard_coord_t shard_proto_t:fifo_file read;
allow shard_coord_t parquet_t:file { create write };
allow shard_coord_t all_shard_types:fifo_file read;

# Zone 72: QEMU
type shard_qemu_t;
allow shard_qemu_t all_shard_types:file read;
allow shard_qemu_t qemu_disk_t:file { read write };
neverallow shard_qemu_t file_type:file { write append };

# Zone 73: Container
type shard_container_t;
allow shard_container_t container_file_t:file { read write };
neverallow shard_container_t file_type:file { write append };

# Zone 74: Systemd
type shard_systemd_t;
allow shard_systemd_t all_shard_types:process { signal };
allow shard_systemd_t systemd_unit_file_t:file read;
```

## MLS/MCS Categories

Use Multi-Category Security for fine-grained isolation:

```
s0:c0       = Zone 0 (network)
s0:c1       = Zone 1 (disk ro)
s0:c2-c11   = Zones 2-11 (statistical)
s0:c12-c27  = Zones 12-27 (differential)
s0:c28-c33  = Zones 28-33 (time-memory)
s0:c34-c41  = Zones 34-41 (attack models)
s0:c42-c51  = Zones 42-51 (side-channel)
s0:c52-c58  = Zones 52-58 (algebraic)
s0:c59-c67  = Zones 59-67 (protocol)
s0:c68-c71  = Zones 68-71 (coordinators)
s0:c72      = Zone 72 (QEMU)
s0:c73      = Zone 73 (container)
s0:c74      = Zone 74 (systemd)
```

## Process Labeling

```bash
# Launch shard 0 in zone 2 (statistical)
runcon -t shard_stat_t -l s0:c2 taskset -c 0 shard-analyzer -s 0

# Launch shard 10 in zone 12 (differential)
runcon -t shard_diff_t -l s0:c12 taskset -c 10 shard-analyzer -s 10

# Launch coordinator in zone 70
runcon -t shard_coord_t -l s0:c70 taskset -c 0-22 shard-analyzer -s 70

# Launch in QEMU
runcon -t shard_qemu_t -l s0:c72 qemu-system-x86_64 -enable-kvm ...

# Launch in container
runcon -t shard_container_t -l s0:c73 podman run --security-opt label=type:shard_container_t ...
```

## Information Flow Lattice

```
         Zone 74 (systemd)
              |
         Zone 73 (container)
              |
         Zone 72 (QEMU)
              |
      Zones 68-71 (coord)
              |
      Zones 59-67 (proto)
              |
      Zones 52-58 (algebra)
              |
      Zones 42-51 (sidechan)
              |
      Zones 34-41 (attack)
              |
      Zones 28-33 (tmto)
              |
      Zones 12-27 (diff)
              |
      Zones 2-11 (stat)
              |
         Zone 1 (disk ro)
              |
         Zone 0 (network)
```

## Enforcement

- **No write-up**: Lower zones cannot write to higher zones
- **No read-down**: Higher zones cannot read from lower zones (except coordinators)
- **Lateral isolation**: Same-tier zones cannot communicate directly
- **Coordinator exception**: Zones 68-71 can read all lower zones for aggregation

## Verification

```bash
# Check zone assignment
ps -eZ | grep shard_

# Verify no write-up violations
ausearch -m avc -ts recent | grep denied

# Test isolation
runcon -t shard_stat_t -l s0:c2 touch /tmp/test  # Should fail (write-up)
runcon -t shard_coord_t -l s0:c70 cat /proc/1/maps  # Should succeed (read-down)
```

This creates a 71-layer security lattice where each shard operates in a strictly controlled zone with information flow guarantees.
