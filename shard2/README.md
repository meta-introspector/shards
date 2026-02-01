# Shard 2: Performance Analysis

## Purpose
Dedicated to performance profiling and register-level analysis of pipelight builds.

## Data Collection

### perf record
- All CPU registers (AX, BX, CX, DX, SI, DI, BP, SP, IP, FLAGS, R8-R15)
- DWARF call graphs
- CPU sampling
- User-space only

### Outputs
- `pipelight-build.perf.data` - Raw perf data
- `pipelight-build.report.txt` - Human-readable report
- `pipelight-build.script.txt` - Event script
- `pipelight-build.regs.txt` - Register samples

## Usage
```bash
cd shard0/hash
./perf-record.sh
```
