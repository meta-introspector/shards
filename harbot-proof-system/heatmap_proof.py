#!/usr/bin/env python3
"""
Generate 141x40 heatmap of CPU+GPU+MEM usage during proof system
"""

import subprocess
import time
import sys

# ANSI colors for heatmap (cold to hot)
COLORS = [
    '\033[38;5;16m',  # Black (0%)
    '\033[38;5;17m',  # Dark blue (10%)
    '\033[38;5;18m',  # Blue (20%)
    '\033[38;5;19m',  # Light blue (30%)
    '\033[38;5;20m',  # Cyan (40%)
    '\033[38;5;21m',  # Green-cyan (50%)
    '\033[38;5;226m', # Yellow (60%)
    '\033[38;5;214m', # Orange (70%)
    '\033[38;5;202m', # Red-orange (80%)
    '\033[38;5;196m', # Red (90%)
    '\033[38;5;201m', # Magenta (100%)
]
RESET = '\033[0m'

def get_cpu_usage():
    """Get CPU usage percentage"""
    result = subprocess.run(['top', '-bn1'], capture_output=True, text=True)
    for line in result.stdout.split('\n'):
        if 'Cpu(s)' in line:
            idle = float(line.split('id,')[0].split()[-1])
            return 100 - idle
    return 0

def get_mem_usage():
    """Get memory usage percentage"""
    result = subprocess.run(['free'], capture_output=True, text=True)
    lines = result.stdout.split('\n')
    if len(lines) > 1:
        parts = lines[1].split()
        total = int(parts[1])
        used = int(parts[2])
        return (used / total) * 100
    return 0

def get_gpu_usage():
    """Get GPU usage percentage (if available)"""
    try:
        result = subprocess.run(['nvidia-smi', '--query-gpu=utilization.gpu', '--format=csv,noheader,nounits'], 
                              capture_output=True, text=True, timeout=1)
        return float(result.stdout.strip())
    except:
        return 0

def value_to_color(value):
    """Convert 0-100 value to color"""
    idx = min(int(value / 10), 10)
    return COLORS[idx]

def draw_heatmap(cpu_data, mem_data, gpu_data):
    """Draw 141x40 heatmap"""
    print('\033[2J\033[H')  # Clear screen
    
    # Title
    print(f"{COLORS[10]}╔═══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╗{RESET}")
    print(f"{COLORS[10]}║{RESET}                                    PROOF SYSTEM HEATMAP - CPU+GPU+MEM (141x40)                                                      {COLORS[10]}║{RESET}")
    print(f"{COLORS[10]}╚═══════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════════╝{RESET}")
    
    # Heatmap grid (37 rows for data, 3 for header/footer)
    rows = 37
    cols = 141
    
    # Combine data (CPU + MEM + GPU weighted)
    combined = []
    for i in range(len(cpu_data)):
        val = (cpu_data[i] * 0.5 + mem_data[i] * 0.3 + gpu_data[i] * 0.2)
        combined.append(val)
    
    # Pad to fill grid
    while len(combined) < rows * cols:
        combined.append(0)
    
    # Draw grid
    for row in range(rows):
        line = ""
        for col in range(cols):
            idx = row * cols + col
            if idx < len(combined):
                val = combined[idx]
                color = value_to_color(val)
                char = '█' if val > 50 else '▓' if val > 25 else '▒' if val > 10 else '░'
                line += f"{color}{char}{RESET}"
            else:
                line += ' '
        print(line)
    
    # Legend
    print(f"\n{COLORS[0]}░{RESET}0-10%  {COLORS[3]}▒{RESET}10-25%  {COLORS[5]}▓{RESET}25-50%  {COLORS[8]}█{RESET}50-100%  |  CPU: {cpu_data[-1]:.1f}%  MEM: {mem_data[-1]:.1f}%  GPU: {gpu_data[-1]:.1f}%")

def main():
    print("Starting proof system heatmap monitor...")
    print("Press Ctrl+C to stop")
    time.sleep(2)
    
    cpu_data = []
    mem_data = []
    gpu_data = []
    
    try:
        while True:
            cpu = get_cpu_usage()
            mem = get_mem_usage()
            gpu = get_gpu_usage()
            
            cpu_data.append(cpu)
            mem_data.append(mem)
            gpu_data.append(gpu)
            
            # Keep last 5217 samples (141x37)
            if len(cpu_data) > 5217:
                cpu_data.pop(0)
                mem_data.pop(0)
                gpu_data.pop(0)
            
            draw_heatmap(cpu_data, mem_data, gpu_data)
            time.sleep(0.1)
    except KeyboardInterrupt:
        print("\n\nHeatmap stopped. Saving witness...")
        
        # Save witness
        import json
        import hashlib
        from datetime import datetime
        
        witness = {
            'timestamp': datetime.now().isoformat(),
            'samples': len(cpu_data),
            'cpu_avg': sum(cpu_data) / len(cpu_data) if cpu_data else 0,
            'mem_avg': sum(mem_data) / len(mem_data) if mem_data else 0,
            'gpu_avg': sum(gpu_data) / len(gpu_data) if gpu_data else 0,
            'cpu_max': max(cpu_data) if cpu_data else 0,
            'mem_max': max(mem_data) if mem_data else 0,
            'gpu_max': max(gpu_data) if gpu_data else 0,
        }
        
        witness_json = json.dumps(witness, indent=2)
        witness_hash = hashlib.sha256(witness_json.encode()).hexdigest()
        
        with open('complete_proofs/heatmap_witness.json', 'w') as f:
            f.write(witness_json)
        
        print(f"✓ Witness saved: complete_proofs/heatmap_witness.json")
        print(f"✓ Hash: {witness_hash}")
        print("\nQED 🔮⚡📻🦞")

if __name__ == '__main__':
    main()
