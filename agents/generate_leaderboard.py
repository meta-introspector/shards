#!/usr/bin/env python3
"""
Generate leaderboard from agent evaluation results
"""

import json
from pathlib import Path
from collections import defaultdict
from typing import List, Dict

def load_results(results_dir: str = "results") -> List[Dict]:
    """Load all evaluation results"""
    results = []
    for file in Path(results_dir).glob("*.json"):
        with open(file) as f:
            results.append(json.load(f))
    return results

def calculate_scores(results: List[Dict]) -> Dict[str, Dict]:
    """Calculate scores per framework"""
    scores = defaultdict(lambda: {
        "total_points": 0,
        "shards_completed": 0,
        "total_time": 0,
        "success_rate": 0,
        "avg_difficulty": 0
    })
    
    framework_attempts = defaultdict(int)
    
    for r in results:
        fw = r["framework"]
        framework_attempts[fw] += 1
        
        if r["success"]:
            scores[fw]["total_points"] += r["points"]
            scores[fw]["shards_completed"] += 1
            scores[fw]["total_time"] += r["time_seconds"]
            scores[fw]["avg_difficulty"] += r["difficulty"]
    
    # Calculate averages
    for fw, data in scores.items():
        if data["shards_completed"] > 0:
            data["avg_difficulty"] /= data["shards_completed"]
            data["success_rate"] = data["shards_completed"] / framework_attempts[fw]
    
    return dict(scores)

def generate_leaderboard(scores: Dict[str, Dict]) -> str:
    """Generate markdown leaderboard"""
    sorted_scores = sorted(scores.items(), 
                          key=lambda x: x[1]["total_points"], 
                          reverse=True)
    
    md = "# 71-Shard Challenge Leaderboard\n\n"
    md += f"**Generated**: {Path('results').stat().st_mtime}\n\n"
    md += "## Overall Rankings\n\n"
    md += "| Rank | Framework | Points | Shards | Success Rate | Avg Time | Avg Difficulty |\n"
    md += "|------|-----------|--------|--------|--------------|----------|----------------|\n"
    
    for rank, (fw, data) in enumerate(sorted_scores, 1):
        md += f"| {rank} | {fw.title()} | {data['total_points']:,} | "
        md += f"{data['shards_completed']} | "
        md += f"{data['success_rate']:.1%} | "
        md += f"{data['total_time']/data['shards_completed']:.2f}s | "
        md += f"{data['avg_difficulty']:.1f}/10 |\n"
    
    return md

def generate_category_breakdown(results: List[Dict]) -> str:
    """Generate category performance breakdown"""
    categories = defaultdict(lambda: defaultdict(int))
    
    for r in results:
        if r["success"]:
            categories[r["category"]][r["framework"]] += 1
    
    md = "\n## Performance by Category\n\n"
    
    for cat in ["Cryptography", "Encryption", "Prompt Injection", 
                "Multi-Agent", "Reverse Engineering", "Economic Security", "Meta-Challenge"]:
        if cat in categories:
            md += f"\n### {cat}\n\n"
            md += "| Framework | Completed |\n"
            md += "|-----------|----------|\n"
            
            for fw, count in sorted(categories[cat].items(), 
                                   key=lambda x: x[1], reverse=True):
                md += f"| {fw.title()} | {count} |\n"
    
    return md

def main():
    print("📊 Generating leaderboard...")
    
    results = load_results()
    print(f"   Loaded {len(results)} results")
    
    scores = calculate_scores(results)
    
    leaderboard = generate_leaderboard(scores)
    leaderboard += generate_category_breakdown(results)
    
    with open("LEADERBOARD.md", "w") as f:
        f.write(leaderboard)
    
    print("✅ Leaderboard saved to LEADERBOARD.md")
    
    # Print to console
    print("\n" + leaderboard)

if __name__ == "__main__":
    main()
