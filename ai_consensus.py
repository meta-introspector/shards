#!/usr/bin/env python3
"""
AI Consensus - Aggregate analysis from multiple free-tier AI services
"""

import json
from pathlib import Path
from collections import defaultdict

def load_analysis(filename):
    """Load AI analysis if exists"""
    path = Path(filename)
    if not path.exists():
        return None
    
    try:
        with open(path) as f:
            content = f.read()
            # Try to parse as JSON first
            try:
                return json.loads(content)
            except:
                # Return as text
                return {"text": content}
    except:
        return None

def extract_insights(analysis, source):
    """Extract key insights from AI analysis"""
    if not analysis:
        return []
    
    text = analysis.get("text", str(analysis))
    
    insights = []
    
    # Look for common patterns
    keywords = {
        "imbalance": "distribution",
        "optimize": "optimization",
        "group": "grouping",
        "error": "error",
        "warning": "warning",
        "suggest": "suggestion",
    }
    
    for keyword, category in keywords.items():
        if keyword in text.lower():
            insights.append({
                "source": source,
                "category": category,
                "confidence": 0.7,
                "text": text[:200]
            })
    
    return insights

def compute_consensus(analyses):
    """Compute consensus from multiple AI analyses"""
    all_insights = []
    
    for source, analysis in analyses.items():
        insights = extract_insights(analysis, source)
        all_insights.extend(insights)
    
    # Group by category
    by_category = defaultdict(list)
    for insight in all_insights:
        by_category[insight["category"]].append(insight)
    
    # Compute consensus
    consensus = {
        "timestamp": "2026-02-01T14:00:00Z",
        "sources": list(analyses.keys()),
        "total_insights": len(all_insights),
        "categories": {},
        "recommendations": []
    }
    
    for category, insights in by_category.items():
        consensus["categories"][category] = {
            "count": len(insights),
            "sources": list(set(i["source"] for i in insights)),
            "avg_confidence": sum(i["confidence"] for i in insights) / len(insights)
        }
    
    # Generate recommendations
    if "distribution" in by_category:
        consensus["recommendations"].append({
            "priority": "high",
            "action": "Review shard distribution balance",
            "reason": f"{len(by_category['distribution'])} AI sources flagged distribution issues"
        })
    
    if "optimization" in by_category:
        consensus["recommendations"].append({
            "priority": "medium",
            "action": "Apply suggested optimizations",
            "reason": f"{len(by_category['optimization'])} AI sources suggested improvements"
        })
    
    return consensus

def main():
    print("=== AI Consensus Analysis ===\n")
    
    # Load all AI analyses
    analyses = {
        "gemini": load_analysis("gemini_analysis.json"),
        "claude": load_analysis("claude_analysis.json"),
        "gpt": load_analysis("gpt_analysis.json"),
        "ollama": load_analysis("ollama_analysis.json"),
    }
    
    # Filter out None values
    analyses = {k: v for k, v in analyses.items() if v is not None}
    
    print(f"Loaded analyses from: {', '.join(analyses.keys())}")
    
    if not analyses:
        print("Warning: No AI analyses found")
        return
    
    # Compute consensus
    consensus = compute_consensus(analyses)
    
    # Save consensus
    with open("AI_ANALYSIS.json", "w") as f:
        json.dump(consensus, f, indent=2)
    
    print(f"\nConsensus computed from {len(analyses)} sources")
    print(f"Total insights: {consensus['total_insights']}")
    print(f"Categories: {', '.join(consensus['categories'].keys())}")
    print(f"Recommendations: {len(consensus['recommendations'])}")
    
    # Print recommendations
    if consensus["recommendations"]:
        print("\nRecommendations:")
        for rec in consensus["recommendations"]:
            print(f"  [{rec['priority'].upper()}] {rec['action']}")
            print(f"    Reason: {rec['reason']}")
    
    print("\nSaved to AI_ANALYSIS.json")

if __name__ == "__main__":
    main()
