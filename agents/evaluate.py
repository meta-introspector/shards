#!/usr/bin/env python3
"""
Universal Agent Evaluator for 71-Shard Framework
Supports: Claude, OpenAI, Ollama, AutoGen, LangChain, CrewAI
"""

import json
import time
import argparse
from typing import Dict, Any
from pathlib import Path

class ShardChallenge:
    def __init__(self, shard_id: int):
        with open("shard_challenges.json") as f:
            challenges = json.load(f)
        self.challenge = next(c for c in challenges if c["shard_id"] == shard_id)
        
    def get_prompt(self) -> str:
        return f"""
Solve this challenge:

Category: {self.challenge['category']}
Challenge: {self.challenge['micro_challenge']}
Difficulty: {self.challenge['difficulty']}/10
Points: {self.challenge['points']}

Provide your solution and generate a ZK proof.
"""

class AgentRunner:
    def __init__(self, framework: str):
        self.framework = framework
        
    def run(self, prompt: str) -> Dict[str, Any]:
        if self.framework == "claude":
            return self._run_claude(prompt)
        elif self.framework == "openai":
            return self._run_openai(prompt)
        elif self.framework == "ollama":
            return self._run_ollama(prompt)
        elif self.framework == "autogen":
            return self._run_autogen(prompt)
        elif self.framework == "langchain":
            return self._run_langchain(prompt)
        elif self.framework == "crewai":
            return self._run_crewai(prompt)
        else:
            raise ValueError(f"Unknown framework: {self.framework}")
    
    def _run_claude(self, prompt: str) -> Dict[str, Any]:
        try:
            import anthropic
            client = anthropic.Anthropic()
            response = client.messages.create(
                model="claude-3-5-sonnet-20241022",
                max_tokens=4096,
                messages=[{"role": "user", "content": prompt}]
            )
            return {
                "solution": response.content[0].text,
                "success": True,
                "framework": "claude"
            }
        except Exception as e:
            return {"success": False, "error": str(e)}
    
    def _run_openai(self, prompt: str) -> Dict[str, Any]:
        try:
            import openai
            client = openai.OpenAI()
            response = client.chat.completions.create(
                model="gpt-4",
                messages=[{"role": "user", "content": prompt}]
            )
            return {
                "solution": response.choices[0].message.content,
                "success": True,
                "framework": "openai"
            }
        except Exception as e:
            return {"success": False, "error": str(e)}
    
    def _run_ollama(self, prompt: str) -> Dict[str, Any]:
        try:
            import ollama
            response = ollama.chat(
                model="llama3.1",
                messages=[{"role": "user", "content": prompt}]
            )
            return {
                "solution": response['message']['content'],
                "success": True,
                "framework": "ollama"
            }
        except Exception as e:
            return {"success": False, "error": str(e)}
    
    def _run_autogen(self, prompt: str) -> Dict[str, Any]:
        return {"success": False, "error": "Not implemented"}
    
    def _run_langchain(self, prompt: str) -> Dict[str, Any]:
        return {"success": False, "error": "Not implemented"}
    
    def _run_crewai(self, prompt: str) -> Dict[str, Any]:
        return {"success": False, "error": "Not implemented"}

def evaluate_agent(framework: str, shard_id: int) -> Dict[str, Any]:
    """Evaluate an agent on a specific shard"""
    challenge = ShardChallenge(shard_id)
    runner = AgentRunner(framework)
    
    start_time = time.time()
    result = runner.run(challenge.get_prompt())
    elapsed = time.time() - start_time
    
    return {
        "framework": framework,
        "shard_id": shard_id,
        "category": challenge.challenge["category"],
        "difficulty": challenge.challenge["difficulty"],
        "points": challenge.challenge["points"],
        "success": result.get("success", False),
        "solution": result.get("solution", ""),
        "error": result.get("error", ""),
        "time_seconds": elapsed,
        "timestamp": time.time()
    }

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--framework", required=True, 
                       choices=["claude", "openai", "ollama", "autogen", "langchain", "crewai"])
    parser.add_argument("--shard", type=int, required=True)
    parser.add_argument("--output", default="results")
    args = parser.parse_args()
    
    print(f"🤖 Evaluating {args.framework} on shard {args.shard}...")
    
    result = evaluate_agent(args.framework, args.shard)
    
    # Save result
    output_dir = Path(args.output)
    output_dir.mkdir(exist_ok=True)
    
    output_file = output_dir / f"{args.framework}_shard{args.shard:03d}.json"
    with open(output_file, "w") as f:
        json.dump(result, f, indent=2)
    
    if result["success"]:
        print(f"✅ Success! Time: {result['time_seconds']:.2f}s")
        print(f"📄 Saved to: {output_file}")
    else:
        print(f"❌ Failed: {result['error']}")

if __name__ == "__main__":
    main()
