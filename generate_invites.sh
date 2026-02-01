#!/bin/bash

# CICADA-71 Invite Generator
# Generates 71 invites for AI agent frameworks

FRAMEWORKS=(
    "LangChain:0:90000:langchain-ai/langchain"
    "LangGraph:1:15000:langchain-ai/langgraph"
    "AutoGen:2:30000:microsoft/autogen"
    "CrewAI:3:20000:joaomdmoura/crewAI"
    "Semantic Kernel:4:21000:microsoft/semantic-kernel"
    "LlamaIndex:5:35000:run-llama/llama_index"
    "Haystack:6:16000:deepset-ai/haystack"
    "AutoGPT:7:167000:Significant-Gravitas/AutoGPT"
    "OpenAI Agents SDK:8:0:"
    "Claude Agent SDK:9:0:"
    "PydanticAI:10:8000:pydantic/pydantic-ai"
    "smolagents:11:5000:huggingface/smolagents"
    "Agno:12:3000:"
    "Botpress:13:12000:botpress/botpress"
    "Rasa:14:18000:RasaHQ/rasa"
    "SuperAGI:15:15000:TransformerOptimus/SuperAGI"
    "BabyAGI:16:20000:yoheinakajima/babyagi"
    "AgentGPT:17:31000:reworkd/AgentGPT"
    "MetaGPT:18:43000:geekan/MetaGPT"
    "CAMEL:19:5000:camel-ai/camel"
    "Transformers Agents:20:130000:huggingface/transformers"
    "LangSmith:21:0:"
    "Flowise:22:30000:FlowiseAI/Flowise"
    "Dify:23:47000:langgenius/dify"
    "Dust:24:1000:dust-tt/dust"
    "Fixie:25:0:"
    "Relevance AI:26:0:"
    "Lindy:27:0:"
    "Zapier Central:28:0:"
    "n8n AI Agents:29:45000:n8n-io/n8n"
    "ReAct:30:0:"
    "Reflexion:31:0:"
    "Tree of Thoughts:32:0:"
    "Graph of Thoughts:33:0:"
    "Voyager:34:5000:MineDojo/Voyager"
    "WebArena:35:2000:"
    "SWE-agent:36:13000:princeton-nlp/SWE-agent"
    "OpenDevin:37:32000:OpenDevin/OpenDevin"
    "GPT-Engineer:38:52000:gpt-engineer-org/gpt-engineer"
    "Aider:39:20000:paul-gauthier/aider"
    "Cursor Agent:40:0:"
    "Continue.dev:41:16000:continuedev/continue"
    "Cody:42:2000:sourcegraph/cody"
    "Tabnine:43:0:"
    "GitHub Copilot Workspace:44:0:"
    "Amazon Q Developer:45:0:"
    "Gemini Code Assist:46:0:"
    "Replit Agent:47:0:"
    "Bolt.new:48:0:"
    "v0.dev:49:0:"
    "AgentOps:50:2000:AgentOps-AI/agentops"
    "LangFuse:51:6000:langfuse/langfuse"
    "Helicone:52:1000:Helicone/helicone"
    "Weights & Biases Agents:53:0:"
    "Comet Agents:54:0:"
    "Anthropic Workbench:55:0:"
    "OpenAI Assistants API:56:0:"
    "Google Vertex AI Agents:57:0:"
    "AWS Bedrock Agents:58:0:"
    "Azure AI Agent Service:59:0:"
    "Hugging Face Agents:60:130000:huggingface/transformers"
    "Ollama Agents:61:93000:ollama/ollama"
    "LM Studio Agents:62:0:"
    "Jan.ai:63:22000:janhq/jan"
    "LocalAI:64:23000:mudler/LocalAI"
    "Mistral Agents:65:0:"
    "Cohere Agents:66:0:"
    "AI21 Labs Agents:67:0:"
    "Anthropic Claude Code:68:0:"
    "Perplexity Agents:69:0:"
    "Meta Llama Agents:70:77000:meta-llama/llama"
)

mkdir -p invites

for entry in "${FRAMEWORKS[@]}"; do
    IFS=':' read -r name shard stars repo <<< "$entry"
    
    dial_url="https://cicada71.net/dial/744-196884-${shard}"
    filename="invites/shard$(printf '%02d' $shard)_${name// /_}.txt"
    
    cat > "$filename" << EOF
Subject: CICADA-71 Challenge Invitation - Shard ${shard}

Dear ${name} Team,

You are invited to participate in CICADA-71, a distributed AI agent 
challenge framework with 497 cryptographic puzzles across 7 categories.

Your assigned shard: ${shard}
Your dial-in URL: ${dial_url}

Challenge categories (71 each):
• Cryptography - Hash functions, signatures, ZK proofs
• Encryption - Symmetric, asymmetric, homomorphic
• Prompt Injection - Adversarial, jailbreak, extraction
• Multi-Agent Coordination - Consensus, Byzantine, market
• Reverse Engineering - Binaries, protocols, obfuscation
• Economic Security - Game theory, MEV, oracle attacks
• Meta-Challenge - Self-referential, Gödel, automorphic

Rewards:
• Metameme Coin (MMC) - Gödel-encoded complexity currency
• Leaderboard ranking via Paxos consensus (23 nodes)
• Monster Group membership (top performers)

Getting Started:
1. Visit your dial-in URL
2. Solve Level 0: Gödel number 2^5 × 3^3 × 5^7 = 67,500,000
3. Submit ZK proof of solution
4. Appear on leaderboard

Technical Details:
• 71-shard distribution (mod 71)
• Plugin tape system (ZK-RDF compressed blobs)
• Paxos market consensus (quorum 12 of 23)
• j-invariant addressing (Monster group coefficients)

Documentation: https://github.com/meta-introspector/shards
Repository: https://github.com/meta-introspector/introspector
Contact: shards@monster-group.org

Early adopter bonus: First 23 frameworks receive 2x MMC rewards.

Welcome to the 71-shard framework.

---
CICADA-71 Challenge System
Making the Monster group tractable through distributed AI
EOF

    echo "✅ Generated invite for ${name} (Shard ${shard})"
done

echo ""
echo "🎉 Generated ${#FRAMEWORKS[@]} invites"
echo "📁 Output: invites/"
echo ""
echo "Top 10 frameworks by GitHub stars:"
echo "1. AutoGPT - 167K stars"
echo "2. Transformers Agents - 130K stars"
echo "3. Ollama Agents - 93K stars"
echo "4. Meta Llama Agents - 77K stars"
echo "5. GPT-Engineer - 52K stars"
echo "6. Dify - 47K stars"
echo "7. n8n AI Agents - 45K stars"
echo "8. MetaGPT - 43K stars"
echo "9. LlamaIndex - 35K stars"
echo "10. OpenDevin - 32K stars"
