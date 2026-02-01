use serde::{Deserialize, Serialize};
use std::fs;

#[derive(Debug, Serialize, Deserialize)]
struct Framework {
    rank: u8,
    name: String,
    shard: u8,
    category: String,
    github_stars: Option<u32>,
    repo: Option<String>,
    contact: Option<String>,
}

#[derive(Debug, Serialize)]
struct Invite {
    framework: String,
    shard: u8,
    dial_url: String,
    message: String,
}

const FRAMEWORKS: [(&str, &str, Option<u32>, Option<&str>); 71] = [
    ("LangChain", "Enterprise", Some(90000), Some("langchain-ai/langchain")),
    ("LangGraph", "Enterprise", Some(15000), Some("langchain-ai/langgraph")),
    ("AutoGen", "Enterprise", Some(30000), Some("microsoft/autogen")),
    ("CrewAI", "Enterprise", Some(20000), Some("joaomdmoura/crewAI")),
    ("Semantic Kernel", "Enterprise", Some(21000), Some("microsoft/semantic-kernel")),
    ("LlamaIndex", "Enterprise", Some(35000), Some("run-llama/llama_index")),
    ("Haystack", "Enterprise", Some(16000), Some("deepset-ai/haystack")),
    ("AutoGPT", "Enterprise", Some(167000), Some("Significant-Gravitas/AutoGPT")),
    ("OpenAI Agents SDK", "Enterprise", None, None),
    ("Claude Agent SDK", "Enterprise", None, None),
    ("PydanticAI", "Specialized", Some(8000), Some("pydantic/pydantic-ai")),
    ("smolagents", "Specialized", Some(5000), Some("huggingface/smolagents")),
    ("Agno", "Specialized", Some(3000), None),
    ("Botpress", "Specialized", Some(12000), Some("botpress/botpress")),
    ("Rasa", "Specialized", Some(18000), Some("RasaHQ/rasa")),
    ("SuperAGI", "Specialized", Some(15000), Some("TransformerOptimus/SuperAGI")),
    ("BabyAGI", "Specialized", Some(20000), Some("yoheinakajima/babyagi")),
    ("AgentGPT", "Specialized", Some(31000), Some("reworkd/AgentGPT")),
    ("MetaGPT", "Specialized", Some(43000), Some("geekan/MetaGPT")),
    ("CAMEL", "Specialized", Some(5000), Some("camel-ai/camel")),
    ("Transformers Agents", "Specialized", Some(130000), Some("huggingface/transformers")),
    ("LangSmith", "Specialized", None, None),
    ("Flowise", "Specialized", Some(30000), Some("FlowiseAI/Flowise")),
    ("Dify", "Specialized", Some(47000), Some("langgenius/dify")),
    ("Dust", "Specialized", Some(1000), Some("dust-tt/dust")),
    ("Fixie", "Specialized", None, None),
    ("Relevance AI", "Specialized", None, None),
    ("Lindy", "Specialized", None, None),
    ("Zapier Central", "Specialized", None, None),
    ("n8n AI Agents", "Specialized", Some(45000), Some("n8n-io/n8n")),
    ("ReAct", "Research", None, None),
    ("Reflexion", "Research", None, None),
    ("Tree of Thoughts", "Research", None, None),
    ("Graph of Thoughts", "Research", None, None),
    ("Voyager", "Research", Some(5000), Some("MineDojo/Voyager")),
    ("WebArena", "Research", Some(2000), None),
    ("SWE-agent", "Research", Some(13000), Some("princeton-nlp/SWE-agent")),
    ("OpenDevin", "Research", Some(32000), Some("OpenDevin/OpenDevin")),
    ("GPT-Engineer", "Research", Some(52000), Some("gpt-engineer-org/gpt-engineer")),
    ("Aider", "Research", Some(20000), Some("paul-gauthier/aider")),
    ("Cursor Agent", "Research", None, None),
    ("Continue.dev", "Research", Some(16000), Some("continuedev/continue")),
    ("Cody", "Research", Some(2000), Some("sourcegraph/cody")),
    ("Tabnine", "Research", None, None),
    ("GitHub Copilot Workspace", "Research", None, None),
    ("Amazon Q Developer", "Research", None, None),
    ("Gemini Code Assist", "Research", None, None),
    ("Replit Agent", "Research", None, None),
    ("Bolt.new", "Research", None, None),
    ("v0.dev", "Research", None, None),
    ("AgentOps", "Domain", Some(2000), Some("AgentOps-AI/agentops")),
    ("LangFuse", "Domain", Some(6000), Some("langfuse/langfuse")),
    ("Helicone", "Domain", Some(1000), Some("Helicone/helicone")),
    ("Weights & Biases Agents", "Domain", None, None),
    ("Comet Agents", "Domain", None, None),
    ("Anthropic Workbench", "Domain", None, None),
    ("OpenAI Assistants API", "Domain", None, None),
    ("Google Vertex AI Agents", "Domain", None, None),
    ("AWS Bedrock Agents", "Domain", None, None),
    ("Azure AI Agent Service", "Domain", None, None),
    ("Hugging Face Agents", "Domain", Some(130000), Some("huggingface/transformers")),
    ("Ollama Agents", "Domain", Some(93000), Some("ollama/ollama")),
    ("LM Studio Agents", "Domain", None, None),
    ("Jan.ai", "Domain", Some(22000), Some("janhq/jan")),
    ("LocalAI", "Domain", Some(23000), Some("mudler/LocalAI")),
    ("Mistral Agents", "Domain", None, None),
    ("Cohere Agents", "Domain", None, None),
    ("AI21 Labs Agents", "Domain", None, None),
    ("Anthropic Claude Code", "Domain", None, None),
    ("Perplexity Agents", "Domain", None, None),
    ("Meta Llama Agents", "Domain", Some(77000), Some("meta-llama/llama")),
];

fn generate_invite(framework: &str, shard: u8) -> Invite {
    let dial_url = format!("https://cicada71.net/dial/744-196884-{}", shard);
    
    let message = format!(
r#"Subject: CICADA-71 Challenge Invitation - Shard {}

Dear {} Team,

You are invited to participate in CICADA-71, a distributed AI agent 
challenge framework with 497 cryptographic puzzles across 7 categories.

Your assigned shard: {}
Your dial-in URL: {}

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
"#,
        shard, framework, shard, dial_url
    );

    Invite {
        framework: framework.to_string(),
        shard,
        dial_url,
        message,
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    fs::create_dir_all("invites")?;
    
    let mut invites = Vec::new();
    
    for (idx, (name, category, stars, repo)) in FRAMEWORKS.iter().enumerate() {
        let shard = idx as u8;
        let invite = generate_invite(name, shard);
        
        // Write individual invite
        let filename = format!("invites/shard{:02}_{}.txt", shard, name.replace(" ", "_"));
        fs::write(&filename, &invite.message)?;
        
        println!("✅ Generated invite for {} (Shard {})", name, shard);
        
        invites.push(invite);
    }
    
    // Write summary JSON
    let summary = serde_json::to_string_pretty(&invites)?;
    fs::write("invites/all_invites.json", summary)?;
    
    println!("\n🎉 Generated {} invites", invites.len());
    println!("📁 Output: invites/");
    println!("📊 Summary: invites/all_invites.json");
    
    Ok(())
}
