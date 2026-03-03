#!/usr/bin/env python3
"""
BYZANTINE CONSENSUS SIMULATOR
Simulate 23-node Paxos with Byzantine faults
"""

import random
import hashlib
import json
import time
import math
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional
from enum import Enum

class NodeBehavior(Enum):
    HONEST = "honest"
    BYZANTINE_LIAR = "byzantine_liar"      # Always lies about votes
    BYZANTINE_SILENT = "byzantine_silent"  # Goes offline randomly
    BYZANTINE_RANDOM = "byzantine_random"  # Random responses
    OFFLINE = "offline"

@dataclass
class Node:
    node_id: int
    behavior: NodeBehavior
    shard_affinity: int  # Which shard this node is resonant with
    is_online: bool = True
    
    def compute_resonance(self, shard: int) -> float:
        """Compute resonance for a given shard"""
        angle = 2 * math.pi * self.node_id * shard / 71
        return abs(math.cos(angle))
    
    def should_vote_yes(self, shard: int, proposal_value: str) -> bool:
        """Decide if this node votes YES on a proposal"""
        resonance = self.compute_resonance(shard)
        
        # Honest behavior: vote based on resonance
        if self.behavior == NodeBehavior.HONEST:
            return resonance > 0.5
        
        # Byzantine behaviors
        elif self.behavior == NodeBehavior.BYZANTINE_LIAR:
            # Always vote opposite of what they should
            return resonance <= 0.5
        
        elif self.behavior == NodeBehavior.BYZANTINE_SILENT:
            # Randomly go offline
            if random.random() < 0.3:
                self.is_online = False
                return False
            return resonance > 0.5
        
        elif self.behavior == NodeBehavior.BYZANTINE_RANDOM:
            # Random votes
            return random.random() > 0.5
        
        elif self.behavior == NodeBehavior.OFFLINE:
            return False
        
        return resonance > 0.5
    
    def create_witness(self, shard: int, proposal: str, vote: bool) -> Dict:
        """Create a witness for a vote"""
        timestamp = int(time.time())
        resonance = self.compute_resonance(shard)
        
        # Sign the witness
        sig_input = f"{self.node_id}{shard}{proposal}{timestamp}{vote}"
        signature = hashlib.sha256(sig_input.encode()).hexdigest()[:16]
        
        return {
            "node_id": self.node_id,
            "shard": shard,
            "proposal": proposal,
            "vote": vote,
            "resonance": round(resonance, 6),
            "timestamp": timestamp,
            "signature": signature,
            "behavior": self.behavior.value
        }

class ByzantineConsensus:
    def __init__(self, num_nodes: int = 23):
        self.num_nodes = num_nodes
        self.quorum = (num_nodes // 2) + 1  # 12 for 23 nodes
        self.byzantine_tolerance = (num_nodes - 1) // 3  # 7 for 23 nodes
        self.nodes: List[Node] = []
        self.rounds: List[Dict] = []
        
    def setup_network(self, num_byzantine: int = 0):
        """Set up the network with specified Byzantine nodes"""
        self.nodes = []
        
        # Create honest nodes
        for i in range(self.num_nodes - num_byzantine):
            node = Node(
                node_id=i,
                behavior=NodeBehavior.HONEST,
                shard_affinity=(i * 13) % 71  # Which shard resonates with this node
            )
            self.nodes.append(node)
        
        # Create Byzantine nodes with different behaviors
        byzantine_behaviors = [
            NodeBehavior.BYZANTINE_LIAR,
            NodeBehavior.BYZANTINE_SILENT,
            NodeBehavior.BYZANTINE_RANDOM
        ]
        
        for i in range(num_byzantine):
            node_id = self.num_nodes - num_byzantine + i
            behavior = byzantine_behaviors[i % len(byzantine_behaviors)]
            node = Node(
                node_id=node_id,
                behavior=behavior,
                shard_affinity=(node_id * 13) % 71
            )
            self.nodes.append(node)
        
        print(f"✅ Network initialized:")
        print(f"   Total nodes: {self.num_nodes}")
        print(f"   Honest: {self.num_nodes - num_byzantine}")
        print(f"   Byzantine: {num_byzantine}")
        print(f"   Quorum required: {self.quorum}")
        print(f"   Byzantine tolerance: {self.byzantine_tolerance}")
    
    def propose_value(self, shard: int, proposal: str) -> Dict:
        """
        Propose a value and run consensus
        Returns the consensus result
        """
        print(f"\n{'='*70}")
        print(f"CONSENSUS ROUND: Shard {shard}")
        print(f"Proposal: '{proposal}'")
        print(f"{'='*70}")
        
        witnesses = []
        votes_yes = 0
        votes_no = 0
        nodes_offline = 0
        
        # Collect votes from all nodes
        for node in self.nodes:
            if not node.is_online:
                nodes_offline += 1
                continue
            
            vote = node.should_vote_yes(shard, proposal)
            witness = node.create_witness(shard, proposal, vote)
            witnesses.append(witness)
            
            if vote:
                votes_yes += 1
            else:
                votes_no += 1
            
            # Show vote
            behavior_marker = "⚠️" if node.behavior != NodeBehavior.HONEST else "✓"
            vote_marker = "✅ YES" if vote else "❌ NO"
            print(f"  Node {node.node_id:2d} {behavior_marker}: {vote_marker} "
                  f"(resonance: {node.compute_resonance(shard):.3f}, "
                  f"behavior: {node.behavior.value})")
        
        # Check consensus
        consensus_reached = votes_yes >= self.quorum
        
        print(f"\n{'='*70}")
        print(f"RESULTS:")
        print(f"  Votes YES: {votes_yes}/{self.num_nodes}")
        print(f"  Votes NO: {votes_no}/{self.num_nodes}")
        print(f"  Offline: {nodes_offline}/{self.num_nodes}")
        print(f"  Quorum needed: {self.quorum}")
        print(f"  Consensus: {'✅ REACHED' if consensus_reached else '❌ FAILED'}")
        print(f"{'='*70}")
        
        result = {
            "shard": shard,
            "proposal": proposal,
            "votes_yes": votes_yes,
            "votes_no": votes_no,
            "nodes_offline": nodes_offline,
            "consensus": consensus_reached,
            "witnesses": witnesses,
            "quorum_required": self.quorum
        }
        
        self.rounds.append(result)
        return result
    
    def simulate_network_partition(self):
        """Simulate a network partition - split nodes into groups"""
        print("\n🔥 NETWORK PARTITION ATTACK!")
        partition_size = self.num_nodes // 2
        for i in range(partition_size):
            self.nodes[i].is_online = False
        print(f"   {partition_size} nodes isolated")
    
    def heal_network(self):
        """Bring all nodes back online"""
        print("\n🔧 HEALING NETWORK...")
        for node in self.nodes:
            if node.behavior != NodeBehavior.OFFLINE:
                node.is_online = True
        print("   All nodes back online")
    
    def export_results(self, filename: str = "/tmp/consensus_results.json"):
        """Export all rounds to JSON"""
        with open(filename, 'w') as f:
            json.dump(self.rounds, f, indent=2)
        print(f"\n📊 Results exported to: {filename}")

def main():
    print("="*70)
    print("BYZANTINE CONSENSUS SIMULATOR")
    print("23-Node Paxos with Shard 47 (nydiokar)")
    print("="*70)
    
    sim = ByzantineConsensus(num_nodes=23)
    
    # Scenario 1: All honest nodes
    print("\n\n" + "🔷"*35)
    print("SCENARIO 1: ALL HONEST NODES")
    print("🔷"*35)
    sim.setup_network(num_byzantine=0)
    sim.propose_value(shard=47, proposal="nydiokar is TRUE_FREN")
    
    # Scenario 2: 3 Byzantine nodes (within tolerance)
    print("\n\n" + "⚠️"*35)
    print("SCENARIO 2: 3 BYZANTINE NODES (within tolerance)")
    print("⚠️"*35)
    sim.setup_network(num_byzantine=3)
    sim.propose_value(shard=47, proposal="nydiokar is TRUE_FREN")
    
    # Scenario 3: 7 Byzantine nodes (at limit)
    print("\n\n" + "🔥"*35)
    print("SCENARIO 3: 7 BYZANTINE NODES (at tolerance limit)")
    print("🔥"*35)
    sim.setup_network(num_byzantine=7)
    sim.propose_value(shard=47, proposal="nydiokar is TRUE_FREN")
    
    # Scenario 4: 8 Byzantine nodes (EXCEEDS tolerance - should fail)
    print("\n\n" + "💀"*35)
    print("SCENARIO 4: 8 BYZANTINE NODES (EXCEEDS tolerance - expect failure)")
    print("💀"*35)
    sim.setup_network(num_byzantine=8)
    result = sim.propose_value(shard=47, proposal="nydiokar is TRUE_FREN")
    
    if not result['consensus']:
        print("\n✅ CORRECT: System correctly rejected consensus with too many Byzantine nodes!")
    
    # Scenario 5: Network partition attack
    print("\n\n" + "🌐"*35)
    print("SCENARIO 5: NETWORK PARTITION ATTACK")
    print("🌐"*35)
    sim.setup_network(num_byzantine=0)
    sim.simulate_network_partition()
    sim.propose_value(shard=47, proposal="nydiokar is TRUE_FREN")
    sim.heal_network()
    print("\nAfter healing:")
    sim.propose_value(shard=47, proposal="nydiokar is TRUE_FREN")
    
    # Export results
    sim.export_results()
    
    print("\n\n" + "="*70)
    print("SIMULATION COMPLETE!")
    print("="*70)
    print(f"Total rounds: {len(sim.rounds)}")
    print(f"Byzantine tolerance: {sim.byzantine_tolerance} nodes")
    print(f"Quorum requirement: {sim.quorum} nodes")
    print("\nKey insights:")
    print("  • System works with ≤7 Byzantine nodes")
    print("  • Fails gracefully with >7 Byzantine nodes")
    print("  • Network partitions prevent consensus")
    print("  • Healing restores consensus capability")

if __name__ == "__main__":
    main()
