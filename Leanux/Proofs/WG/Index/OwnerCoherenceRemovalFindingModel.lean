import Leanux.Proofs.WG.Config.QuietModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace RemovalOwnerWitness

/-- A last-reference peer with its own handshake owner word, empty key slots,
work and trie state. No reachability is claimed for this local witness. -/
def peer : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [],
  internalId := 0, handshakeEntryPeer := some 0}

def key : Keypair := {peer := some 0}
def entry : IndexEntry := {index := 7, owner := .keypair 0}

def device : Device := {
  ifindex := 0, ifname := "wg0", numPeers := 1, peerList := [0],
  peers := ({} : Std.TreeMap PeerId Peer).insert 0 peer,
  keypairs := ({} : Std.TreeMap KeypairId Keypair).insert 0 key,
  indexTable := [entry], nextKeypairId := 1}

def deadDevice : Device := Config.deadPeerDevice (Config.unlistPeer device 0) 0 peer
def deadPeer : Peer := {peer with isDead := true}
def finalDevice : Device := Config.quietRemovedDevice deadDevice 0 deadPeer

end RemovalOwnerWitness

end Leanux.Proofs.WG.Index
