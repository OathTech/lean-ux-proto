import Leanux.Proofs.WG.Index.TableModel

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

def ownerWord (d : Device) : IndexOwner → Option (Option PeerId)
  | .handshake pid => d.peers[pid]?.map Peer.handshakeEntryPeer
  | .keypair kp => d.keypairs[kp]?.map Keypair.peer

/-- Exact owner-store update, used only with resident-owner premises below. -/
def writeOwnerWord (d : Device) (owner : IndexOwner) (word : Option PeerId) : Device :=
  match owner with
  | .handshake pid => match d.peers[pid]? with
    | none => d
    | some p => { d with peers := d.peers.insert pid { p with handshakeEntryPeer := word } }
  | .keypair kp => match d.keypairs[kp]? with
    | none => d
    | some k => { d with keypairs := d.keypairs.insert kp { k with peer := word } }

theorem writeOwnerWord_read (d : Device) (owner : IndexOwner) (old word : Option PeerId)
    (resident : ownerWord d owner = some old) :
    ownerWord (writeOwnerWord d owner word) owner = some word := by
  cases owner with
  | handshake pid =>
    cases h : d.peers[pid]? <;> simp_all [ownerWord, writeOwnerWord]
  | keypair kp =>
    cases h : d.keypairs[kp]? <;> simp_all [ownerWord, writeOwnerWord]

def acquirePeer (d : Device) (pid : PeerId) (p : Peer) : Device :=
  { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }

theorem bucket_find (index : Nat) (table : List IndexEntry) :
    (bucket index table).find? (·.index == index) = table.find? (·.index == index) := by
  simp only [bucket, List.find?_filter]
  congr 1
  funext e
  by_cases same : e.index = index <;> simp [same]

end Leanux.Proofs.WG.Index
