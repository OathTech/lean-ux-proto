import Leanux.Proofs.WG.Index.OwnerCoherenceModel

/-! Concrete arbitrary-state witness for mismatched staged-send peer ownership.
No initialized reachability is asserted. The single real clock record keeps the
selected key valid; no placeholder clock is used. -/

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace PersistentOwnerWitness

def victim : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 0,
  isDead := true, staged := [{}], keypairCurrent := some 1,
  persistentKeepaliveInterval := 1 }
def acquired : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1 }
def dangling : Keypair := {peer := some 0}
def selected : Keypair := {peer := some 1, sending := {isValid := true}}
def entry : IndexEntry := {index := 7, owner := .keypair 0}
def device : Device := {
  ifindex := 0, ifname := "wg0", numPeers := 2, peerList := [0,1],
  peers := (({} : Std.TreeMap PeerId Peer).insert 0 victim).insert 1 acquired,
  keypairs := (({} : Std.TreeMap KeypairId Keypair).insert 0 dangling).insert 1 selected,
  indexTable := [entry], nextKeypairId := 2 }
def clock : HiddenRecord := {site := HiddenSite.birthdateExpired.info.id, bytes := List.replicate 8 0}

end PersistentOwnerWitness
open PersistentOwnerWitness

theorem persistentOwnerWitness_coherent : HashedOwnersCoherent device := by
  intro e member
  have same : e = entry := by simpa [device] using member
  subst e
  refine ⟨0, victim, ?_, ?_, by decide, ?_⟩
  · simp [ownerWord, entry, device, dangling, Std.TreeMap.getElem_insert]
  · simp [device, Std.TreeMap.getElem_insert]
  · exact ⟨dangling, by simp [device, Std.TreeMap.getElem_insert], by decide⟩


end Leanux.Proofs.WG.Index
