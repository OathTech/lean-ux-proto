import Leanux.Proofs.WG.Lifetimes.SavedPeers

/-! Demand-driven reads through a saved map and a list of scalar IDs. Missing
entries emit nothing; repeated IDs repeat their actual saved-object read. The
scan completes before a caller starts effects that can change the peer store. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def savedPeerLookup (peers : Std.TreeMap PeerId Peer) (pid : PeerId) : MixedM (Option Peer) := do
  match peers[pid]? with
  | none => return none
  | some p => savedPeerRead pid p; return some p

theorem savedPeerLookup_run (peers : Std.TreeMap PeerId Peer) (pid : PeerId) (w : World) (h : List LifetimeEvent) :
    runPrefix (savedPeerLookup peers pid) w h =
      (.ok (peers[pid]?, w), h ++ (peers[pid]?).toList.map (fun p => .peer (.read pid p.internalId))) := by
  unfold savedPeerLookup
  cases hp : peers[pid]? <;> simp [-bind_pure_comp, hp, savedPeerRead, map_eq_pure_bind, runPrefix_bind]

theorem savedPeerLookup_erases (peers : Std.TreeMap PeerId Peer) (pid : PeerId) :
    ErasesPrefix (savedPeerLookup peers pid) (pure peers[pid]?) := by
  intro w h
  rw [savedPeerLookup_run]
  rfl

theorem savedPeerLookup_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (peers : Std.TreeMap PeerId Peer) (pid : PeerId) :
    AmbientSpec I (fun s => P s ∧ SavedPeers peers.toList s)
      (savedPeerLookup peers pid) (fun _ s => P s ∧ SavedPeers peers.toList s) := by
  unfold savedPeerLookup
  cases hp : peers[pid]? with
  | none => exact c.pure _ _
  | some p =>
    have hm : (pid,p) ∈ peers.toList := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hp
    have hr : AmbientSpec I (fun s => P s ∧ SavedPeers peers.toList s)
        (savedPeerRead pid p) (fun _ s => P s ∧ SavedPeers peers.toList s) :=
      (savedPeerRead_spec c (fun s => P s ∧ SavedPeers peers.toList s) pid p).consequence
        (fun _ _ hi => ⟨hi.1, hi.2, hi.2.2 pid p hm⟩)
        (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
    exact PrefixEnsures.bind hr (fun _ => c.pure (fun s => P s ∧ SavedPeers peers.toList s) (some p))

def savedPeerLookupFlatMap (peers : Std.TreeMap PeerId Peer)
    (f : PeerId → Peer → List α) : List PeerId → MixedM (List α)
  | [] => pure []
  | pid :: rest => do
    let p ← savedPeerLookup peers pid
    let tail ← savedPeerLookupFlatMap peers f rest
    return (p.toList.flatMap (f pid)) ++ tail

theorem savedPeerLookupFlatMap_run (peers : Std.TreeMap PeerId Peer)
    (f : PeerId → Peer → List α) (ids : List PeerId) (w : World) (h : List LifetimeEvent) :
    runPrefix (savedPeerLookupFlatMap peers f ids) w h =
      (.ok (ids.flatMap (fun pid => (peers[pid]?).toList.flatMap (f pid)), w),
        h ++ ids.flatMap (fun pid => (peers[pid]?).toList.map (fun p => .peer (.read pid p.internalId)))) := by
  induction ids generalizing h with
  | nil => simp [savedPeerLookupFlatMap]
  | cons pid ids ih => simp [-bind_pure_comp, savedPeerLookupFlatMap, map_eq_pure_bind, runPrefix_bind, savedPeerLookup_run, ih, List.append_assoc]

theorem savedPeerLookupFlatMap_erases (peers : Std.TreeMap PeerId Peer)
    (f : PeerId → Peer → List α) (ids : List PeerId) :
    ErasesPrefix (savedPeerLookupFlatMap peers f ids)
      (pure (ids.flatMap (fun pid => (peers[pid]?).toList.flatMap (f pid)))) := by
  intro w h
  rw [savedPeerLookupFlatMap_run]
  rfl

theorem savedPeerLookupFlatMap_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (peers : Std.TreeMap PeerId Peer) (f : PeerId → Peer → List α) (ids : List PeerId) :
    AmbientSpec I (fun s => P s ∧ SavedPeers peers.toList s)
      (savedPeerLookupFlatMap peers f ids) (fun _ s => P s ∧ SavedPeers peers.toList s) := by
  induction ids with
  | nil => exact c.pure _ _
  | cons pid ids ih =>
    exact PrefixEnsures.bind (savedPeerLookup_spec c P peers pid) (fun _ =>
      PrefixEnsures.bind ih (fun _ => c.pure (fun s => P s ∧ SavedPeers peers.toList s) _))

end Leanux.Proofs.WG.Lifetimes
