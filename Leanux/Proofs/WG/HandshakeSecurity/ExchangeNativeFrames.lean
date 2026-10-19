import Leanux.Proofs.WG.HandshakeSecurity.ExchangeObservation
import Leanux.Proofs.WG.HandshakeSecurity.LookupFrames
import Leanux.Proofs.WG.Origins.ConfiguredReceive
import Leanux.Proofs.WG.HandshakeSecurity.FreshnessAllocation

/-! Native exchange-carrier frames inspect only the optional handshake tags.
Dropping a peer or zeroing its handshake cannot restore a consumed exchange. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def Retains (w v : WGWorld) : Prop :=
  ∀ pid tag, handshakeTagAt v pid = some tag → tag ≠ HANDSHAKE_ZEROED →
    handshakeTagAt w pid = some tag

theorem Retains.refl (w : WGWorld) : Retains w w := fun _ _ found _ => found

theorem Retains.trans {w v u : WGWorld} (first : Retains w v) (second : Retains v u) : Retains w u :=
  fun pid tag found nonzero => first pid tag (second pid tag found nonzero) nonzero

theorem retained_handshake {w v : WGWorld} (h : RetainsHandshake w v) : Retains w v := by
  intro pid tag found _
  obtain ⟨p,resident,equal⟩ := Option.map_eq_some_iff.mp found
  have view := h pid (handshakeView p) (by simpa only [peerView,Option.map_eq_some_iff] using ⟨p,resident,rfl⟩)
  have mapped := congrArg (Option.map HandshakeView.state) view
  simpa only [peerView,handshakeTagAt,Option.map_map,Function.comp_def,handshakeView,Option.map_some,equal] using mapped

theorem retained {h : List Event} {w v : WGWorld} (hi : StateInv h w) (frame : Retains w v) : StateInv h v := by
  obtain ⟨ledger,history,coherent⟩ := hi
  exact ⟨ledger,history,fun pid tag found nonzero => coherent pid tag (frame pid tag found nonzero) nonzero⟩

theorem frame (h : List Event) (action : WG.M α)
    (retention : ∀ w v a b result, (action.run w).run a = .ok ((result,v),b) → Retains w v) :
    Framing.Preserves (StateInv h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact retained hi (retention w v a b result run)

theorem frame_world (h : List Event) (action : WG.M α) (same : SameView id action) :
    Framing.Preserves (StateInv h) action := by
  apply frame h action
  intro w v a b result run
  have equal := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  change v = w at equal
  rw [equal]
  exact .refl _

theorem read_peer (pid : PeerId) (h : List Event) : Framing.Preserves (StateInv h) (getPeer pid) := by
  apply frame h _
  intro w v a b p run
  rw [(getPeer_normal pid w v p a b run).1]
  exact .refl _

theorem modify_device (f : Device → Device) (same : ∀ d, (f d).peers = d.peers) (h : List Event) :
    Framing.Preserves (StateInv h) (modifyDev f) := by
  apply frame h _
  intro w v a b result run
  cases run
  intro pid tag found _
  simpa only [handshakeTagAt,Option.bind_map,Function.comp_def,same] using found

theorem modify_world (f : WGWorld → WGWorld)
    (same : ∀ w, handshakeTagAt (f w) = handshakeTagAt w) (h : List Event) :
    Framing.Preserves (StateInv h) (modify f : WG.M Unit) := by
  apply frame h _
  intro w v a b result run
  cases run
  intro pid tag found _
  simpa only [same] using found

theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).handshakeState = p.handshakeState ∨ (f p).handshakeState = HANDSHAKE_ZEROED)
    (h : List Event) : Framing.Preserves (StateInv h) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply frame h _
  intro w v a b result run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ambient,getter,setter⟩ := run
  obtain ⟨worldEq,ambientEq,d,hd,hp⟩ := getPeer_normal pid w read p a ambient getter
  subst read
  subst ambient
  change Except.ok (((),{w with dev := w.dev.map fun d => {d with peers := d.peers.insert pid (f p)}}),a) =
    .ok ((result,v),b) at setter
  simp only [hd,Option.map_some,Except.ok.injEq,Prod.mk.injEq] at setter
  rw [← setter.1.2]
  intro target tag found nonzero
  by_cases eq : pid = target
  · subst target
    have tagEq : (f p).handshakeState = tag := by simpa [handshakeTagAt,hd] using found
    rcases same p with same | zero
    · simpa [handshakeTagAt,hd,hp] using same.symm.trans tagEq
    · exact False.elim (nonzero (tagEq.symm.trans zero))
  · simpa [handshakeTagAt,hd,Std.TreeMap.getElem?_insert,eq] using found

theorem peer_put (peer : Option PeerId) (h : List Event) : Framing.Preserves (StateInv h) (peerPut peer) :=
  frame h _ (fun w v a b result run => retained_handshake (peerPut_retains_handshake peer w v a b result run))

theorem peer_get_maybe (peer : Option PeerId) (h : List Event) : Framing.Preserves (StateInv h) (peerGetMaybeZero peer) :=
  frame h _ (fun w v a b result run => retained_handshake (peerGetMaybeZero_retains_handshake peer w v a b result run))

theorem pubkey_lookup (key : Key) (h : List Event) : Framing.Preserves (StateInv h) (pubkeyLookup key) :=
  frame h _ (fun w v a b result run => retained_handshake (pubkeyLookup_retains_handshake key w v a b result run))

theorem allocation (h : List Event) (pid : PeerId) (key : Key) (w : WGWorld)
    (hi : StateInv h w) : StateInv h (Peers.creationCoreWorld w pid key) := by
  apply retained hi
  intro target tag found nonzero
  cases hd : w.dev with
  | none => simp [Peers.creationCoreWorld,handshakeTagAt,hd] at found
  | some d =>
    by_cases eq : pid = target
    · subst target
      have zero : tag = HANDSHAKE_ZEROED := by simpa [Peers.creationCoreWorld,Peers.createdPeer,handshakeTagAt,hd,HANDSHAKE_ZEROED] using found.symm
      exact False.elim (nonzero zero)
    · simpa [Peers.creationCoreWorld,handshakeTagAt,hd,Std.TreeMap.getElem?_insert,eq] using found

theorem initial (net bare : Bool) : StateInv [] (Runner.initialWG net bare) := by
  refine ⟨fun _ => none,.nil,?_⟩
  intro pid tag found _
  cases net <;> cases bare <;> simp [Runner.initialWG,handshakeTagAt] at found

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
