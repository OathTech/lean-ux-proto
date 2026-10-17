import Leanux.Proofs.WG.Index.TablePeerFrames
import Leanux.Proofs.WG.Config.AllowedRemovalSource
import Leanux.Proofs.WG.Config.PeerDead

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Local variant of C1 Framing.hoare_liftAip. The actual adapter's device
check and arbitrary Ambient execution are retained. -/
theorem hoare_liftAip_variant {α : Type} (a : AipM α) (P : WGWorld → Prop)
    (stable : ∀ g d (s : AipStore), P g → g.dev = some d →
      P {g with dev := some {d with nodes := s.nodes, nextNode := s.nextNode, peerAllowedips := s.trie}}) :
    ⦃fun g => ⌜P g⌝⦄ liftAip a ⦃⇓? _ g => ⌜P g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient x final after pre run
  cases device : g.dev with
  | none =>
    simp [liftAip, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases executed : (a.run {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}).run ambient with
    | error err =>
      simp [liftAip, getDev, device, executed] at run
      cases run
    | ok pair =>
      obtain ⟨⟨value, store⟩, inputs⟩ := pair
      simp [liftAip, getDev, modifyDev, device, executed] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact stable g d store pre device

/-- Local table/cursor variant of WGBase.removeByPeer_spec.
Exact index-table/allocation-cursor frame. No trie shape, peer residency,
owner coherence or successful-completion assumption is added at entry. -/
theorem removeByPeer_spec_tableCursor_variant (pid : PeerId)
    (initial : Option TimerDiscipline.TableCursor) :
    Ensures (removeByPeer pid)
      (fun g => g.dev.map TimerDiscipline.tableCursor = initial)
      (fun _ g => g.dev.map TimerDiscipline.tableCursor = initial) := by
  let P := fun g : WGWorld => g.dev.map TimerDiscipline.tableCursor = initial
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have haip {α : Type} (action : AipM α) :
      Ensures (liftM action : WG.M α) P (fun _ => P) := by
    change Ensures (liftAip action) P (fun _ => P)
    apply (ensures_iff _ _ _).mpr (hoare_liftAip_variant action P ?_)
    intro g d store pre device
    simpa [P, device, TimerDiscipline.tableCursor] using pre
  have hpeer (id : PeerId) : Ensures (getPeer id) P (fun _ => P) := by
    intro g a result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec id P) g a result final after pre run).1
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    simpa [P, modifyDev, Option.map_map, Function.comp_def, same] using pre
  have hlistDel (id : NodeId) : Ensures (listDel id) P (fun _ => P) := by
    intro g a result final after pre run
    cases device : g.dev with
    | none =>
      simp [Config.listDel_source, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      obtain ⟨value, next, inputs, executed, effect⟩ := Config.listDel_returns id d g a device
      rw [executed] at run
      cases run
      have same := congrArg TimerDiscipline.tableCursor
        (Config.deleteListedNodes_withoutPeers id d d.peers.toList)
      have sameCursor : TimerDiscipline.tableCursor (Config.deleteListedNodes id d d.peers.toList) = TimerDiscipline.tableCursor d := by
        simpa [TimerDiscipline.tableCursor, Config.withoutPeers] using same
      simpa [P, effect, device, sameCursor] using pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient (AmbientM.branch site value)
  have hbit (n : AipNode) (bit : Nat) : Ensures (n.bitAt bit : WG.M (Option NodeId)) P (fun _ => P) := by
    unfold AipNode.bitAt
    split
    · exact hpure _
    · exact hambient (AmbientM.invariant _)
  have hinv {α : Type} (what : String) : Ensures (invariant what : WG.M α) P (fun _ => P) :=
    hambient (AmbientM.invariant what)
  have hnode (id : NodeId) (n : AipNode) :
      Ensures (Config.removeNodeSource id n) P (fun _ => P) := by
    unfold Config.removeNodeSource
    repeat' first
      | (with_reducible exact hpure _)
      | (with_reducible exact haip _)
      | (with_reducible exact hbit _ _)
      | (with_reducible exact hbranch _ _)
      | (with_reducible exact hinv _)
      | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | split
  have hlist {α β : Type} (xs : List α) (initial : β)
      (body : α → β → WG.M (ForInStep β))
      (step : ∀ a b, Ensures (body a b) P (fun _ => P)) :
      Ensures (forIn xs initial body) P (fun _ => P) := by
    induction xs generalizing initial with
    | nil => simpa only [List.forIn_nil] using hpure initial
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (step x initial) ?_
      intro result
      cases result with
      | done final => exact hpure final
      | yield next => exact ih next
  rw [Config.removeByPeer_source]
  refine ensures_bind (Q := fun _ => P) _ _ (hpeer pid) ?_
  intro p
  rw [Config.removeByPeer_factor]
  unfold Config.removeByPeerFactored
  refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
  intro empty
  cases empty with
  | true => exact hpure ()
  | false =>
    refine ensures_bind (Q := fun _ => P) _ _ (hmodify _ (fun _ => rfl)) ?_
    intro _
    refine ensures_bind (Q := fun _ => P) _ _ (hlist _ _ _ ?_) ?_
    · intro id accumulator
      refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
      intro _
      refine ensures_bind (Q := fun _ => P) _ _ (hlistDel id) ?_
      intro _
      refine ensures_bind (Q := fun _ => P) _ _ (haip (getNode id)) ?_
      exact hnode id
    · intro _
      refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
      intro _
      exact hpure ()

/-- Local table/cursor variant of WGBase.peerMakeDead_spec.
The mixed WG path changes peer membership and flags, but retains the
complete table/cursor pair even for malformed trie states on normal return. -/
theorem peerMakeDead_spec_tableCursor_variant (pid : PeerId)
    (initial : Option TimerDiscipline.TableCursor) :
    Ensures (peerMakeDead pid)
      (fun g => g.dev.map TimerDiscipline.tableCursor = initial)
      (fun _ g => g.dev.map TimerDiscipline.tableCursor = initial) := by
  let P := fun g : WGWorld => g.dev.map TimerDiscipline.tableCursor = initial
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    exact pre
  have hread : Ensures getDev P (fun _ => P) := by
    intro g a result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hpeer (id : PeerId) : Ensures (getPeer id) P (fun _ => P) := by
    intro g a result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec id P) g a result final after pre run).1
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    simpa [P, modifyDev, Option.map_map, Function.comp_def, same] using pre
  have hset (id : PeerId) (p : Peer) : Ensures (setPeer id p) P (fun _ => P) :=
    hmodify (fun d => {d with peers := d.peers.insert id p}) (fun _ => rfl)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  rw [Config.peerMakeDead_source]
  refine ensures_bind (Q := fun _ => P) _ _ (hmodify _ (fun _ => rfl)) ?_
  intro _
  refine ensures_bind (Q := fun _ => P) _ _ (removeByPeer_spec_tableCursor_variant pid initial) ?_
  intro _
  unfold Config.makeDeadAfterRemoval
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hread
    | with_reducible exact hpeer _
    | with_reducible exact hset _ _
    | with_reducible exact hbranch _ _
    | with_reducible exact hmodify _ (fun _ => rfl)
    | (with_reducible refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))

end Leanux.Proofs.WG.Index
