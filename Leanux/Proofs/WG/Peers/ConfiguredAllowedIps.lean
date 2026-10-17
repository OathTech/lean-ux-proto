import Leanux.Proofs.WG.Peers.ConfiguredIdentity
import Leanux.Proofs.WG.AllowedIps.ClearWalk

/-! Normal clearing preserves the configured peer identities. The native trie
actions retain their own failure paths; no well-formedness or totality is assumed. -/
namespace Leanux.Proofs.WG.ConfiguredIdentity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem rootRemovePeerLists_view (root : NodeId) :
    SameView view (rootRemovePeerLists root) := by
  intro initial
  let P := fun w : WGWorld => view w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact preserves_pure d
  have peer (pid : PeerId) : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_spec (fun s => s = initial) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  have aip {α : Type} (a : AipM α) : Preserves P (liftAip a) := by
    apply hoare_liftAip a P
    intro w d store hi hd
    simpa only [P, view, hd, Option.map_some, state] using hi
  have children (cs : List (Option NodeId)) (stack : List NodeId) :
      Preserves P (AllowedIps.pushChildren cs stack) := by
    unfold AllowedIps.pushChildren
    apply list_view_spec view (fun s => s = initial)
    intro c rest
    unfold AllowedIps.pushChild
    apply preserves_bind (ambient (AmbientM.branch .pushRcuNonNull c.isSome))
    intro nonnull
    cases nonnull <;> cases c <;> exact preserves_pure _
  have step (i : Nat) (stack : Option Unit × List NodeId) :
      Preserves P (AllowedIps.rootRemoveStep i stack) := by
    unfold AllowedIps.rootRemoveStep
    cases stack.2 with
    | nil =>
      exact preserves_bind (ambient (AmbientM.branch .rootRemoveLenPositive false))
        (fun _ => preserves_pure _)
    | cons id rest =>
      apply preserves_bind (ambient (AmbientM.branch .rootRemoveLenPositive true))
      intro _
      apply preserves_bind (ambient (AmbientM.branch .rootRemovePopped true))
      intro _
      apply preserves_bind (aip (getNode id))
      intro n
      apply preserves_bind (children n.bit.toList rest)
      intro next
      apply preserves_bind (ambient (AmbientM.branch .rootRemoveHasPeer n.peer.isSome))
      intro hasPeer
      cases hasPeer with
      | false => exact preserves_pure _
      | true =>
        cases n.peer with
        | none =>
          exact preserves_bind (ambient (AmbientM.invariant "unreachable"))
            (fun _ => preserves_pure _)
        | some pid =>
          apply preserves_bind (peer pid)
          intro p
          split
          · exact preserves_bind (ambient (AmbientM.invariant "trie node missing from its peer's list"))
              (fun _ => preserves_bind ((listDel_view id).wp (fun s => s = initial))
                (fun _ => preserves_pure _))
          · exact preserves_bind ((listDel_view id).wp (fun s => s = initial))
              (fun _ => preserves_pure _)
  rw [← AllowedIps.rootRemoveSource_eq]
  unfold AllowedIps.rootRemoveSource
  apply preserves_bind device
  intro d
  apply preserves_bind
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    exact list_view_spec view (fun s => s = initial) _ _ _ step
  · intro result
    cases result.1 with
    | none => exact ambient (AmbientM.invariant "root_remove_peer_lists did not terminate")
    | some x => exact preserves_pure x

theorem allowedipsFree_view : SameView view WG.free := by
  intro initial
  let P := fun w : WGWorld => view w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact preserves_pure d
  have aip {α : Type} (a : AipM α) : Preserves P (liftAip a) := by
    apply hoare_liftAip a P
    intro w d store hi hd
    simpa only [P, view, hd, Option.map_some, state] using hi
  unfold WG.free
  apply preserves_bind device
  intro d
  apply preserves_bind (modifyDev_spec (fun s => s = initial)
    (fun q => {q with peerAllowedips := {root4 := none, root6 := none, seq := d.peerAllowedips.seq + 1}})
    (fun _ => rfl))
  intro _
  apply preserves_bind
  · apply list_view_spec view (fun s => s = initial)
    intro item acc
    rcases item with ⟨old, decision⟩
    apply preserves_bind (ambient (AmbientM.branch decision old.isSome))
    intro present
    cases present with
    | false => exact preserves_pure _
    | true =>
      cases old with
      | none => exact preserves_pure _
      | some root =>
        apply preserves_bind ((rootRemovePeerLists_view root).wp (fun s => s = initial))
        intro _
        apply preserves_bind (aip (subtree root))
        intro nodes
        apply preserves_bind
        · apply list_view_spec view (fun s => s = initial)
          intro id _
          exact preserves_bind (aip (freeNode id)) (fun _ => preserves_pure _)
        · intro _
          exact preserves_pure _
  · intro _
    exact preserves_pure _

end Leanux.Proofs.WG.ConfiguredIdentity
