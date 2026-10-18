import Leanux.Proofs.WG.TransmitSecurity.NonceStaging
import Leanux.Proofs.WG.TransmitSecurity.NonceQueueFrames

/-! Allocation non-reuse throughout a complete original staged-send call,
including the bound-refusal branch and journal prefixes before Stop. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

private theorem packet_allocations (ps : List DataPacket) :
    SameView view (ps.mapM newTxSkb) := by
  induction ps with
  | nil => exact SameView.pure _ _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact (Frames.packet_new p).bind fun x => ih.bind fun xs => SameView.pure _ (x :: xs)

private theorem loop_safe {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix Allocation (ForInStep β))
    (hg : ∀ x b, StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (g x b)) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => Inv (view w) h) List.Nodup
    (fun _ _ _ _ hi => hi.nodup) hg

open Lean Meta Elab Tactic in
elab "nonce_source_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let action ←
    if target.isAppOf ``StatePrefixPreserves then pure args.back!
    else if target.isAppOf ``StatePrefixEnsures then pure args[args.size - 2]!
    else throwError "not a state-prefix contract"
  let action := action.consumeMData.headBeta
  let action := if action.isAppOf ``liftWGPrefix then action.getAppArgs.back!.consumeMData else action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

theorem stagingObserved_safe (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (stagingObserved pid) := by
  unfold stagingObserved
  apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.peer_read pid))
  intro p
  apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.ambient _))
  intro empty
  split
  · exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi)
  · apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.peer_write _ _))
    intro _
    apply StatePrefixEnsures.bind (Frames.lift_preserves (Frames.key_get p.keypairCurrent))
    intro kp
    have hout (invalid : Bool) := Frames.lift_preserves (Frames.outNokey pid p.staged kp invalid)
    change StatePrefixPreserves _ _
      (do
        if ← liftWGPrefix (branch .stagedNoKeypair kp.isNone) then
          return ← liftWGPrefix (stagedOutNokey pid p.staged kp false)
        _)
    apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.ambient _))
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact Frames.lift_frame (Frames.ambient _)
      | some id =>
        apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.key_read _))
        intro k
        apply StatePrefixEnsures.bind (Frames.lift_frame (Frames.ambient _))
        intro invalid
        split
        · exact hout false
        · apply StatePrefixEnsures.bind (Frames.lift_frame ((branchExpired_sameWGWorld _ _ _ _).factor view))
          intro expired
          split
          · exact hout true
          · dsimp only
            repeat' first
              | (nonce_source_head reserveObserved; exact reserveObserved_safe _)
              | (first | nonce_source_head branch | nonce_source_head branchCmp
                 exact Frames.lift_frame (Frames.ambient _))
              | (nonce_source_head ipTunnelEcnEncap
                 exact Frames.lift_frame ((ipTunnelEcnEncap_sameWGWorld _).factor view))
              | (nonce_source_head IndexOwner.peerDeref
                 exact Frames.lift_frame (fun initial => indexOwner_peerDeref_preserves _ (fun w => view w = initial)))
              | (nonce_source_head peerGet; exact Frames.lift_frame (Frames.peerGet _))
              | (nonce_source_head List.mapM; exact Frames.lift_frame (packet_allocations _))
              | (nonce_source_head createData; exact Frames.lift_preserves (Frames.create _ _))
              | (nonce_source_head stagedOutNokey; exact hout true)
              | (nonce_source_head Pure.pure
                 exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi))
              | (nonce_source_head ForIn.forIn; apply loop_safe)
              | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
              | split
              | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.TransmitSecurity.Nonce
