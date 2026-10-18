import Leanux.Proofs.WG.RetirementSecurity.TxCryptStaging

/-! Rejection repays the actual acquired current-key occurrence once.
Restaging and handshake work preserve the remaining key-holder projection;
they do not manufacture a replacement key credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def stagedInvalidSource (key : Option KeypairId) (invalid : Bool) : WG.M Unit := do
  if invalid then
    let some kid := key | invariant "unreachable"
    let k ← getKeypair kid
    setKeypair kid {k with sending := {k.sending with isValid := false}}

def stagedRestoreSource (pid : PeerId) (packets : List WG.Packet) : WG.M Unit := do
  for _ in packets do _ ← branch .stagedOrphanWalk true
  _ ← branch .stagedOrphanWalk false
  setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}
  sendQueuedHandshakeInitiation pid false

theorem staged_no_key_factor (pid : PeerId) (packets : List WG.Packet)
    (key : Option KeypairId) (invalid : Bool) :
    stagedOutNokey pid packets key invalid = (do
      stagedInvalidSource key invalid
      keypairPut key false
      stagedRestoreSource pid packets) := by
  cases invalid <;> cases key <;>
    simp only [stagedOutNokey,stagedInvalidSource,stagedRestoreSource,Bool.false_eq_true,
      ite_false,ite_true,bind_assoc,pure_bind]

theorem staged_invalid_account (key : Option KeypairId) (invalid : Bool) :
    Preserves (HolderAccount temporary) (stagedInvalidSource key invalid) := by
  cases invalid with
  | false => exact preserves_pure _
  | true =>
    cases key with
    | none =>
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b _ run
      cases run
    | some kid =>
      exact key_update_holders kid (fun k => {k with sending := {k.sending with isValid := false}})
        (fun _ => rfl) (fun _ => rfl) temporary

theorem staged_restore_ownership (pid : PeerId) (packets : List WG.Packet) :
    SameView ownershipPointView (stagedRestoreSource pid packets) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold stagedRestoreSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => ownershipPointView w = initial)
       intro x b
       change Preserves (fun w => ownershipPointView w = initial) _)
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact (sendQueued_ownership _ _).wp (· = initial))
    | ownership_source_step initial

theorem HolderAccount.no_key (saved : Option Credits.Allocation)
    (account : HolderAccount (saved.toList ++ temporary) w) (pid : PeerId) (packets : List WG.Packet)
    (invalid : Bool) (a b : Ambient)
    (run : ((stagedOutNokey pid packets (saved.map (·.slot)) invalid).run w).run a =
      .ok (((),v),b)) : HolderAccount temporary v := by
  rw [staged_no_key_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,invalidRun,tail⟩ := run
  have invalidated := (hoare_iff_run_ambient _ _ _).mp (staged_invalid_account (saved.map (·.slot)) invalid)
    w a () u c account invalidRun
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨_,t,e,putRun,restoreRun⟩ := tail
  have paid : HolderAccount temporary t := by
    cases saved with
    | none =>
      simp only [Option.map_none] at putRun
      cases putRun
      simpa only [Option.toList_none,List.nil_append] using invalidated
    | some allocation =>
      exact invalidated.put false c e putRun
  exact paid.points ((ProjectedAction.iff_run_ambient _ _ _).mp
    (staged_restore_ownership pid packets) t e () v b restoreRun)

end Leanux.Proofs.WG.RetirementSecurity
