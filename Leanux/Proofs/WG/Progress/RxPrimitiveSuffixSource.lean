import Leanux.Proofs.WG.Progress.ReleaseSuffixSource
import Leanux.Proofs.WG.Queues.RxPollJointProjection

/-! Normal record-suffix preservation for actual RX queue and replay-counter operations, plus transport through an exact append-only native observation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem native_forIn {α β : Type} (records : List HiddenRecord) (xs : List α) (initial : β)
    (f : α → β → WG.M (ForInStep β)) (each : ∀ x b, NativeKeeps records (f x b)) :
    NativeKeeps records (forIn xs initial f) := by
  induction xs generalizing initial with
  | nil => exact native_pure records _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply native_bind records _ _ (each x initial)
    intro step
    cases step with
    | done b => exact native_pure records b
    | yield b => exact ih b

theorem counterValidate_retains (records : List HiddenRecord) (kid : KeypairId) (nonce : Nat) :
    NativeKeeps records (counterValidate kid nonce) := by
  unfold counterValidate
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact native_getKeypair records _
    | with_reducible exact native_setKeypair records _ _
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_branchCmp records _ _ _ _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_forIn records
    | with_reducible apply native_or records
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem prev_dequeue_retains {α : Type} (records : List HiddenRecord) (q : PrevQueue α) :
    NativeKeeps records q.dequeue := by
  unfold PrevQueue.dequeue
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_unsupported records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem prev_peek_retains {α : Type} (records : List HiddenRecord) (q : PrevQueue α) :
    NativeKeeps records q.peek := by
  unfold PrevQueue.peek
  repeat' first
    | with_reducible exact prev_dequeue_retains records _
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem rx_peek_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (Queues.peekRxQueue pid) := by
  unfold Queues.peekRxQueue
  repeat' first
    | with_reducible exact native_getPeer records _
    | with_reducible exact native_setPeer records _ _
    | with_reducible exact prev_peek_retains records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | (with_reducible intro x; try dsimp only)

theorem rx_drop_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (Queues.dropRxQueue pid) := by
  unfold Queues.dropRxQueue
  repeat' first
    | with_reducible exact native_getPeer records _
    | with_reducible exact native_setPeer records _ _
    | with_reducible apply native_bind records
    | (with_reducible intro x; try dsimp only)

theorem rx_complete_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (Queues.completeRxQueue pid) :=
  native_peerUpdate records pid _

theorem endpointFromSkb_retains (records : List HiddenRecord) (src : SkbSource) :
    NativeKeeps records (endpointFromSkb src) := by
  unfold endpointFromSkb
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_unsupported records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem native_and (records : List HiddenRecord) (left right : WG.M Bool)
    (hl : NativeKeeps records left) (hr : NativeKeeps records right) :
    NativeKeeps records (WG.andM left right) := by
  unfold WG.andM
  apply native_bind records _ _ hl
  intro b
  cases b
  · exact native_pure records _
  · exact hr

theorem rx_ready_retains (records : List HiddenRecord) (first : Option SkbId) :
    NativeKeeps records (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((←getRxSkb f).state != .uncrypted)) := by
  apply native_and records _ _ (native_branch records _ _)
  split
  · exact native_bind records _ _ (native_getRx records _) (fun _=>native_branch records _ _)
  · exact native_invariant records _

theorem freeRx_retains (records : List HiddenRecord) (id : SkbId) :
    NativeKeeps records (freeRxSkb id) := by
  apply native_liftSkb
  intro s
  unfold SkbStore.freeRx SkbStore.getRx
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · exact preserves_pure _
  · exact ambient_stop _ _

theorem native_observed {E α : Type} (records : List HiddenRecord)
    (observed : WGPrefix E α) (action : WG.M α)
    (appends : StateAppends observed) (erases : ErasesStatePrefix observed action)
    (keep : NativeKeeps records action) :
    StatePrefixPreserves (fun (_ : List E) _ a=>Tail records a.hidden) (fun _=>True) observed := by
  intro g a h pre
  obtain ⟨suffix,append⟩ := appends g a h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run : (runPrefix (observed.run g) a h).1 with
  | error e => trivial
  | ok out =>
    obtain ⟨⟨value,after⟩,b⟩ := out
    exact (hoare_iff_run _ _ _).mp (keep g) a (value,after) b pre
      ((erases g a h).symm.trans run)

end Leanux.Proofs.WG.Progress.RecordSuffix
