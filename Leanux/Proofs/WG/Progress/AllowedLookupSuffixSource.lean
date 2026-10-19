import Leanux.Proofs.WG.Progress.StagingSuffixSource
import Leanux.Proofs.WG.Queues.RxBorrow

/-! Ambient record-suffix transport through the original bounded allowed-IP search, acquisition and repayment. No represented-trie or live-owner premise is needed for normal-result preservation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

abbrev AipKeeps (records : List HiddenRecord) {α : Type} (action : AipM α) : Prop :=
  ∀ s, Preserves (fun a=>Tail records a.hidden) (action.run s)

theorem aip_pure {α : Type} (records : List HiddenRecord) (value : α) :
    AipKeeps records (pure value) := fun _=>preserves_pure _

theorem aip_bind {α β : Type} (records : List HiddenRecord)
    (action : AipM α) (next : α→AipM β)
    (first : AipKeeps records action) (rest : ∀ x,AipKeeps records (next x)) :
    AipKeeps records (action >>= next) := by
  intro s
  rw [StateT.run_bind]
  exact preserves_bind (first s) (fun out=>rest out.1 out.2)

theorem aip_ambient {α : Type} (records : List HiddenRecord) (action : AmbientM α)
    (keep : Preserves (fun a=>Tail records a.hidden) action) :
    AipKeeps records (monadLift action) := by
  intro s
  change Preserves _ (action >>= fun value=>pure (value,s))
  exact preserves_bind keep (fun _=>preserves_pure _)

theorem aip_forIn {α β : Type} (records : List HiddenRecord) (xs : List α) (initial : β)
    (f : α→β→AipM (ForInStep β)) (each : ∀x b,AipKeeps records (f x b)) :
    AipKeeps records (forIn xs initial f) := by
  induction xs generalizing initial with
  | nil => exact aip_pure records _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply aip_bind records _ _ (each x initial)
    intro step
    cases step with
    | done b => exact aip_pure records b
    | yield b => exact ih b

theorem aip_getNode (records : List HiddenRecord) (id : NodeId) :
    AipKeeps records (getNode id) := by
  intro s
  unfold getNode
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · exact preserves_pure _
  · exact ambient_stop _ _

theorem aip_branch (records : List HiddenRecord) (decision : Decision) (value : Bool) :
    AipKeeps records (branch decision value) := by
  apply aip_ambient
  apply (hoare_iff_run _ _ _).mpr
  intro before out after pre run
  cases run
  exact pre

theorem aip_invariant {α : Type} (records : List HiddenRecord) (message : String) :
    AipKeeps records (invariant message : AipM α) := fun _=>ambient_stop _ _

theorem findNode_retains (records : List HiddenRecord) (root : Option NodeId) (bits key : Nat) :
    AipKeeps records (findNode root bits key) := by
  unfold findNode prefixMatches commonBits choose AipNode.bitAt
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact aip_getNode records _
    | with_reducible exact aip_branch records _ _
    | with_reducible exact aip_invariant records _
    | with_reducible exact aip_pure records _
    | with_reducible apply aip_forIn records
    | with_reducible apply aip_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem native_liftAip {α : Type} (records : List HiddenRecord) (action : AipM α)
    (keep : AipKeeps records action) :
    NativeKeeps records (liftAip action) := by
  unfold liftAip
  apply native_bind records _ _ (native_getDev records)
  intro d
  apply native_bind records _ _ (native_ambient records _ (keep _))
  intro out
  exact native_bind records _ _ (native_modifyDev records _) (fun _=>native_pure records _)

theorem swapEndian_retains (records : List HiddenRecord) (bits : Nat) :
    NativeKeeps records (swapEndian bits) := by
  unfold swapEndian
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | native_suffix_step

theorem peerGetMaybeZero_retains (records : List HiddenRecord) (peer : Option PeerId) :
    NativeKeeps records (peerGetMaybeZero peer) := by
  unfold peerGetMaybeZero requireNotPending
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | (native_suffix_head refcountIncNotZero; exact native_refcountIncNotZero records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | native_suffix_step

theorem lookup_retains (records : List HiddenRecord) (root : Option NodeId) (bits key : Nat) :
    NativeKeeps records (lookup root bits key) := by
  unfold lookup
  apply native_bind records _ _ (swapEndian_retains records bits)
  intro _
  apply native_bind records _ _ (native_liftAip records _ (findNode_retains records root bits key))
  intro node
  have read (id : NodeId) : NativeKeeps records (monadLift (getNode id) : WG.M AipNode) :=
    native_liftAip records _ (aip_getNode records id)
  repeat' first
    | with_reducible exact read _
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head peerGetMaybeZero; exact peerGetMaybeZero_retains records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | (native_suffix_head unsupported; exact native_unsupported records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem lookupSrc_retains (records : List HiddenRecord) (protocol : Nat) (bytes : List UInt8) :
    NativeKeeps records (lookupSrc protocol bytes) := by
  unfold lookupSrc
  repeat' first
    | (native_suffix_head getDev; exact native_getDev records)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head lookup; exact lookup_retains records _ _ _)
    | native_suffix_step

theorem lookupRepay_retains (records : List HiddenRecord) (protocol : Nat) (bytes : List UInt8) :
    NativeKeeps records (Queues.RxBorrow.source protocol bytes) := by
  unfold Queues.RxBorrow.source Queues.RxBorrow.repayLookup
  exact native_bind records _ _ (lookupSrc_retains records protocol bytes)
    (fun peer=>native_bind records _ _ (peerPut_retains records peer) (fun _=>native_pure records _))

end Leanux.Proofs.WG.Progress.RecordSuffix
