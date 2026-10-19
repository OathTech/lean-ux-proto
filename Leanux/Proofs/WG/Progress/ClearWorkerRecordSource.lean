import Leanux.Proofs.WG.Progress.ClearWorkerRecordFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceClearWorkerSource

/-! Source-derived record suffix transport for the actual clear callback and
selected clear-work dispatch. The source retains all original failure paths.
The general section rule is instantiated with the complete real callback. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem handshakeClear_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (handshakeClear pid) := by
  unfold handshakeClear handshakeZero
  repeat' first
    | with_reducible exact native_peerDeref records _
    | with_reducible exact native_indexRemove records _
    | with_reducible exact native_getPeer records _
    | with_reducible exact native_setPeer records _ _
    | with_reducible apply native_bind records
    | (with_reducible intro x; try dsimp only)

theorem keypairsClear_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (keypairsClear pid) := by
  unfold keypairsClear
  repeat' first
    | with_reducible exact native_getPeer records _
    | with_reducible exact native_modifyPeer records _ _
    | with_reducible exact keypairPut_retains records _ _
    | with_reducible apply native_bind records
    | (with_reducible intro x; try dsimp only)

theorem clearCallback_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact native_bind records _ _ (handshakeClear_retains records pid) (fun _ =>
    native_bind records _ _ (keypairsClear_retains records pid) (fun _ =>
      peerPut_retains records (some pid)))

theorem peekUnit_retains (records : List HiddenRecord) (worker : Worker) :
    Preserves (fun w : World => Tail records w.ambient.hidden)
      (peekUnit worker : Leanux.M (Option Nat)) := by
  apply liftAmbient_contract (AmbientM.peekUnit worker) (fun a=>Tail records a.hidden) (fun _ a=>Tail records a.hidden)
  unfold AmbientM.peekUnit
  apply preserves_bind (retain_tail Ambient.hidden _ skipAmbient_suffix records)
  intro _
  apply preserves_bind (hoare_consequence (hoare_get _)
    (fun _ h=>h) (fun _ _ h=>h.2))
  intro a
  split
  · split <;> exact preserves_pure _
  · exact preserves_pure _

theorem resolveUnit_retains (records : List HiddenRecord) (worker : Worker)
    (unit : Nat) (queue : List Nat) :
    Preserves (fun w : World => Tail records w.ambient.hidden)
      (resolveUnit worker unit queue : Leanux.M Nat) := by
  apply liftAmbient_contract (AmbientM.resolveUnit worker unit queue) (fun a=>Tail records a.hidden) (fun _ a=>Tail records a.hidden)
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  have same := (hoare_iff_run _ _ _).mp
    (resolveUnit_hidden (records := before.hidden) worker unit queue)
      before value after rfl run
  simpa only [same] using pre

theorem clearSelect_retains (records : List HiddenRecord) :
    Preserves (fun w : World => Tail records w.ambient.hidden) Index.clearWorkerSelect := by
  unfold Index.clearWorkerSelect
  apply preserves_bind (native_product records getDev (native_getDev records))
  intro d
  split
  · apply preserves_bind (peekUnit_retains records .clearPeerWorker)
    intro chosen
    cases chosen
    · exact preserves_pure _
    · exact resolveUnit_retains records _ _ _
  · apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run

theorem runWorker_strict (records : List HiddenRecord) (worker : Worker)
    (body : Leanux.M Unit)
    (keep : Preserves (fun w : World => Tail records w.ambient.hidden) body) :
    Hoare (Env.runWorker worker body)
      (fun w => Tail records w.ambient.hidden)
      (fun _ w => StrictTail records w.ambient.hidden) := by
  have stop : Hoare (do let _ ← (hidden (.sectionStop worker) : Leanux.M (List UInt8)); pure ())
      (fun w => Tail records w.ambient.hidden)
      (fun _ w => StrictTail records w.ambient.hidden) :=
    hoare_bind _ _ (hidden_after_product_tail (.sectionStop worker) records)
      (fun _=>preserves_pure _)
  by_cases net : (worker == .netRx) = true
  · simp only [Env.runWorker,net,↓reduceIte]
    apply hoare_bind _ _ (hoare_consequence
      (hidden_after_product_tail (.sectionStart worker) records)
        (fun _ h=>h) (fun _ _ h=>strict_tail h))
    intro _
    apply hoare_bind _ _ (modifyAmbient_hidden records (fun a=>{a with netRxSection:=a.netRxSections}) (fun _=>rfl))
    intro _
    apply hoare_bind _ _ keep
    intro _
    exact hoare_bind _ _ (modifyAmbient_hidden records (fun a=>{a with netRxSection:=0}) (fun _=>rfl)) (fun _=>stop)
  · simp only [Env.runWorker,net]
    apply hoare_bind _ _ (hoare_consequence
      (hidden_after_product_tail (.sectionStart worker) records)
        (fun _ h=>h) (fun _ _ h=>strict_tail h))
    intro _
    exact hoare_bind _ _ keep (fun _=>stop)

theorem clearWorker_strict (records : List HiddenRecord) :
    Hoare Env.runOneClearWorker
      (fun w => Tail records w.ambient.hidden)
      (fun _ w => StrictTail records w.ambient.hidden) := by
  rw [Index.runOneClearWorker_select_source]
  apply hoare_bind _ _ (clearSelect_retains records)
  intro pid
  apply hoare_bind _ _ (native_product records _ (native_modifyDev records _))
  intro _
  exact runWorker_strict records .clearPeerWorker _ (native_product records _
    (clearCallback_retains records pid))

end Leanux.Proofs.WG.Progress.RecordSuffix
