import Leanux.Proofs.WG.TransmitSecurity.CompletionOriginHistory
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginWorkerFrames

/-! Separate source and history frames for the completion-origin carrier.
Only the actual completion cut can append a completion entry. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000

def txEntry? (e : TxDisposition.Event) : Option (List SkbId) := entry? (.disposition e)

open Lean Meta Elab Tactic in
elab "completion_frame_access" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let some last := target.getAppArgs.back? | throwError "not an action contract"
  let action := last.consumeMData.headBeta
  unless action.isAppOf ``TxDisposition.nativeAccess do throwError "not a native access"

macro "completion_entry_frame_step" : tactic => `(tactic| first
  | (completion_frame_access; change HistoryFrame _ (focusPrefix _ _ _); exact focusPrefix_other _ _ _ (fun _ => rfl) _)
  | with_reducible exact HistoryFrame.lift _ _
  | with_reducible exact HistoryFrame.pure _ _
  | with_reducible exact HistoryFrame.emit _ rfl
  | with_reducible apply HistoryFrame.bind
  | with_reducible apply HistoryFrame.forIn
  | (with_reducible intro x; try dsimp only)
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

macro "completion_entry_appends_step" : tactic => `(tactic| first
  | (completion_frame_access; change Appends (focusPrefix _ _ _); exact Appends.focus _ _ _)
  | with_reducible exact Appends.lift _
  | with_reducible exact Appends.pure _
  | (change Appends (emitPrefix _); exact fun _ _ => ⟨[_],rfl⟩)
  | with_reducible apply Appends.bind
  | with_reducible apply Appends.forIn
  | (with_reducible intro x; try dsimp only)
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem create_frame (pid : PeerId) (items : List SkbId) :
    HistoryFrame txEntry? (TxDisposition.create pid items) := by
  unfold TxDisposition.create TxDisposition.enqueue TxDisposition.enqueueCore TxDisposition.publish
  repeat' completion_entry_frame_step

theorem create_appends (pid : PeerId) (items : List SkbId) : Appends (TxDisposition.create pid items) := by
  unfold TxDisposition.create TxDisposition.enqueue TxDisposition.enqueueCore TxDisposition.publish
  repeat' completion_entry_appends_step

theorem drop_frame (pid : PeerId) (items : List SkbId) :
    HistoryFrame txEntry? (TxDisposition.drop pid items) := by
  unfold TxDisposition.drop
  repeat' completion_entry_frame_step

theorem drop_appends (pid : PeerId) (items : List SkbId) : Appends (TxDisposition.drop pid items) := by
  unfold TxDisposition.drop
  repeat' completion_entry_appends_step

theorem dispose_frame (pid : PeerId) (items : List SkbId) (key : KeypairId) :
    HistoryFrame txEntry? (TxDisposition.dispose pid items key) := by
  unfold TxDisposition.dispose
  repeat' completion_entry_frame_step

theorem dispose_appends (pid : PeerId) (items : List SkbId) (key : KeypairId) :
    Appends (TxDisposition.dispose pid items key) := by
  unfold TxDisposition.dispose
  repeat' completion_entry_appends_step

theorem with_native {g : PrefixM Completion.Event α} {a : Leanux.M α}
    (good : PrefixPreserves (fun h _ => Good bank h) (Good bank) g)
    (erases : ErasesPrefix g a)
    (frame : Preserves (fun w : World => PacketOrigins.Inv bank w.wg) a) :
    PrefixPreserves (Inv bank) (Good bank) g := by
  intro w h before
  obtain ⟨suffix,extension,safe,after⟩ := good w h before.2
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    exact ⟨(hoare_iff_run _ _ _).mp frame w out.1 out.2 before.1
      ((erases w h).symm.trans result),by simpa only [result] using after⟩

theorem access {a : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix a native)
    (frame : Preserves (PacketOrigins.Inv bank) native) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.access a) :=
  with_native (access_good a) (Completion.access_erases erases)
    (PublicationPoll.native_product _ _ frame)

theorem lift_safe (a : Leanux.M α)
    (frame : Preserves (fun w : World => PacketOrigins.Inv bank w.wg) a) :
    PrefixPreserves (Inv bank) (Good bank) (liftPrefix a) :=
  with_native (lift_good a) (erasesPrefix_lift a) frame

theorem peer_modify (pid : PeerId) (f : Peer → Peer) :
    Preserves (PacketOrigins.Inv bank) (do setPeer pid (f (← getPeer pid))) := by
  apply preserves_bind (PacketOrigins.NativeFrames.read_peer pid)
  intro p
  unfold setPeer
  exact PacketOrigins.frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl))

theorem drop (pid : PeerId) (items : List SkbId) :
    PrefixPreserves (Inv bank) (Good bank)
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop pid items)) := by
  apply with_native
    (quiet (Appends.focus _ _ _) (focus_frame _ _ _ _ (drop_appends pid items) (drop_frame pid items)))
    (focusPrefix_erases _ _ (TxDisposition.drop_erases pid items))
  apply PublicationPoll.native_product
  apply preserves_bind (PacketOrigins.NativeFrames.read_peer pid)
  intro p
  exact peer_modify pid (fun q => {p with txQueue := q.txQueue.dropPeeked})

theorem dispose (pid : PeerId) (items : List SkbId) (key : KeypairId) :
    PrefixPreserves (Inv bank) (Good bank)
      (focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose pid items key)) := by
  apply with_native
    (quiet (Appends.focus _ _ _) (focus_frame _ _ _ _ (dispose_appends pid items key) (dispose_frame pid items key)))
    (focusPrefix_erases _ _ (TxDisposition.dispose_erases pid items key))
  apply PublicationPoll.native_product
  unfold TxDisposition.disposeSource
  repeat' origin_staging_frame

theorem complete (pid : PeerId) (items : List SkbId) (cert : Certificate bank items) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.complete pid items) :=
  with_native (complete_good pid items cert) (Completion.complete_erases pid items)
    (PublicationPoll.native_product _ _ (PacketOrigins.frame
      (PacketOrigins.snapshot_wire (RetirementSecurity.createDataDone_cryptWire pid items))))

theorem branch (decision : Decision) (value : Bool) :
    PrefixPreserves (Inv bank) (Good bank) (liftPrefix (liftWG (Leanux.branch decision value))) := by
  apply lift_safe
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run
  exact before

theorem stop (s : String) :
    PrefixPreserves (Inv bank) (Good bank) (liftPrefix (liftWG (invariant s : WG.M α))) := by
  apply lift_safe
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run

end Leanux.Proofs.WG.TransmitSecurity.CompletionOrigin
