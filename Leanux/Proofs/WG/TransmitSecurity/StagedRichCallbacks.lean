import Leanux.Proofs.WG.TransmitSecurity.StagedRichSourceOrigins
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalCallbackProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietEffects

/-! Existing staged origins at the actual enriched callback cuts. New quiet
receipts extend the full journal; they never renumber an earlier birth. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
open HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem rich_selection (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => Carrier h w) Safe (CausalJournal.selection pid)
      (fun value h w _ => Carrier h w ∧ ∀ peer key, value = some (peer,key) → Saved h pid peer w) := by
  let body := Take.observed Event.stagingTaken pid
  have appends : StateAppends body := by
    unfold body Take.observed
    exact StateAppends.bind ((StateAppends.lift _).receiptWGObserved _) (fun _ => StateAppends.lift _)
  have frame : StateHistoryFrame selection? body := by
    intro w a h
    exact (congrArg Prod.snd (Take.observed_projects Event.stagingTaken selection? (fun _ => rfl) pid w a h)).symm
  have history := quiet_history appends frame
  have erased := Take.observed_erases Event.stagingTaken pid
  intro w a h before
  obtain ⟨suffix,position,safe,_⟩ := history w a h before.2
  change (runWGPrefix body w a h).2 = h ++ suffix at position
  change Safe (runWGPrefix body w a h).2 at safe
  have equation := runWGPrefix_receiptWGObserved body
    (fun run => Event.old (.responder (.selected pid run))) w a h
  change runWGPrefix (CausalJournal.selection pid) w a h = _ at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : runWGPrefix body w a h with
  | mk result tail =>
    rw [run] at position safe
    simp only [runWGPrefix,runStatePrefix] at run
    rw [run]
    cases result with
    | error stop => exact ⟨suffix,position,safe,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      change tail = h ++ suffix at position
      change Safe tail at safe
      have native : ((HandshakeSecurity.Responder.selectionPrefix pid).run w).run a = .ok ((value,v),b) :=
        (erased w a h).symm.trans (congrArg Prod.fst run)
      let receipt : WGRunWitness (Option (Peer × Option KeypairId)) := ⟨value,w,v,a,b⟩
      have inv : Inv tail w := by rw [position]; exact before.1.append suffix
      obtain ⟨next,checked,saved⟩ := selection_origin pid receipt native inv
      have good := safe.emit checked
      refine ⟨suffix ++ [.old (.responder (.selected pid receipt))],?_,good,⟨next.append _,good⟩,?_⟩
      · change tail ++ [_] = h ++ (suffix ++ [_])
        rw [position,List.append_assoc]
      · intro peer key selected
        exact (saved peer key selected).append _

theorem rich_restore (pid : PeerId) (peer : Peer) :
    StatePrefixEnsures (Held pid peer) Safe (stagedRestore pid peer.staged)
      (fun _ h w _ => Carrier h w) := by
  have captured : StatePrefixEnsures (Held pid peer) Safe
      (captureWGObserved (liftWGPrefix (HandshakeSecurity.NonceRejection.restore pid peer.staged)))
      (fun _ h w _ => Carrier h w) :=
    (held_restore pid peer).captureWGObserved.consequence
      (fun _ _ _ before => before) (fun _ _ _ _ after => by
        obtain ⟨rfl,rfl,carrier,_⟩ := after
        exact carrier)
  unfold stagedRestore Restore.observed receiptWGObserved
  exact StatePrefixEnsures.bind captured (fun r =>
    StatePrefixEnsures.bind (state_emit (.stagedRestored ⟨pid,peer.staged,r⟩) True.intro)
      (fun _ => state_pure r.value))

theorem rich_queued (pid : PeerId) (retry : Bool) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid retry) :=
  state_quiet
    (CallbackQuiet.queued selection? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid retry).1
    (CallbackQuiet.queued selection? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid retry).2
    (RetirementSecurity.NestedPeerRelease.projects_erases selection?
      (CallbackQuiet.queued_projects selection? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid retry)
      (erasesStatePrefix_lift _))
    (fun _ => Native.queued pid retry)

theorem rich_create (pid : PeerId) (items : List SkbId) : StateSafe (CausalJournal.create pid items) :=
  state_quiet
    (CallbackQuiet.create selection? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items).1
    (CallbackQuiet.create selection? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items).2
    (RetirementSecurity.NestedPeerRelease.projects_erases selection?
      (HandshakeSecurity.ExchangeCausal.Callbacks.create selection? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items)
      (erasesStatePrefix_lift _))
    (fun _ => Native.create pid items)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
