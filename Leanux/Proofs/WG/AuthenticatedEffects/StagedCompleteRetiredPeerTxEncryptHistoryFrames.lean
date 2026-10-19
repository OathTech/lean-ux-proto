import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxEncryptFrames

/-! The actual encrypt iteration retains the fixed receive-history cut through
its real NAPI call, then through encryption, publication and rescheduling. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ExactAt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem encrypt_normal (hi : ExactAt initial loans before h w)
    (run : runPrefix RxHistory.encryptIteration w h = (.ok (result,v),k)) :
    ExactAt initial loans before k v := by
  unfold RxHistory.encryptIteration at run
  obtain ⟨item,polled,polledHistory,pollRun,rest⟩ := DecryptIteration.bind_normal run
  have first := (ExactAt.mixed _ _ (liftWGObserver_erases (erasesStatePrefix_lift TxRing.pollSource))
    (fun _ => Encrypt.lift_boundary (Encrypt.native_boundary HolderEncrypt.poll_fields)) w h hi).choose_spec.2.2
  change runPrefix (RxHistory.mixed (liftWGObserver (liftStatePrefix TxRing.pollSource))) w h = _ at pollRun
  rw [pollRun] at first
  obtain ⟨u,received,receivedHistory,napiRun,tailRun⟩ := DecryptIteration.bind_normal rest
  cases u
  have middle := (softirq_preserves initial loans before polled polledHistory first).choose_spec.2.2
  rw [napiRun] at middle
  have last := (ExactAt.mixed _ _ (RxWorkers.encryptTail_erases item)
    (fun _ => Encrypt.tail_boundary item) received receivedHistory middle).choose_spec.2.2
  simpa only [tailRun] using last

theorem encrypt_preserves (initial : RxCredits.Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) RxHistory.encryptIteration := by
  apply NapiCarrier.normal_spec
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptIteration_appends)
  intro w h x v hi run
  exact encrypt_normal hi (Prod.ext run rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ExactAt
