import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.WG.RetirementSecurity.CreateRefusalReceipts

/-! The actual createData admission prefix, before either successful-return
test or refusal cleanup. The factor exposes the same source continuation;
it adds no receipt and does not replace the final journal's source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def front (o : TxSource.Ops E) (pid : PeerId) (items : List SkbId) : PrefixM E Int := do
  if ← o.step (branch .createDataDead (← o.access (getPeerMixed pid)).isDead) then
    return -EINVAL
  let ret ← o.enqueue pid items
  if ← o.step (branch .createDataEpipe (ret == -WG.EPIPE)) then TxSource.publish o items .dead
  return ret

def tail (o : TxSource.Ops E) (free : Terminal.Reason → SkbId → PrefixM E Unit)
    (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int) : PrefixM E Unit := do
  if ← o.step (branch .createDataOk (ret == 0)) then return
  if ← o.step (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  o.access (keypairPutPrefix (some (← o.access (getTxSkbPrefix first)).keypair) false)
  o.release (some pid)
  for id in items do free (.createRefused pid ret) id

theorem create_factor (o : TxSource.Ops E)
    (free : Terminal.Reason → SkbId → PrefixM E Unit) (pid : PeerId) (items : List SkbId) :
    Terminal.createWith o free pid items = (do
      let some first := items.head? | o.step (invariant "an empty ring item")
      let ret ← front o pid items
      tail o free pid items first ret) := by
  simp only [Terminal.createWith,front,tail,bind_assoc,TxDisposition.bind_ite,pure_bind]
  rfl

def actualOps : TxSource.Ops CausalJournal.Event :=
  TxSource.observed CausalJournal.txEvent CausalJournal.txEvent? CausalJournal.Event.stagedDisposal

def actual (pid : PeerId) (items : List SkbId) := front actualOps pid items

theorem final_factor (pid : PeerId) (items : List SkbId) :
    Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items = (do
      let some first := items.head? | actualOps.step (invariant "an empty ring item")
      let ret ← actual pid items
      tail actualOps (Terminal.freeObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.terminalDrop) pid items first ret) :=
  create_factor actualOps _ pid items

private theorem projected_erases {ρ : E → Option F} {g : PrefixM E α} {t : PrefixM F α}
    (projects : ProjectsPrefix ρ id g t) (erases : ErasesPrefix t native) : ErasesPrefix g native := by
  intro w h
  have same := congrArg Prod.fst (projects w h)
  simp only [id_eq,Prod.eta] at same
  cases result : (runPrefix g w h).1 <;>
    simpa only [result,Except.map] using same.symm.trans (erases w (h.filterMap ρ))

theorem publication_erases (items : List SkbId) (state : PacketState) :
    ErasesPrefix (TxSource.publish actualOps items state) (liftWG (enqueuePerPeerTx items state)) := by
  apply projected_erases (TxSource.publish_observed_projects CausalJournal.old?
    CausalJournal.txEvent CausalJournal.txEvent? Journal.Event.disposition Journal.disposition?
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    CausalJournal.Event.stagedDisposal (fun _ => rfl) items state)
  exact focusPrefix_erases _ _ (TxDisposition.publish_erases items state)

theorem actual_erases (pid : PeerId) (items : List SkbId) :
    ErasesPrefix (actual pid items) (liftWG (RxCredits.createReturnSource pid items)) := by
  have step {α : Type} (action : WG.M α) : ErasesPrefix (actualOps.step action) (liftWG action) :=
    focusPrefix_erases _ _ (erasesPrefix_lift _)
  have access (peer : PeerId) : ErasesPrefix (actualOps.access (getPeerMixed peer)) (liftWG (getPeer peer)) :=
    focusPrefix_erases _ _ (TxDisposition.nativeAccess_erases (getPeerMixed_erases peer))
  have enqueue (peer : PeerId) (batch : List SkbId) :
      ErasesPrefix (actualOps.enqueue peer batch) (liftWG (enqueuePerDeviceAndPeer peer batch)) :=
    focusPrefix_erases _ _ (TxDisposition.enqueue_erases peer batch)
  unfold actual front RxCredits.createReturnSource RxCredits.createPublishReturn
  simp only [liftWG_bind,liftWG_pure,apply_ite]
  repeat' first
    | with_reducible exact publication_erases _ _
    | exact enqueue _ _
    | exact access _
    | exact step _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split


end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
