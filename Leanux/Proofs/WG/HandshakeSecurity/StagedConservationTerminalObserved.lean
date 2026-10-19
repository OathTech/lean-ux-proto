import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTerminalReceipt

/-! Native TX creation and DEAD disposal emit per-packet terminal receipts,
retaining all prior lifetime events. Reference repayments are separately
observed, and crypted completion cleanup does not acquire a drop label. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects

def freeObserved (encode : TxDisposition.Event → E) (decode : E → Option TxDisposition.Event)
    (record : Receipt → E) (reason : Reason) (skb : SkbId) : PrefixM E Unit :=
  observed record
    (focusPrefix encode decode (StagedDisposal.TxSource.native.access (freeTxSkbPrefix skb))) reason skb

def createObserved (encode : TxDisposition.Event → E) (decode : E → Option TxDisposition.Event)
    (disposal : StagedDisposal.Event → E) (record : Receipt → E)
    (pid : PeerId) (item : List SkbId) : PrefixM E Unit :=
  createWith (StagedDisposal.TxSource.observed encode decode disposal)
    (freeObserved encode decode record) pid item

def deadObserved (encode : TxDisposition.Event → E) (decode : E → Option TxDisposition.Event)
    (disposal : StagedDisposal.Event → E) (record : Receipt → E)
    (pid : PeerId) (item : List SkbId) (head : DataPacket) : PrefixM E Bool :=
  disposeWith (StagedDisposal.TxSource.observed encode decode disposal)
    (freeObserved encode decode record (.deadBatch pid head)) pid item head.keypair

theorem freeObserved_erases (encode : TxDisposition.Event → E)
    (decode : E → Option TxDisposition.Event) (record : Receipt → E)
    (reason : Reason) (skb : SkbId) :
    ErasesPrefix (freeObserved encode decode record reason skb) (liftWG (freeTxSkb skb)) := by
  apply observed_erases
  exact focusPrefix_erases encode decode
    (liftWGObserver_erases
      (focusStatePrefix_erases TxDisposition.Event.access TxDisposition.accessEvent
        (freeTxSkbPrefix_erases skb)))

theorem freeObserved_projects (ρ : E → Option F)
    (eg : TxDisposition.Event → E) (dg : E → Option TxDisposition.Event)
    (et : TxDisposition.Event → F) (dt : F → Option TxDisposition.Event)
    (enc : ∀ event, ρ (eg event) = some (et event))
    (dec : ∀ event, dg event = (ρ event).bind dt)
    (record : Receipt → E) (quiet : ∀ event, ρ (record event) = none)
    (reason : Reason) (skb : SkbId) :
    ProjectsPrefix ρ id (freeObserved eg dg record reason skb)
      (focusPrefix et dt (StagedDisposal.TxSource.native.access (freeTxSkbPrefix skb))) :=
  observed_projects record ρ quiet _ _ (CompletionEffects.focus_matching ρ eg dg et dt enc dec _) reason skb

variable (ρ : E → Option F)
  (eg : TxDisposition.Event → E) (dg : E → Option TxDisposition.Event)
  (et : TxDisposition.Event → F) (dt : F → Option TxDisposition.Event)
  (enc : ∀ event, ρ (eg event) = some (et event))
  (dec : ∀ event, dg event = (ρ event).bind dt)
  (inverse : ∀ event, dt (et event) = some event)
  (disposal : StagedDisposal.Event → E) (disposalQuiet : ∀ event, ρ (disposal event) = none)
  (record : Receipt → E) (quiet : ∀ event, ρ (record event) = none)

include enc dec inverse disposalQuiet quiet

theorem createObserved_projects (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ρ id (createObserved eg dg disposal record pid item)
      (focusPrefix et dt (TxDisposition.create pid item)) := by
  rw [← StagedDisposal.TxSource.create_native,
    ← StagedDisposal.TxSource.create_focus et dt inverse
      StagedDisposal.TxSource.native StagedDisposal.TxSource.native_appends]
  apply create_projects ρ
    (StagedDisposal.TxSource.observed_matching ρ eg dg et dt enc dec inverse disposal disposalQuiet)
  exact freeObserved_projects ρ eg dg et dt enc dec record quiet

theorem deadObserved_projects (pid : PeerId) (item : List SkbId) (head : DataPacket) :
    ProjectsPrefix ρ id (deadObserved eg dg disposal record pid item head)
      (focusPrefix et dt (TxDisposition.dispose pid item head.keypair)) := by
  rw [← StagedDisposal.TxSource.dispose_native,
    ← StagedDisposal.TxSource.dispose_focus et dt inverse
      StagedDisposal.TxSource.native StagedDisposal.TxSource.native_appends]
  apply dispose_projects ρ
    (StagedDisposal.TxSource.observed_matching ρ eg dg et dt enc dec inverse disposal disposalQuiet)
  exact freeObserved_projects ρ eg dg et dt enc dec record quiet (.deadBatch pid head)

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Terminal
