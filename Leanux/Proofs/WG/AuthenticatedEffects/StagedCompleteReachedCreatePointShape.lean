import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointSource

/-! A finite original-create vocabulary. The canonical witness fixes each
native argument and branch order. Remaining release/repayment/free interiors
are named children, never arbitrary extensional factors. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
open CausalJournal
set_option maxHeartbeats 600000

abbrev History := List CausalJournal.Event
abbrev Result (α : Type) := Except Stop (α × World)

inductive Fault where
  | empty
  | unqueued

def Fault.text : Fault → String
  | .empty=>"an empty ring item"
  | .unqueued=>"an item for the tx worker that is not on its peer's tx_queue"

inductive Atom : Type → Type 1 where
  | fault (α : Type) (kind : Fault) : Atom α
  | branch (site : Leanux.Decision) (value : Bool) : Atom Bool
  | peer (pid : PeerId) : Atom Peer
  | packet (id : SkbId) : Atom DataPacket
  | owner (kid : KeypairId) : Atom PeerId
  | acquire (pid : PeerId) : Atom Unit
  | mark (id : SkbId) (state : PacketState) : Atom Unit
  | queue (pid : PeerId) (peer : Peer) (items : List SkbId) : Atom Unit
  | device : Atom Device
  | nextCpu (cpu : Int) : Atom Int
  | lastCpu (cpu : Int) : Atom Unit
  | queueEncrypt : Atom Unit
  | ring (items : List SkbId) : Atom Unit
  | chooseCpu (pid : PeerId) : Atom Nat
  | peekWork (pid : PeerId) : Atom Bool
  | recordWork (pid : PeerId) : Atom Unit
  | appendWork (pid : PeerId) : Atom Unit
  | event (event : TxDisposition.Event) : Atom Unit

def Atom.action : Atom α → PrefixM CausalJournal.Event α
  | .fault _ kind=>Admission.actualOps.step (invariant kind.text)
  | .branch site value=>Admission.actualOps.step (Leanux.branch site value)
  | .peer pid=>Admission.actualOps.access (getPeerMixed pid)
  | .packet id=>Admission.actualOps.access (getTxSkbPrefix id)
  | .owner kid=>Admission.actualOps.access (peerDerefPrefix (.keypair kid))
  | .acquire pid=>Admission.actualOps.access (peerGetMixed pid)
  | .mark id state=>Admission.actualOps.access (setTxSkbPrefix id fun p=>{p with state})
  | .queue pid value items=>queueWrite pid value items
  | .device=>Admission.actualOps.step getDev
  | .nextCpu cpu=>Admission.actualOps.step (cpumaskNextOnlineFrom cpu)
  | .lastCpu cpu=>Admission.actualOps.step (modifyDev fun d=>{d with encryptLastCpu:=cpu})
  | .queueEncrypt=>Admission.actualOps.step (queueDeviceWork .encryptWorker)
  | .ring items=>Admission.actualOps.step (modifyDev fun d=>{d with encryptQueue:=d.encryptQueue.produce items})
  | .chooseCpu pid=>Admission.actualOps.access (cpumaskChooseOnlinePrefix pid)
  | .peekWork pid=>Admission.actualOps.step (peekQueuedUnit .txWorker pid)
  | .recordWork pid=>Admission.actualOps.step (recordQueued .txWorker pid)
  | .appendWork pid=>Admission.actualOps.step (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]})
  | .event value=>Admission.actualOps.event value

inductive Child : {α : Type} → PrefixM CausalJournal.Event α → Type 1 where
  | release (pid : Option PeerId) : Child (Admission.actualOps.release pid)
  | repay (kid : Option KeypairId) : Child (Admission.actualOps.access (keypairPutPrefix kid false))
  | free (reason : Terminal.Reason) (id : SkbId) : Child (CreateDisposal.free reason id)

inductive Label where
  | create (pid : PeerId) (items : List SkbId)
  | admission (pid : PeerId) (items : List SkbId)
  | enqueue (pid : PeerId) (items : List SkbId)
  | before (pid : PeerId) (items : List SkbId)
  | install (pid : PeerId) (peer : Peer) (items : List SkbId)
  | ring (items : List SkbId)
  | borrow (items : List SkbId)
  | publication (items : List SkbId) (state : PacketState)
  | published (pid : PeerId) (first : SkbId) (state : PacketState)
  | schedule (pid : PeerId)
  | tail (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int)

inductive Shape : {α : Type} → PrefixM CausalJournal.Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | atom (token : Atom α) : Shape token.action
  | child (token : Child action) : Shape action
  | bind {body : PrefixM CausalJournal.Event α} {next : α → PrefixM CausalJournal.Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (body : Shape action) : Shape action

noncomputable def listShape (xs : List α) (initial : σ)
    (body : α → σ → PrefixM CausalJournal.Event (ForInStep σ))
    (shapes : ∀ value acc, Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive:=fun remaining=>∀ acc,Shape (forIn remaining acc body))
    (fun acc=>.pure acc)
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision=>match decision with
        | .done final=>.pure final
        | .yield next=>ih next)) xs initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
