import Leanux.Proofs.WG.RetirementSecurity.RxEnqueueHolders
import Leanux.Proofs.WG.RetirementSecurity.OwnershipSourceFrames
import Leanux.Proofs.WG.RetirementSecurity.TxPublishHolders

/-! Pure-IRQ RX publication changes packet state and NAPI bookkeeping while
retaining all key holders. Its freshly acquired peer reference supplies the
matching put and prevents removal of a holder group. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem ownershipPoints_holderStore (action : WG.M α) (same : SameView holderStore action) :
    SameView ownershipPointView action := by
  apply same.of_factor
    (fun s =>
      ((fun id => (s.1.bind fun fields => fields.2 id).map fun k => (k.internalId,k.refcount)),
       s.1.isSome,(fun pid => (s.2.1.bind fun peers => peers[pid]?).map peerOwnership),s.2.2))
    ownershipPointView
  intro w
  unfold ownershipPointView keyReferenceView holderStore
  cases device : w.dev <;> simp [keyAt,ownershipAt,peerAt,Origins.view,peersAt,packetKeyWords,device]

theorem rx_publication_middle_ownership (pid : PeerId) (id : SkbId) (state : PacketState) :
    SameView ownershipPointView (Queues.RxCredits.publicationMiddle pid id state) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  have mark : Preserves (fun w => ownershipPointView w = initial)
      (setRxSkb id (fun p => {p with state})) :=
    (ownershipPoints_holderStore _ (setRx_holderStore id (fun p => {p with state}) (fun _ => rfl))).wp
      (fun s => s = initial)
  unfold Queues.RxCredits.publicationMiddle
  simp only [invariant]
  repeat' first
    | (rx_retention_head setRxSkb; exact mark)
    | ownership_source_step initial

theorem HolderAccount.publish_rx (account : HolderAccount temporary w)
    (id : SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerRx (pure () : WG.M Unit) id state).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  rw [Queues.RxCredits.publication_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨packet,u,aa,readRun,pid,t,ab,ownerRun,_,s,ac,getRun,_,e,ae,middleRun,putRun⟩ := run
  have hu : HolderAccount temporary u :=
    (Packets.getRxSkb_current id w u packet a aa readRun).1 ▸ account
  have ht := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerDeref_preserves (.keypair packet.keypair) (HolderAccount temporary))
    u aa pid t ab hu ownerRun
  obtain ⟨hs,p,found,positive⟩ := ht.peer_get pid ab ac getRun
  have own := (ProjectedAction.iff_run_ambient _ _ _).mp
    (rx_publication_middle_ownership pid id state) s ac () e ae middleRun
  have he := hs.points own
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.RxCredits.publicationMiddle_frame pid id state) s ac () e ae middleRun
  have count : (peerAt e pid).map (·.refcount) = some p.refcount := by
    have cell := congrFun (congrArg Prod.snd same) pid
    have equation := congrArg (Option.map (fun fields => fields.2.1)) cell
    simp only [Queues.RxCredits.peerView,Option.map_map,Function.comp_def] at equation
    change (peerAt e pid).map (·.refcount) = (peerAt s pid).map (·.refcount) at equation
    simpa only [found,Option.map_some] using equation
  have ready : PeerReleaseReady pid e := by
    intro q resident final
    rw [resident] at count
    simp only [Option.map_some,Option.some.injEq] at count
    omega
  exact he.peer_put ready ae b putRun

end Leanux.Proofs.WG.RetirementSecurity
