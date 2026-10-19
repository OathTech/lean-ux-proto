import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxSelectionFrames
import Leanux.Proofs.WG.Queues.TxHolderAccount
import Leanux.Proofs.WG.RetirementSecurity.TxWorkerHolders

/-! The actual TX drop transfers one lasting batch reference to its local
loan. The original disposal suffix frees the batch and pays that same loan;
final peer deletion is allowed on normal return. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders RetirementSecurity

theorem Upper.take_tx (upper : Upper holders carriers loans w)
    (selected : TxSelected holders.tx pid chosen rest) :
    Upper (holders.withoutTx rest) carriers (chosen.owner :: loans) w := by
  apply upper.relabel
  apply List.perm_iff_count.mpr
  intro owner
  have count := List.Perm.count_eq (selected.perm.map TxHandoff.owner) owner
  simp only [List.map_cons,List.count_cons] at count
  simp only [owners,withoutTx,List.count_append,List.count_cons]
  omega

theorem Account.tx_select (account : Account holders carriers loans w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (peek : p.txQueue.peeked = some item) (a b : Ambient)
    (run : ((txDropSource pid).run w).run a = .ok (((),v),b)) :
    ∃ chosen rest, TxSelected holders.tx pid chosen rest ∧ chosen.item = item ∧
      Account (holders.withoutTx rest) carriers (chosen.owner :: loans) v := by
  have queue : handoffTxView w pid = some p.txQueue.all := by simp [handoffTxView,device,found]
  obtain ⟨chosen,rest,selected,itemEq,_,_,_⟩ := account.funded.tx_selected (item := item) queue
    (by simp [PrevQueue.all,peek])
  obtain ⟨other,q,otherDevice,otherFound,_,state⟩ := txDrop_effect pid a b run
  have eq := Option.some.inj (device.symm.trans otherDevice)
  subst other
  have eq := Option.some.inj (found.symm.trans otherFound)
  subst q
  have input := account.funded.tx_input account.stable selected
  have kept := (pinned_const
    _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.queue_update)
    input device found p.txQueue.dropPeeked
  have stable : StableRx carriers v := by simpa only [state,replacePeer] using kept.2
  have funded : CarrierState carriers ((holders.withoutTx rest).owners ++ chosen.owner :: loans) v := by
    have shifted := WorkReservations.carrier_loans_perm kept.1 List.perm_middle.symm
    simpa only [state,replacePeer] using shifted
  have aligned : (holders.withoutTx rest).Aligned v := by
    rw [state]
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [withoutTx,replacePeer,passiveView,device] using account.funded.aligned.base
    · intro out outDevice
      have outEq : out = {d with peers := d.peers.insert pid {p with txQueue := p.txQueue.dropPeeked}} := by
        simpa [replacePeer] using outDevice.symm
      subst out
      exact account.funded.aligned.send d device
    · simpa [withoutTx,replacePeer,device] using account.funded.aligned.clear
    · intro owner batches present
      by_cases eq : pid = owner
      · subst owner
        have batchEq : batches = p.txQueue.dropPeeked.all := by
          simpa [handoffTxView,replacePeer] using present.symm
        have dropEq : p.txQueue.dropPeeked.all = (holders.withoutTx rest).items pid := by
          have shape := account.funded.aligned.tx pid p.txQueue.all queue
          rw [selected.head] at shape
          have dropped := congrArg List.tail shape
          simpa [PrevQueue.all,PrevQueue.dropPeeked,peek] using dropped
        exact batchEq.trans dropEq
      · have old : handoffTxView w owner = some batches := by
          simpa [handoffTxView,replacePeer,device,Std.TreeMap.getElem?_insert,eq] using present
        rw [selected.other owner (Ne.symm eq)]
        exact account.funded.aligned.tx owner batches old
    · exact account.funded.aligned.cursor7
    · exact account.funded.aligned.cursor8
  have peers : peerView v = peerView w := by
    rw [state]
    unfold peerView replacePeer
    simp only [device,Option.map_some,Option.bind_some]
    congr 1
    funext owner
    by_cases eq : pid = owner <;> simp_all [Std.TreeMap.getElem?_insert]
  exact ⟨chosen,rest,selected,itemEq,⟨aligned,funded⟩,
    (account.upper.take_tx selected).peer_view peers,stable⟩

theorem free_tx_peers (id : SkbId) : SameView peerView (freeTxSkb id) := by
  intro initial
  unfold freeTxSkb
  apply hoare_liftSkb
  intro w d store hi device
  simpa only [peerView,device,Option.map_some,Option.bind_some] using hi

theorem free_tx_holders (id : SkbId) (initial : WGWorld) : Preserves (Frame initial) (freeTxSkb id) := by
  unfold freeTxSkb
  apply hoare_liftSkb
  intro w d store hi device
  exact hi.trans (by constructor <;> first
    | (simp [passiveView,sendView,device])
    | (intro q xs h; simpa [handoffTxView,device] using h))

theorem free_tx_list_peers (item : List SkbId) : SameView peerView (TxDisposition.freeList item) := by
  induction item with
  | nil => simpa only [TxDisposition.freeList_nil] using SameView.pure peerView ()
  | cons first rest ih =>
    rw [TxDisposition.freeList_cons]
    exact (free_tx_peers first).bind (fun _ => ih)

theorem free_tx_list_holders (item : List SkbId) (initial : WGWorld) :
    Preserves (Frame initial) (TxDisposition.freeList item) := by
  induction item with
  | nil => simpa only [TxDisposition.freeList_nil] using (preserves_pure () : Preserves (Frame initial) (pure ()))
  | cons first rest ih =>
    rw [TxDisposition.freeList_cons]
    exact preserves_bind (free_tx_holders first initial) (fun _ => ih)

theorem Account.free_tx_list (account : Account holders carriers loans w)
    (item : List SkbId) (a b : Ambient)
    (run : ((TxDisposition.freeList item).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v := by
  have kept := (hoare_iff_run_ambient _ _ _).mp (TxReservation.freeList_preserves item)
    w a () v b ⟨account.funded.carriers,account.stable⟩ run
  have frame := (hoare_iff_run_ambient _ _ _).mp (free_tx_list_holders item w)
    w a () v b (Frame.refl w) run
  exact ⟨⟨account.funded.aligned.frame frame,kept.1⟩,
    account.upper.peer_view ((ProjectedAction.iff_run_ambient _ _ _).mp
      (free_tx_list_peers item) w a () v b run),kept.2⟩

theorem Account.tx_dispose (account : Account holders carriers (owner :: loans) w)
    (item : List SkbId) (key : KeypairId) (a b : Ambient)
    (run : ((TxDisposition.disposeSource owner.slot item key).run w).run a = .ok ((result,v),b)) :
    result = true ∧ Account holders carriers loans v := by
  have factor : TxDisposition.disposeSource owner.slot item key = (do
      TxDisposition.freeList item
      keypairPut (some key) false
      peerPut (some owner.slot)
      pure true : WG.M Bool) := by
    simp only [TxDisposition.disposeSource,TxDisposition.freeList,bind_assoc,pure_bind]
  rw [factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,freed,af,freeRun,run⟩ := run
  cases u
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,keys,ak,keyRun,run⟩ := run
  cases u
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,paidWorld,ap,peerRun,run⟩ := run
  cases u
  cases run
  have freedAccount := account.free_tx_list item a af freeRun
  have stable := freedAccount.stable.view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (stable_keypairPut (some key) false) freed af () keys ak keyRun)
  have keyAccount := (freedAccount.phased.key_put (some key) false af ak keyRun).boundary stable
  exact ⟨rfl,keyAccount.payment peerRun⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
