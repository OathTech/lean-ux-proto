import Leanux.Proofs.WG.RetirementSecurity.RxCompletionWireFrames

/-! Actual RX completion can append new TX work after key confirmation,
but preserves exclusive physical ownership and every pre-existing pending
encryption alias. Packet boundedness supplies freshness at the staged cut. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem TxInventory.wire_queues (inventory : TxInventory locals w)
    (wire : txCryptWire v = txCryptWire w)
    (queues : handoffTxView v = handoffTxView w) : TxInventory locals v := by
  apply inventory.transport
  · intro pid p found
    have after : handoffTxView v pid = some p.txQueue.all := by
      simpa only [handoffTxView,peerAt,Option.map_some] using congrArg (Option.map fun p => p.txQueue.all) found
    rw [queues] at after
    obtain ⟨old,resident,items⟩ := Option.map_eq_some_iff.mp after
    exact ⟨old,resident,congrArg List.flatten items⟩
  · intro id packet found
    exact ⟨packet,(congrFun (congrArg Prod.snd wire) id).trans found⟩

theorem ownership_queues {action : WG.M α} (same : SameView ownershipPointView action) :
    SameView handoffTxView action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact ownership_points_queues ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

abbrev TxOccurrences (locals : List TxLocalBatch) (active : List (List SkbId)) (w : WGWorld) :=
  TxInventory locals w ∧ TxCryptInventory active w

theorem occurrence_passive {action : WG.M α} (wire : SameView txCryptWire action)
    (queues : SameView handoffTxView action) : Preserves (TxOccurrences locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp wire w a result v b run
  have owners := (ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run
  exact ⟨before.1.wire_queues fields owners,
    before.2.frame_packets (congrArg Prod.fst fields) (fun _ owned => owned.queues owners)
      (congrArg Prod.snd fields)⟩

theorem confirmation_occurrences (pid : PeerId) (kid : KeypairId) :
    Preserves (TxOccurrences locals active) (receivedWithKeypair pid kid) :=
  occurrence_passive (confirmation_cryptWire pid kid)
    ((receivedWithKeypair_protect pid kid).factor (fun s => s.2.2.1))

theorem promote_send_occurrences (before : TxOccurrences locals active w)
    (bounded : Packets.Inv w) (pid : PeerId) (kid : KeypairId) (a b : Ambient)
    (run : ((promoteAndSend pid kid).run w).run a = .ok (((),v),b)) :
    TxOccurrences locals active v := by
  simp only [promoteAndSend,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨fresh,u,c,confirmRun,flag,t,e,branchRun,tail⟩ := run
  have beforeU := (hoare_iff_run_ambient _ _ _).mp (confirmation_occurrences pid kid)
    w a fresh u c before confirmRun
  have boundU := (hoare_iff_run_ambient _ _ _).mp (geometry_bound (confirmation_geometry pid kid))
    w a fresh u c bounded confirmRun
  have exactBranch : flag = fresh ∧ t = u := by cases branchRun; exact ⟨rfl,rfl⟩
  obtain ⟨sameFlag,sameWorld⟩ := exactBranch
  subst flag
  subst t
  cases fresh with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact beforeU
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,f,timerRun,sendRun⟩ := tail
    have beforeT := (hoare_iff_run_ambient _ _ _).mp
      (occurrence_passive (handshakeComplete_cryptWire pid .walltimeLastHandshakeData)
        (ownership_queues (handshakeComplete_ownership pid .walltimeLastHandshakeData)))
      u e () t f beforeU timerRun
    have boundT := (hoare_iff_run_ambient _ _ _).mp
      (geometry_bound (handshakeComplete_geometry pid .walltimeLastHandshakeData))
      u e () t f boundU timerRun
    exact CryptStaging.staged ⟨⟨boundT,beforeT.1⟩,beforeT.2⟩ pid f b sendRun

theorem receive_done_occurrences (before : TxOccurrences locals active w)
    (bounded : Packets.Inv w) (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) (a b : Ambient)
    (run : ((consumeDataDone pid pkt endpoint).run w).run a = .ok ((result,v),b)) :
    TxOccurrences locals active v := by
  rw [Packets.consumeDataDone_factor,rxPrepare_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepareRun,finishRun⟩ := run
  obtain ⟨_,t,e,endpointRun,_,s,f,promoteRun,restRun⟩ := prepareRun
  have beforeT := (hoare_iff_run_ambient _ _ _).mp
    (occurrence_passive (endpoint_cryptWire pid endpoint) (ownership_queues (endpoint_ownership pid endpoint)))
    w a () t e before endpointRun
  have boundT := (hoare_iff_run_ambient _ _ _).mp (geometry_bound (endpoint_geometry pid endpoint))
    w a () t e bounded endpointRun
  have beforeS := promote_send_occurrences beforeT boundT pid pkt.keypair e f promoteRun
  have beforeU := (hoare_iff_run_ambient _ _ _).mp
    (occurrence_passive (prepareRest_cryptWire pid pkt) (ownership_queues (prepareRest_ownership pid pkt)))
    s f ready u c beforeS restRun
  cases ready with
  | none => cases finishRun; exact beforeU
  | some ready =>
    exact (hoare_iff_run_ambient _ _ _).mp
      (occurrence_passive (finishRx_cryptWire pid ready) (ownership_queues (finishRx_ownership pid ready)))
      u c result v b beforeU finishRun

end Leanux.Proofs.WG.RetirementSecurity
