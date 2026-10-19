import Leanux.Proofs.WG.RetirementSecurity.TxWorkRxFrames

/-! Successful native receive completion retains TX service across key
confirmation, a possible staged send and authenticated receive bookkeeping.
The staging frontier is derived from the incoming physical allocation carrier. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem stage_frame {action : WG.M α}
    (geometry : SameView StagingOccurrences.geometry action)
    (wire : SameView txCryptWire action) (queues : SameView handoffTxView action)
    (work : SameView queued action) : Preserves (StageReady locals crypt tx) action := by
  apply stage_join (passive wire queues work)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have bounded:=(hoare_iff_run_ambient _ _ _).mp (geometry_bound geometry) w a result v b before.1.1 run
  have owned:=(hoare_iff_run_ambient _ _ _).mp (occurrence_passive wire queues)
    w a result v b ⟨before.1.2,before.2⟩ run
  exact ⟨⟨bounded,owned.1⟩,owned.2⟩

theorem stage_confirmation (pid : PeerId) (kid : KeypairId) :
    Preserves (StageReady locals crypt tx) (receivedWithKeypair pid kid) :=
  stage_frame (confirmation_geometry pid kid) (confirmation_cryptWire pid kid)
    ((receivedWithKeypair_protect pid kid).factor (fun s=>s.2.2.1)) (confirmation_work pid kid)

theorem stage_endpoint (pid : PeerId) (endpoint : Endpoint) :
    Preserves (StageReady locals crypt tx) (setPeerEndpoint pid endpoint) :=
  stage_frame (endpoint_geometry pid endpoint) (endpoint_cryptWire pid endpoint)
    (ownership_queues (endpoint_ownership pid endpoint)) (endpoint_work pid endpoint)

theorem stage_handshake_complete (pid : PeerId) (site : HiddenSite) :
    Preserves (StageReady locals crypt tx) (timersHandshakeComplete pid site) :=
  stage_frame (handshakeComplete_geometry pid site) (handshakeComplete_cryptWire pid site)
    (ownership_queues (handshakeComplete_ownership pid site)) (handshake_complete_work pid site)

theorem promote_send_service (before : StageReady locals crypt tx w) (pid : PeerId) (kid : KeypairId)
    (a b : Ambient) (run : ((promoteAndSend pid kid).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v := by
  simp only [promoteAndSend,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨fresh,u,c,confirmed,flag,t,e,branched,tail⟩:=run
  have held:=(hoare_iff_run_ambient _ _ _).mp (stage_confirmation pid kid) w a fresh u c before confirmed
  have same:flag=fresh ∧ t=u := by cases branched; exact ⟨rfl,rfl⟩
  obtain ⟨flagSame,stateSame⟩:=same
  subst flag
  subst t
  cases fresh with
  | false=>simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact held.1
  | true=>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,f,timer,sent⟩:=tail
    exact staged_service
      ((hoare_iff_run_ambient _ _ _).mp (stage_handshake_complete pid .walltimeLastHandshakeData)
        u e () t f held timer) pid f b sent

theorem receive_done_service (before : StageReady locals crypt tx w) (pid : PeerId)
    (pkt : RxPacket) (endpoint : Endpoint) (a b : Ambient)
    (run : ((consumeDataDone pid pkt endpoint).run w).run a=.ok ((result,v),b)) :
    Obligations crypt tx v := by
  rw [Packets.consumeDataDone_factor,rxPrepare_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepareRun,finishRun⟩:=run
  obtain ⟨_,t,e,endpointRun,_,s,f,promoted,rest⟩:=prepareRun
  have held:=(hoare_iff_run_ambient _ _ _).mp (stage_endpoint pid endpoint) w a () t e before endpointRun
  have sent:=promote_send_service held pid pkt.keypair e f promoted
  have prepared:=(hoare_iff_run_ambient _ _ _).mp
    (passive (prepareRest_cryptWire pid pkt) (ownership_queues (prepareRest_ownership pid pkt))
      (prepare_rest_work pid pkt)) s f ready u c sent rest
  cases ready with
  | none=>cases finishRun; exact prepared
  | some ready=>
    exact (hoare_iff_run_ambient _ _ _).mp
      (passive (finishRx_cryptWire pid ready) (ownership_queues (finishRx_ownership pid ready))
        (finish_work pid ready)) u c result v b prepared finishRun

theorem serving_receive_done (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (Serving locals crypt tx) (consumeDataDone pid pkt endpoint) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨receive_done_service before.stage_ready pid pkt endpoint a b run,
    (hoare_iff_run_ambient _ _ _).mp
      (TxCovered.join (RxPollOccurrences.consume pid pkt endpoint) (TxCoverageNative.consume pid pkt endpoint))
      w a result v b before.2 run⟩

end Leanux.Proofs.WG.RetirementSecurity.TxWork
