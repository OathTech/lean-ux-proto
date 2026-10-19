import Leanux.Proofs.WG.TransmitSecurity.BatchNativeStack

/-! Authentication can promote a responder key and stage waiting packets.
The original receive completion preserves alignment across that native send. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem promote_send (before : Ready locals w) (pid : PeerId) (kid : KeypairId) (a b : Ambient)
    (run : ((promoteAndSend pid kid).run w).run a = .ok (((),v),b)) : Inv v := by
  simp only [promoteAndSend,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨fresh,u,c,confirmRun,flag,t,e,branchRun,tail⟩ := run
  have held := (hoare_iff_run_ambient _ _ _).mp
    (ready_frame (confirmation_geometry pid kid)
      ((receivedWithKeypair_protect pid kid).factor (fun s => s.2.2.1)))
    w a fresh u c before confirmRun
  have exactBranch : flag = fresh ∧ t = u := by cases branchRun; exact ⟨rfl,rfl⟩
  obtain ⟨sameFlag,sameWorld⟩ := exactBranch
  subst flag
  subst t
  cases fresh with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact held.2
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,f,timerRun,sendRun⟩ := tail
    have kept := (hoare_iff_run_ambient _ _ _).mp
      (ready_frame (handshakeComplete_geometry pid .walltimeLastHandshakeData)
        (ownership_queues (handshakeComplete_ownership pid .walltimeLastHandshakeData)))
      u e () t f held timerRun
    exact send kept pid f b sendRun

theorem receive_done (before : Ready locals w)
    (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) (a b : Ambient)
    (run : ((consumeDataDone pid pkt endpoint).run w).run a = .ok ((result,v),b)) : Inv v := by
  rw [Packets.consumeDataDone_factor,rxPrepare_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepareRun,finishRun⟩ := run
  obtain ⟨_,t,e,endpointRun,_,s,f,promoteRun,restRun⟩ := prepareRun
  have held := (hoare_iff_run_ambient _ _ _).mp
    (ready_frame (endpoint_geometry pid endpoint) (ownership_queues (endpoint_ownership pid endpoint)))
    w a () t e before endpointRun
  have promoted := promote_send held pid pkt.keypair e f promoteRun
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (wire (ownership_queues (prepareRest_ownership pid pkt)) (prepareRest_cryptWire pid pkt))
    s f ready u c promoted restRun
  cases ready with
  | none => cases finishRun; exact kept
  | some ready =>
    exact (hoare_iff_run_ambient _ _ _).mp
      (wire (ownership_queues (finishRx_ownership pid ready)) (finishRx_cryptWire pid ready))
      u c result v b kept finishRun

theorem consume (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (Coherent locals active) (consumeDataDone pid pkt endpoint) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (RxPollOccurrences.consume pid pkt endpoint)
      w a result v b before.1 run,
    receive_done ⟨⟨before.1.1.bounded,before.1.2.1⟩,before.2⟩ pid pkt endpoint a b run⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
