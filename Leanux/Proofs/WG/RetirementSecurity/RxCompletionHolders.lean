import Leanux.Proofs.WG.RetirementSecurity.RxCompletionGeometry

/-! The actual RX completion callback transports key references through
confirmation and its conditional staged send. The incoming packet's key
compatibility and packet-allocation boundedness remain explicit; this does
not assume that a successful receive already owns a complete post-state. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem HolderAccount.promote_send (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (compatible : KeyCompatible pid kid w) (a b : Ambient)
    (run : ((promoteAndSend pid kid).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  simp only [promoteAndSend,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨fresh,u,c,confirmRun,flag,t,e,branchRun,tail⟩ := run
  have accountU := account.confirm pid kid a c confirmRun
  have boundU := (hoare_iff_run_ambient _ _ _).mp (geometry_bound (confirmation_geometry pid kid))
    w a fresh u c bounded confirmRun
  have exactBranch : flag = fresh ∧ t = u := by cases branchRun; exact ⟨rfl,rfl⟩
  obtain ⟨sameFlag,sameWorld⟩ := exactBranch
  subst flag
  subst t
  cases fresh with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact accountU
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,f,timerRun,sendRun⟩ := tail
    have current := receivedWithKeypair_current_compatible compatible a c confirmRun
    have currentT := (hoare_iff_run_ambient _ _ _).mp
      (control_current (project := id) (timersHandshakeComplete_control pid .walltimeLastHandshakeData) pid)
      u e () t f current timerRun
    have boundT := (hoare_iff_run_ambient _ _ _).mp
      (geometry_bound (handshakeComplete_geometry pid .walltimeLastHandshakeData))
      u e () t f boundU timerRun
    have accountT := accountU.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (handshakeComplete_ownership pid .walltimeLastHandshakeData) u e () t f timerRun)
    exact accountT.staged boundT currentT f b sendRun

/-- The original authenticated receive-completion callback neither loses nor
creates key references: promotion transfers slot credits, and a resulting
staged send transfers or repays its real current-key acquisition. -/
theorem HolderAccount.receive_done (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (compatible : KeyCompatible pid pkt.keypair w)
    (endpoint : Endpoint) (a b : Ambient)
    (run : ((consumeDataDone pid pkt endpoint).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := by
  rw [Packets.consumeDataDone_factor,rxPrepare_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepareRun,finishRun⟩ := run
  obtain ⟨_,t,e,endpointRun,_,s,f,promoteRun,restRun⟩ := prepareRun
  have accountT := account.points ((ProjectedAction.iff_run_ambient _ _ _).mp
    (endpoint_ownership pid endpoint) w a () t e endpointRun)
  have boundT := (hoare_iff_run_ambient _ _ _).mp (geometry_bound (endpoint_geometry pid endpoint))
    w a () t e bounded endpointRun
  have compatibleT := ((hoare_iff_run_ambient _ _ _).mp
    (stage_control (project := id) (setPeerEndpoint_control pid endpoint) w pid pkt.keypair)
    w a () t e ⟨Transfer.refl w,compatible⟩ endpointRun).2
  have accountS := accountT.promote_send boundT compatibleT e f promoteRun
  have accountU := accountS.points ((ProjectedAction.iff_run_ambient _ _ _).mp
    (prepareRest_ownership pid pkt) s f ready u c restRun)
  cases ready with
  | none => cases finishRun; exact accountU
  | some ready => exact accountU.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (finishRx_ownership pid ready) u c result v b finishRun)

end Leanux.Proofs.WG.RetirementSecurity
