import Leanux.Proofs.WG.TransmitSecurity.CompletionSocketFrames
import Leanux.Proofs.WG.TransmitSecurity.CompletionReceipts
import Leanux.Proofs.WG.AuthenticatedEffects.Emission

/-! Native cached transport socket calls append at most one datagram, whose
endpoint, bytes and traffic class are the actual call arguments. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes AuthenticatedEffects

theorem tunnel_sent (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool)
    (w v : WGWorld) (a b : Ambient)
    (run : ((tunnelXmitSource e bytes ds r exactRx).run w).run a = .ok (((),v),b)) :
    ∃ sport, v.sent = w.sent ++ [tunnelDatagram e bytes ds r sport] := by
  rw [tunnel_factor,native_bind_run] at run
  cases front : ((tunnelFront e bytes r exactRx).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨sport,u⟩,c⟩
    rw [front] at run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (tunnelFront_sent e bytes r exactRx) w a sport u c front
    cases run
    exact ⟨sport,congrArg (fun sent => sent ++ [tunnelDatagram e bytes ds r sport]) same⟩

theorem tunnel_emission (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool)
    (w v : WGWorld) (a b : Ambient)
    (run : ((tunnelXmitSource e bytes ds r exactRx).run w).run a = .ok (((),v),b)) :
    SocketEmission e bytes ds w.sent v.sent := by
  obtain ⟨sport,eq⟩ := tunnel_sent e bytes ds r exactRx w v a b run
  exact ⟨[tunnelDatagram e bytes ds r sport],eq,by simp,by simp [tunnelDatagram]⟩

theorem send4_emission (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (w v : WGWorld) (a b : Ambient) (result : Int)
    (run : ((send4 e cache bytes ds exactRx).run w).run a = .ok ((result,v),b)) :
    SocketEmission e bytes ds w.sent v.sent := by
  rw [← send4Source_eq, socket4Front_factor, native_bind_run] at run
  cases front : ((socket4Front e cache bytes ds exactRx).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨r,u⟩,c⟩
    rw [front] at run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (socket4Front_sent e cache bytes ds exactRx) w a r u c front
    cases r with
    | error err =>
      cases run
      rw [same]
      exact SocketEmission.refl e bytes ds _
    | ok route =>
      change ((tunnelXmitSource e bytes ds route exactRx >>= fun _ => pure 0).run u).run c = _ at run
      rw [native_bind_run] at run
      cases tunnel : ((tunnelXmitSource e bytes ds route exactRx).run u).run c with
      | error err => simp [tunnel] at run
      | ok out =>
        rcases out with ⟨⟨doneUnit,z⟩,d⟩
        rw [tunnel] at run
        cases run
        cases doneUnit
        rw [← same]
        exact tunnel_emission e bytes ds route exactRx u _ c _ tunnel

theorem send6_emission (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (w v : WGWorld) (a b : Ambient) (result : Int)
    (run : ((send6 e cache bytes ds exactRx).run w).run a = .ok ((result,v),b)) :
    SocketEmission e bytes ds w.sent v.sent := by
  rw [socket6_factor, native_bind_run] at run
  cases front : ((socket6Front e cache).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨r,u⟩,c⟩
    rw [front] at run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (socket6Front_sent e cache) w a r u c front
    cases r with
    | error err =>
      cases run
      rw [same]
      exact SocketEmission.refl e bytes ds _
    | ok route =>
      change ((tunnelXmitSource e bytes ds route exactRx >>= fun _ => pure 0).run u).run c = _ at run
      rw [native_bind_run] at run
      cases tunnel : ((tunnelXmitSource e bytes ds route exactRx).run u).run c with
      | error err => simp [tunnel] at run
      | ok out =>
        rcases out with ⟨⟨doneUnit,z⟩,d⟩
        rw [tunnel] at run
        cases run
        cases doneUnit
        rw [← same]
        exact tunnel_emission e bytes ds route exactRx u _ c _ tunnel

/-- A valid retained socket receipt binds every actual datagram added by that
call to its observed peer endpoint, packet bytes and traffic class. -/
theorem SocketReceipt.Valid.emission {r : SocketReceipt} (valid : r.Valid) :
    SocketEmission r.endpoint r.packet.value.bytes r.packet.value.ds
      r.socket.before.wg.sent r.socket.after.wg.sent := by
  have run := valid.2.2
  change (liftWG r.action).run r.socket.before = .ok (r.socket.value,r.socket.after) at run
  rw [liftWG_run] at run
  cases native : (r.action.run r.socket.before.wg).run r.socket.before.ambient with
  | error err => simp [native,Except.map] at run
  | ok out =>
    rcases out with ⟨⟨result,wg⟩,ambient⟩
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    have same : r.socket.after.wg = wg := congrArg World.wg run.2.symm
    rw [same]
    unfold SocketReceipt.action at native
    split at native
    · exact send4_emission _ _ _ _ _ _ _ _ _ _ native
    · exact send6_emission _ _ _ _ _ _ _ _ _ _ native

end Leanux.Proofs.WG.TransmitSecurity.Completion
