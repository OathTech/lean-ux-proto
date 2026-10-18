import Leanux.Proofs.WG.AuthenticatedEffects.SentFrames
import Leanux.Proofs.WG.AuthenticatedEffects.ReplyBinding

/-! Actual egress-queue claims. Unlike attempt receipts, these describe the
original native datagram append. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes Leanux.Proofs.Framing

def SocketEmission (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (before after : List SentDatagram) : Prop :=
  ∃ suffix, after = before ++ suffix ∧ suffix.length ≤ 1 ∧
    ∀ d ∈ suffix, d.family = e.family ∧ d.addr = e.addr ∧ d.port = e.port ∧
      d.bytes = bytes ∧ d.ds = ds

theorem SocketEmission.refl (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (sent : List SentDatagram) : SocketEmission e bytes ds sent sent := ⟨[],by simp⟩

theorem tunnelReply_sent (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route)
    (w v : WGWorld) (a b : Ambient)
    (run : ((tunnelXmitSource e bytes ds r false).run w).run a = .ok (((),v),b)) :
    ∃ sport, v.sent = w.sent ++ [tunnelDatagram e bytes ds r sport] := by
  rw [tunnelReply_factor,native_bind_run] at run
  cases front : ((tunnelReplyFront e bytes r).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨sport,u⟩,c⟩
    rw [front] at run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (tunnelReplyFront_sent e bytes r) w a sport u c front
    cases run
    exact ⟨sport,congrArg (fun sent => sent ++ [tunnelDatagram e bytes ds r sport]) same⟩

theorem tunnelReply_emission (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route)
    (w v : WGWorld) (a b : Ambient)
    (run : ((tunnelXmitSource e bytes ds r false).run w).run a = .ok (((),v),b)) :
    SocketEmission e bytes ds w.sent v.sent := by
  obtain ⟨sport,eq⟩ := tunnelReply_sent e bytes ds r w v a b run
  exact ⟨[tunnelDatagram e bytes ds r sport],eq,by simp,by simp [tunnelDatagram]⟩

theorem send4_reply_emission (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (w v : WGWorld) (a b : Ambient) (result : Int)
    (run : ((send4 e none bytes ds false).run w).run a = .ok ((result,v),b)) :
    SocketEmission e bytes ds w.sent v.sent := by
  rw [← send4Source_eq, socket4Front_factor, native_bind_run] at run
  cases front : ((socket4Front e none bytes ds false).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨r,u⟩,c⟩
    rw [front] at run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (socket4Front_sent e bytes ds false) w a r u c front
    cases r with
    | error err =>
      cases run
      rw [same]
      exact SocketEmission.refl e bytes ds _
    | ok route =>
      change ((tunnelXmitSource e bytes ds route false >>= fun _ => pure 0).run u).run c = _ at run
      rw [native_bind_run] at run
      cases tunnel : ((tunnelXmitSource e bytes ds route false).run u).run c with
      | error err => simp [tunnel] at run
      | ok out =>
        rcases out with ⟨⟨doneUnit,z⟩,d⟩
        rw [tunnel] at run
        cases run
        cases doneUnit
        rw [← same]
        exact tunnelReply_emission e bytes ds route u _ c _ tunnel

theorem send6_reply_emission (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (w v : WGWorld) (a b : Ambient) (result : Int)
    (run : ((send6 e none bytes ds false).run w).run a = .ok ((result,v),b)) :
    SocketEmission e bytes ds w.sent v.sent := by
  rw [socket6_factor, native_bind_run] at run
  cases front : ((socket6Front e none).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨r,u⟩,c⟩
    rw [front] at run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (socket6Front_sent e) w a r u c front
    cases r with
    | error err =>
      cases run
      rw [same]
      exact SocketEmission.refl e bytes ds _
    | ok route =>
      change ((tunnelXmitSource e bytes ds route false >>= fun _ => pure 0).run u).run c = _ at run
      rw [native_bind_run] at run
      cases tunnel : ((tunnelXmitSource e bytes ds route false).run u).run c with
      | error err => simp [tunnel] at run
      | ok out =>
        rcases out with ⟨⟨doneUnit,z⟩,d⟩
        rw [tunnel] at run
        cases run
        cases doneUnit
        rw [← same]
        exact tunnelReply_emission e bytes ds route u _ c _ tunnel

private theorem discard_run (f : WG.M α) (w : WGWorld) (a : Ambient) :
    ((discard f).run w).run a = (((f.run w).run a).map fun out => (((),out.1.2),out.2)) := by
  simp only [discard, map_const]
  change (((f.run w).run a).map fun out => (((),out.1.2),out.2)) = _
  cases result : ((f.run w).run a) <;> rfl

theorem replySocket_emission (target : ReplyTarget) (bytes : List UInt8)
    (w v : WGWorld) (a b : Ambient)
    (run : ((replySocket target bytes).run w).run a = .ok (((),v),b)) :
    SocketEmission target.endpoint bytes 0 w.sent v.sent := by
  unfold replySocket at run
  split at run
  · rw [discard_run] at run
    cases sent : ((send4 target.endpoint none bytes 0 false).run w).run a with
    | error err => simp [sent,Except.map] at run
    | ok out =>
      rcases out with ⟨⟨result,z⟩,d⟩
      simp only [sent,Except.map,Except.ok.injEq,Prod.mk.injEq,true_and] at run
      rcases run with ⟨rfl,rfl⟩
      exact send4_reply_emission target.endpoint bytes 0 w z a d result sent
  · rw [discard_run] at run
    cases sent : ((send6 target.endpoint none bytes 0 false).run w).run a with
    | error err => simp [sent,Except.map] at run
    | ok out =>
      rcases out with ⟨⟨result,z⟩,d⟩
      simp only [sent,Except.map,Except.ok.injEq,Prod.mk.injEq,true_and] at run
      rcases run with ⟨rfl,rfl⟩
      exact send6_reply_emission target.endpoint bytes 0 w z a d result sent

def ReplyEmission (src : SkbSource) (bytes : List UInt8)
    (before after : List SentDatagram) : Prop :=
  ∃ suffix, after = before ++ suffix ∧ suffix.length ≤ 1 ∧
    ∀ d ∈ suffix, d.addr = src.saddr ∧ d.port = src.sport ∧ d.bytes = bytes

theorem reply_emission (src : SkbSource) (bytes : List UInt8)
    (w v : WGWorld) (a b : Ambient)
    (run : ((sendBufferAsReplyToSkb src bytes).run w).run a = .ok (((),v),b)) :
    ReplyEmission src bytes w.sent v.sent := by
  rw [reply_factor,native_bind_run] at run
  cases front : ((replyFront src).run w).run a with
  | error err => simp [front] at run
  | ok out =>
    rcases out with ⟨⟨target,u⟩,c⟩
    rw [front] at run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (replyFront_sent src) w a target u c front
    cases target with
    | none => cases run; exact ⟨[],by simp [same]⟩
    | some t =>
      have source := replyFront_source src w u a c t front
      obtain ⟨suffix,eq,length,members⟩ := replySocket_emission t bytes u v c b run
      refine ⟨suffix,?_,length,?_⟩
      · simpa only [same] using eq
      · intro d hd
        have bound := members d hd
        exact ⟨bound.2.1.trans source.1,bound.2.2.1.trans source.2,bound.2.2.2.1⟩

theorem cookie_emission (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (run : ((sendHandshakeCookie msg src).run w).run a = .ok (((),v),b)) :
    ∃ bytes u c,
      ((cookieMessageCreate (u32le msg 4) src ((msg.drop (msg.length - 32)).take 16)).run w).run a =
        .ok ((bytes,u),c) ∧ ReplyEmission src bytes w.sent v.sent := by
  unfold sendHandshakeCookie at run
  rw [native_bind_run] at run
  cases created : ((cookieMessageCreate (u32le msg 4) src
      ((msg.drop (msg.length - 32)).take 16)).run w).run a with
  | error err => simp [created] at run
  | ok out =>
    rcases out with ⟨⟨bytes,u⟩,c⟩
    rw [created] at run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (cookieMessageCreate_sent _ src _) w a bytes u c created
    refine ⟨bytes,u,c,rfl,?_⟩
    rw [← same]
    exact reply_emission src bytes u v c b run

theorem qualifying_cookie_emission (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : Cookies.FailedMac2 msg src w a)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    ∃ bytes u c,
      ((cookieMessageCreate (u32le msg 4) src ((msg.drop (msg.length - 32)).take 16)).run h.made).run
        (cookieReplyEntry msg h.checked) = .ok ((bytes,u),c) ∧
      ReplyEmission src bytes w.sent v.sent := by
  rw [qualifying_rejected_run msg src w a kind h] at run
  obtain ⟨bytes,u,c,created,emitted⟩ := cookie_emission msg src h.made v _ b run
  have hm := (ProjectedAction.iff_run_ambient _ _ _).mp (makeCookie_sent src)
    h.loaded _ h.cookie h.made h.madeAmbient h.cookieRun
  have hl := (ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_sent
    w _ true h.loaded h.loadedAmbient h.loadRun
  exact ⟨bytes,u,c,created,by simpa only [hm,hl] using emitted⟩

end Leanux.Proofs.WG.AuthenticatedEffects
