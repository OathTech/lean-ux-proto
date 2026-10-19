import Leanux.Proofs.WG.AuthenticatedEffects.CookieSocketSource

/-! Exact ordered accounting through the original cookie sender. Each native
append contributes one receipt at its source cut; failure before that cut
adds no receipt, and later Stop retains the reached receipt prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CookieAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def Counted (body : WGPrefix DatagramReceipt α) : Prop :=
  ∀ earlier : List SentDatagram,
    StatePrefixPreserves (fun h w _ => w.sent = earlier ++ h.map DatagramReceipt.datagram)
      (fun _ => True) body

theorem pure_counted (value : α) : Counted (pure value) := fun _ =>
  StatePrefixEnsures.pure _ (fun _ _ _ _ => True.intro) (fun _ _ _ hi => hi)

theorem bind_counted {body : WGPrefix DatagramReceipt α} {next : α → WGPrefix DatagramReceipt β}
    (head : Counted body) (tail : ∀ value, Counted (next value)) : Counted (body >>= next) :=
  fun earlier => StatePrefixEnsures.bind (head earlier) (fun value => tail value earlier)

theorem native_counted (body : WG.M α) (frame : SameView WGWorld.sent body) :
    Counted (liftWGPrefix body) := fun _ =>
  StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
    (fun _ w a value v b hi run =>
      ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b run).trans hi)

theorem tunnel (endpoint : Endpoint) (bytes : List UInt8) (ds : Nat) (route : Route) :
    Counted (tunnelObserved endpoint bytes ds route) := by
  intro earlier w a h hi
  have observed := tunnelObserved_run endpoint bytes ds route w a h
  change runPrefix ((tunnelObserved endpoint bytes ds route).run w) a h = _ at observed
  rw [observed]
  cases native : ((tunnelReplyFront endpoint bytes route).run w).run a with
  | error stop => exact ⟨[],by simp,True.intro,True.intro⟩
  | ok out =>
    obtain ⟨⟨port,v⟩,b⟩ := out
    let receipt : DatagramReceipt := ⟨endpoint,bytes,ds,route,⟨port,w,v,a,b⟩⟩
    refine ⟨[receipt],rfl,True.intro,?_⟩
    have frame := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
      (tunnelReplyFront_sent endpoint bytes route) w a port v b native
    change v.sent ++ [receipt.datagram] = earlier ++ (h ++ [receipt]).map DatagramReceipt.datagram
    rw [frame,hi,List.map_append,List.map_cons,List.map_nil,List.append_assoc]

theorem socket (front : WG.M (Except Int Route)) (endpoint : Endpoint)
    (bytes : List UInt8) (ds : Nat) (frame : SameView WGWorld.sent front) :
    Counted (socketEmitted front endpoint bytes ds) := by
  apply bind_counted (native_counted front frame)
  intro result
  cases result with
  | error err => exact pure_counted err
  | ok route => exact bind_counted (tunnel endpoint bytes ds route) (fun _ => pure_counted 0)

theorem reply_socket (target : ReplyTarget) (bytes : List UInt8) :
    Counted (replySocketEmitted target bytes) := by
  unfold replySocketEmitted
  split
  · exact bind_counted (socket _ _ _ _ (socket4Front_sent _ _ _ _)) (fun _ => pure_counted ())
  · exact bind_counted (socket _ _ _ _ (socket6Front_sent _)) (fun _ => pure_counted ())

theorem reply (src : SkbSource) (bytes : List UInt8) : Counted (replyEmitted src bytes) := by
  apply bind_counted (native_counted _ (replyFront_sent src))
  intro target
  cases target with
  | none => exact pure_counted ()
  | some target => exact reply_socket target bytes

theorem cookie (msg : List UInt8) (src : SkbSource) : Counted (cookieEmitted msg src) :=
  bind_counted (native_counted _ (cookieMessageCreate_sent _ _ _)) (reply src)

end Leanux.Proofs.WG.AuthenticatedEffects.CookieAccounting
