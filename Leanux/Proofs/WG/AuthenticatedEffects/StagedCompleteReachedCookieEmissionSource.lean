import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieRouteSource
import Leanux.Proofs.WG.AuthenticatedEffects.CookieSocketSource

/-! Exact cookie-emission source equations retain native prefixes and the original captured tunnel entry before the append and its single receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CookieEmission
open Leanux Leanux.WG Leanux.Proofs.Logged

def relabel (record : E→F) (body : WGPrefix E α) : WGPrefix F α := focusStatePrefix record (fun _=>none) body

theorem relabel_run (record : E→F) (body : WGPrefix E α) (w : WGWorld) (a : Ambient) (h : List F) :
    runWGPrefix (relabel record body) w a h =
      ((runWGPrefix body w a []).1,h++(runWGPrefix body w a []).2.map record) := by
  change ((runWGPrefix body w a (h.filterMap (fun _=>none))).1,
    h++((runWGPrefix body w a (h.filterMap (fun _=>none))).2.drop
      (h.filterMap (fun _=> (none : Option E))).length).map record)=_
  have empty : h.filterMap (fun _=>(none : Option E))=[] := by simp
  rw [empty,List.length_nil,List.drop_zero]

theorem relabel_native_bind (record : E→F) (body : WG.M α) (next : α→WGPrefix E β) :
    relabel record (liftWGPrefix body >>= next) =
      (liftWGPrefix body >>= fun value=>relabel record (next value)) := by
  funext w a h
  change runWGPrefix (relabel record (liftWGPrefix body >>= next)) w a h=
    runWGPrefix (liftWGPrefix body >>= fun value=>relabel record (next value)) w a h
  rw [relabel_run,liftWG_bind_run,liftWG_bind_run]
  cases performed : (body.run w).run a with
  | error stop=>simp
  | ok out=>rcases out with ⟨⟨value,v⟩,b⟩;exact (relabel_run record (next value) v b h).symm

theorem relabel_pure (record : E→F) (value : α) : relabel record (pure value)=pure value := by
  funext w a h
  change runWGPrefix (relabel record (pure value)) w a h=runWGPrefix (pure value : WGPrefix F α) w a h
  rw [relabel_run]
  change (Except.ok ((value,w),a),h++([] : List E).map record)=(Except.ok ((value,w),a),h)
  simp

theorem capture_bind_run (body : WG.M α) (next : WGRunWitness α→WGPrefix E β)
    (w : WGWorld) (a : Ambient) (h : List E) :
    runWGPrefix (captureWGRun body >>= next) w a h = match (body.run w).run a with
    | .error stop=>(.error stop,h)
    | .ok ((value,v),b)=>runWGPrefix (next ⟨value,w,v,a,b⟩) v b h := by
  change runStatePrefix (captureWGRun body >>= next) w a h=_
  rw [runStatePrefix_bind]
  have captured := runWGPrefix_captureWGRun (E:=E) body w a h
  change runStatePrefix (captureWGRun body) w a h=_ at captured
  rw [captured]
  cases performed : (body.run w).run a with
  | error stop=>rfl
  | ok out=>rcases out with ⟨⟨value,v⟩,b⟩;rfl

theorem relabel_capture_bind (record : E→F) (body : WG.M α) (next : WGRunWitness α→WGPrefix E β) :
    relabel record (captureWGRun body >>= next) =
      (captureWGRun body >>= fun value=>relabel record (next value)) := by
  funext w a h
  change runWGPrefix (relabel record (captureWGRun body >>= next)) w a h=
    runWGPrefix (captureWGRun body >>= fun value=>relabel record (next value)) w a h
  rw [relabel_run,capture_bind_run,capture_bind_run]
  cases performed : (body.run w).run a with
  | error stop=>simp
  | ok out=>rcases out with ⟨⟨value,v⟩,b⟩;exact (relabel_run record (next ⟨value,w,v,a,b⟩) v b h).symm


theorem relabel_emit (record : E→F) (event : E) : relabel record (emitStatePrefix event)=emitStatePrefix (record event) := by
  funext w a h
  change runWGPrefix (relabel record (emitStatePrefix event)) w a h=runWGPrefix (emitStatePrefix (record event)) w a h
  rw [relabel_run]
  rfl

theorem unit_return (body : WGPrefix E Unit) : (body >>= fun _=>pure ())=body := by
  have unit : (fun _ : Unit=>pure () : Unit→WGPrefix E Unit)=pure := by funext value;cases value;rfl
  rw [unit,bind_pure]

def tunnel (record : DatagramReceipt→E) (e : Endpoint) (bytes : Key) (ds : Nat) (route : Route) : WGPrefix E Unit := do
  let front←captureWGRun (tunnelReplyFront e bytes route)
  liftWGPrefix (modify fun w=>{w with sent:=w.sent++[tunnelDatagram e bytes ds route front.value]})
  emitStatePrefix (record ⟨e,bytes,ds,route,front⟩)

theorem tunnel_source (record : DatagramReceipt→E) (e : Endpoint) (bytes : Key) (ds : Nat) (route : Route) :
    relabel record (tunnelObserved e bytes ds route)=tunnel record e bytes ds route := by
  unfold tunnelObserved tunnel
  rw [relabel_capture_bind]
  congr 1
  funext front
  rw [relabel_native_bind]
  congr 1
  funext ignored
  exact relabel_emit _ _

def socket (record : DatagramReceipt→E) (args : ProtocolSocket.Args) : WGPrefix E Unit := do
  match ← liftWGPrefix (CookieRoute.action args) with
  | .error _=>pure ()
  | .ok route=>tunnel record args.endpoint args.bytes args.ds route

theorem socket_source (record : DatagramReceipt→E) (front : WG.M (Except Int Route))
    (e : Endpoint) (bytes : Key) (ds : Nat) :
    relabel record (socketEmitted front e bytes ds >>= fun _=>pure ())=(do
      match ← liftWGPrefix front with
      | .error _=>pure ()
      | .ok route=>tunnel record e bytes ds route) := by
  unfold socketEmitted
  rw [bind_assoc,relabel_native_bind]
  congr 1
  funext result
  cases result with
  | error code=>simpa only [pure_bind] using relabel_pure record ()
  | ok route=>
    simp only [bind_assoc,pure_bind,unit_return]
    exact tunnel_source _ _ _ _ _

def reply (record : DatagramReceipt→E) (src : SkbSource) (bytes : Key) : WGPrefix E Unit := do
  match ← liftWGPrefix (replyFront src) with
  | none=>pure ()
  | some target=>socket record ⟨target.ipv4,target.endpoint,none,bytes,0,false⟩

theorem reply_source (record : DatagramReceipt→E) (src : SkbSource) (bytes : Key) :
    relabel record (replyEmitted src bytes)=reply record src bytes := by
  unfold replyEmitted reply
  rw [relabel_native_bind]
  congr 1
  funext result
  cases result with
  | none=>exact relabel_pure record ()
  | some target=>
    unfold replySocketEmitted send4Emitted send6Emitted socket CookieRoute.action
    rcases target with ⟨endpoint,ipv4⟩
    cases ipv4 <;> exact socket_source _ _ _ _ _

def observed (record : CookieSocket.Receipt→E) (mac : HandshakeMac) (msg : Key) (src : SkbSource) : WGPrefix E Unit := do
  let bytes←liftWGPrefix (cookieMessageCreate (u32le msg 4) src ((msg.drop (msg.length-32)).take 16))
  reply (fun receipt=>record ⟨mac,msg,src,receipt⟩) src bytes

theorem observed_source (record : CookieSocket.Receipt→E) (mac : HandshakeMac) (msg : Key) (src : SkbSource) :
    CookieSocket.observed record mac msg src=observed record mac msg src := by
  change relabel (fun r=>record ⟨mac,msg,src,r⟩) (cookieEmitted msg src)=_
  unfold cookieEmitted observed
  rw [relabel_native_bind]
  congr 1
  funext bytes
  exact reply_source _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CookieEmission
