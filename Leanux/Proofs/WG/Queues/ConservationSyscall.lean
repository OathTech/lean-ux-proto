import Leanux.Proofs.WG.Queues.HolderTrafficDispatch
import Leanux.Proofs.WG.Queues.HolderDumpEntry
import Leanux.Proofs.WG.Queues.HolderEntryPollFree
import Leanux.Proofs.WG.Queues.JointSyscallLifecycle

/-! Source certificates through the original syscall boundary. Proof data
composes the existing Rule at exact returned cuts; no executable observer is
introduced. External reservations are fixed across each composition. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConservationSyscall
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open DurableHolders ConservationSource HolderTrafficDispatch

structure Checked (loans : Reservations) (action : RxHistory.Obs α) where
  rule : Rule action
  established : Established rule loans

def Checked.pure (x : α) : Checked loans (pure x) :=
  ⟨ConservationSource.pure x,pure_established x⟩

def Checked.bind {a : RxHistory.Obs α} {b : α→RxHistory.Obs β}
    (first : Checked loans a) (next : ∀x,Checked loans (b x)) : Checked loans (a >>= b) :=
  ⟨ConservationSource.bind first.rule (fun x=>(next x).rule),
    bind_established first.established (fun x=>(next x).established)⟩

def Checked.lift (a : Leanux.M α) (frame : SameView (fun w : World=>wgStoreView w.wg) a) :
    Checked loans (liftPrefix a) := ⟨HolderTrafficDispatch.lift a,lift_established a frame⟩

def Checked.branch (condition : Bool) {yes no : RxHistory.Obs α}
    (a : Checked loans yes) (b : Checked loans no) : Checked loans (if condition then yes else no) :=
  ⟨HolderTrafficDispatch.branch condition a.rule b.rule,
    branch_established condition a.established b.established⟩

def Checked.forIn (items : List γ) (initial : β)
    (action : γ→β→RxHistory.Obs (ForInStep β)) (steps : ∀x y,Checked loans (action x y)) :
    Checked loans (ForIn.forIn items initial action) :=
  match items with
  | []=>Checked.pure initial
  | x::xs=>by
    rw [List.forIn_cons]
    apply Checked.bind (steps x initial)
    intro step
    cases step with
    | done value=>exact Checked.pure value
    | yield value=>exact Checked.forIn xs value action steps

/-- Audit-only leaves retain their actual source journal, with no RX admission
or removal constructors. State preservation is proved separately below. -/
def audit (action : AuditM α) : Rule (RxHistory.audit action) where
  relation := fun cs w h x v k next=>runPrefix (RxHistory.audit action) w h=(.ok (x,v),k) ∧ next=cs
  source := by intro cs w h x v k next hi; exact hi.1
  appends := by
    intro cs w h x v k next hi
    obtain ⟨suffix,hist⟩ := (Appends.focus RxHistory.Event.audit RxHistory.auditEvent action) w h
    change (runPrefix (RxHistory.audit action) w h).2=h++suffix at hist
    exact ⟨suffix,by simpa only [hi.1] using hist⟩
  unique := by intro cs w h x v k left right a b; exact a.2.trans b.2.symm

def Checked.audit (action : AuditM α)
    (keeps : ∀cs,PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit action)) :
    Checked loans (RxHistory.audit action) := by
  refine ⟨ConservationSyscall.audit action,?_⟩
  intro cs w h x v k hi run
  obtain ⟨_,_,_,post⟩ := keeps cs w h hi
  rw [run] at post
  exact ⟨cs,⟨run,rfl⟩,post⟩

/-- A deferred stage selects its exact fresh removal suffix. Each concrete
use below supplies the original normal endpoint theorem for this same stage. -/
def deferred (action : RxHistory.Obs α) : Rule action where
  relation := fun cs w h x v k next=>runPrefix action w h=(.ok (x,v),k) ∧
    ∃suffix,k=h++suffix ∧ next=remaining cs (NapiCarrier.removedPackets suffix)
  source := by intro cs w h x v k next hi; exact hi.1
  appends := by rintro cs w h x v k next ⟨_,suffix,hist,_⟩; exact ⟨suffix,hist⟩
  unique := by
    rintro cs w h x v k left right ⟨_,suffix,hist,rfl⟩ ⟨_,other,hist',rfl⟩
    have same := List.append_cancel_left (hist.symm.trans hist')
    rw [same]

def Checked.deferred (action : RxHistory.Obs α)
    (normal : ∀{cs w h x v k},HolderEntry.Inv cs loans h w→
      runPrefix action w h=(.ok (x,v),k)→
      ∃suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :
    Checked loans action := by
  refine ⟨ConservationSyscall.deferred action,?_⟩
  intro cs w h x v k hi run
  obtain ⟨suffix,hist,entry⟩ := normal hi run
  exact ⟨_,⟨run,suffix,hist,rfl⟩,entry⟩

def sendWorkers : Checked loans RxHistory.runSendWorkers :=
  Checked.deferred _ HolderEntryDeferred.sendAll_normal

def timers : Checked loans RxHistory.idleTimers := ⟨HolderTrafficDispatch.idle,idle_established⟩

def afterXmit : Checked loans RxHistory.afterXmit :=
  Checked.deferred _ HolderEntryDeferred.afterXmit_normal

def afterAdvance : Checked loans RxHistory.afterAdvance :=
  Checked.deferred _ HolderEntryDeferred.afterAdvance_normal

private def fs (a : FS.M α) : Checked loans (liftPrefix (liftFS a)) :=
  Checked.lift _ (fun _initial=>productFS_spec a _ (fun _ _ _ _ hi=>hi))

private def seccomp (a : Seccomp.M α) : Checked loans (liftPrefix (liftSeccomp a)) :=
  Checked.lift _ (fun _initial=>productSeccomp_spec a _ (fun _ _ _ _ hi=>hi))

private def ambient (a : AmbientM α) : Checked loans (liftPrefix (liftAmbient a)) :=
  Checked.lift _ (fun _initial=>productAmbient_spec a _ (fun _ _ hi=>hi))

private def modifyWorld (f : World→World) (same : ∀w,wgStoreView (f w).wg=wgStoreView w.wg) :
    Checked loans (liftPrefix (modify f)) :=
  Checked.lift _ (fun _initial=>hoare_modify (P:=fun w=>wgStoreView w.wg=_initial) f (fun w hi=>(same w).trans hi))

private def routing : Checked loans (liftPrefix (getRouting : Leanux.M Net.Routing)) :=
  Checked.lift _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl)

private def current : Checked loans (liftPrefix Leanux.getCurrent) := by
  unfold Leanux.getCurrent
  exact fs (StateT.lift TaskM.getCurrent)

/-- All return-to-user callbacks remain arbitrary original product observers.
The call selects the same callback order even when dispatch returned errno. -/
def tail (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : Checked loans dispatch) (hs : Checked loans sendWorkers)
    (ht : Checked loans timers) (hr : Checked loans route) (hx : Checked loans xmit)
    (ha : Checked loans advance) (hc : Checked loans cleanup) : Checked loans (do
      let ret ← dispatch
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      match call with
      | .wgSet _ | .wgInject .. => sendWorkers; timers
      | .wgUp => sendWorkers; timers; route
      | .wgXmit .. => xmit; timers
      | .wgBatch .. => timers
      | .wgAdvance _ => advance
      | .wgNetnsClose => cleanup
      | _ => pure ()
      match call with
      | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
      | .wgAddroute .. | .wgAddaddr .. =>
        let shape := Net.Fib.shape (← liftPrefix getRouting)
        liftPrefix (modifyAmbient fun w=>{w with extraOut:=w.extraOut++[("fib_trie",shape)]})
      | _ => pure ()
      pure ret) := by
  apply Checked.bind hd
  intro ret
  apply Checked.bind
  · apply Checked.forIn
    intro c acc
    exact (seccomp (Seccomp.enterHarnessCall c)).bind (fun _=>Checked.pure (ForInStep.yield acc))
  · intro _
    apply Checked.bind (fs taskWorkRun)
    intro _
    cases call
    all_goals dsimp only
    all_goals repeat' first
      | exact hs
      | exact ht
      | exact hr
      | exact hx
      | exact ha
      | exact hc
      | exact routing
      | exact ambient _
      | exact modifyWorld _ (fun _=>rfl)
      | exact Checked.pure _
      | apply Checked.bind
      | (intro)

/-- Entry resets and the seccomp guard retain the exact original source. -/
def entry (call : Syscall) {body : RxHistory.Obs α} (hb : Checked loans body) :
    Checked loans (do
      liftPrefix (modify fun w => {w with fs := {w.fs with userOut := none,userFds := none}, seccomp := {w.seccomp with emitted := {},translatedLen := none}})
      liftPrefix (modifyWG fun g=>{g with queuedThisCall:=[]})
      liftPrefix (modifyAmbient fun a=>{a with steps:=#[],extraOut:=[],fired:=#[],netRxSections:=0,netRxSection:=0})
      match syscallNr call with
      | some nr=>liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
      | none=>
        if call.isNet && (←liftPrefix getCurrent).seccomp.mode != .disabled then
          liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
      body) := by
  apply Checked.bind
  · apply modifyWorld
    intro w
    rfl
  intro _
  apply Checked.bind
  · apply modifyWorld
    intro w
    rfl
  intro _
  apply Checked.bind
  · apply modifyWorld
    intro w
    rfl
  intro _
  cases hn : syscallNr call
  all_goals repeat' first
    | exact hb
    | exact current
    | exact seccomp _
    | exact ambient (AmbientM.unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
    | exact Checked.pure _
    | apply Checked.bind
    | apply Checked.branch
    | (intro)
    | (split)

/-- Every callback remains an arbitrary original product observer. -/
def syscallWith (call : Syscall) {dispatch : RxHistory.Obs Int}
    {sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit}
    (hd : Checked loans dispatch) (hs : Checked loans sendWorkers)
    (ht : Checked loans timers) (hr : Checked loans route) (hx : Checked loans xmit)
    (ha : Checked loans advance) (hc : Checked loans cleanup) :
    Checked loans (Configuration.syscallWith (fun {_} a=>liftPrefix a)
      dispatch sendWorkers timers route xmit advance cleanup call) :=
  entry call (tail call hd hs ht hr hx ha hc)

/-- Every original dispatch constructor has its source-selected ledger. Audit
arms retain the ledger; traffic arms retain their existing dynamic source paths. -/
def dispatch (call : Syscall) : Checked [] (RxHistory.syscallDispatch call) := by
  cases call
  case wgInject family port msg tos ll dest=>
    exact ⟨HolderTrafficDispatch.injectDispatch family port msg tos ll dest,
      injectDispatch_established family port msg tos ll dest⟩
  case wgFlood count port family messages=>
    exact ⟨ConservationSource.flood count port family messages,floodDispatch_established count port family messages⟩
  case wgBatch items waitMs=>
    exact ⟨ConservationSource.batch items,batchDispatch_established items waitMs⟩
  case wgObserve=>exact ⟨observeDispatch,observeDispatch_established⟩
  case wgSet attrs=>exact Checked.audit _ (fun _=>HolderEntryPollFree.configuration attrs)
  case wgGet ref=>exact Checked.audit _ (fun _=>HolderDumpEntry.dispatchGet ref)
  case wgGetStart ref=>exact Checked.audit _ (fun _=>HolderDumpEntry.dispatchStart ref)
  case wgGetRecv=>exact Checked.audit _ (fun _=>HolderDumpEntry.dispatchRecv)
  case wgUp=>exact Checked.audit _ (fun _=>HolderEntryPollFree.up)
  case wgXmit family addr payload opts=>exact Checked.audit _ (fun _=>HolderEntryDispatch.xmit family addr payload opts)
  case wgSetMtu n=>exact Checked.audit _ (fun _=>HolderEntryPollFree.mtu n)
  case wgDeladdr family=>exact Checked.audit _ (fun _=>HolderEntryPollFree.deladdr family)
  case wgDelroute family named dst plen oif typeCode metric=>
    exact Checked.audit _ (fun _=>HolderEntryPollFree.delroute family named dst plen oif typeCode metric)
  case wgAddroute dst plen oif typeCode metric mtu flags=>
    exact Checked.audit _ (fun _=>HolderEntryPollFree.addroute dst plen oif typeCode metric mtu flags)
  case wgAddaddr addr plen=>exact Checked.audit _ (fun _=>HolderEntryPollFree.addaddr addr plen)
  case wgAdvance ticks=>exact Checked.audit _ (fun _=>HolderEntryPollFree.advance ticks)
  case wgCreate=>exact Checked.audit _ (fun _=>HolderEntryPollFree.create)
  case wgDown=>exact Checked.audit _ (fun _=>HolderEntryPollFree.down)
  case wgDelete=>exact Checked.audit _ (fun _=>HolderEntryPollFree.delete)
  case wgNetnsClose=>exact Checked.audit _ (fun _=>HolderEntryPollFree.namespaceClose)
  case eventfd2 count flags=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.eventfd2 count flags) (by trivial))
  case dup fd=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.dup fd) (by trivial))
  case dup3 oldfd newfd flags=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.dup3 oldfd newfd flags) (by trivial))
  case close fd=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.close fd) (by trivial))
  case read fd count=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.read fd count) (by trivial))
  case write fd count buf=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.write fd count buf) (by trivial))
  case pipe2 flags=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.pipe2 flags) (by trivial))
  case fcntl fd cmd arg=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.fcntl fd cmd arg) (by trivial))
  case epollCreate1 flags=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.epollCreate1 flags) (by trivial))
  case epollCtl epfd op fd events data=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.epollCtl epfd op fd events data) (by trivial))
  case epollWait epfd maxevents timeout=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.epollWait epfd maxevents timeout) (by trivial))
  case seccompInstall via flags filter len bad mode=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.seccompInstall via flags filter len bad mode) (by trivial))
  case seccompProbe nr args target strict=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.seccompProbe nr args target strict) (by trivial))
  case seccompPrctl cmd args=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.seccompPrctl cmd args) (by trivial))
  case seccompCapdrop=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.seccompCapdrop) (by trivial))
  case seccompQuery cmd action flags=>exact Checked.audit _ (fun _=>HolderEntryPollFree.ordinary (.seccompQuery cmd action flags) (by trivial))

/-- Complete original syscall source, with no assumed output funding or
successful-dispatch condition. All four return waits follow their actual arms. -/
def syscall (call : Syscall) : Checked [] (RxHistory.syscall call) := by
  rw [Configuration.syscallRx_factor]
  exact syscallWith call (dispatch call) sendWorkers timers
    (Checked.audit _ (fun _=>HolderEntryControls.route)) afterXmit afterAdvance
    (Checked.audit _ (fun _=>HolderEntryControls.cleanup))

def rule (call : Syscall) : Rule (RxHistory.syscall call) := (syscall call).rule

theorem established (call : Syscall) : Established (rule call) [] := (syscall call).established

/-- One actual normal syscall returns its unique source-selected ledger and
funded entry, retaining exact native/world and journal endpoints. -/
theorem normal (call : Syscall) (hi : HolderEntry.Inv cs [] h w)
    (run : runPrefix (RxHistory.syscall call) w h=(.ok (result,v),k)) :
    ∃next,(rule call).relation cs w h result v k next ∧ HolderEntry.Inv next [] k v :=
  established call hi run

/-- On a Stop only the actual reached owner-safe journal is claimed; no
failed state or invented completed ledger is introduced. -/
theorem checked (call : Syscall) (hi : HolderEntry.Inv cs [] h w) :
    ∃suffix,(runPrefix (RxHistory.syscall call) w h).2=h++suffix ∧
      OwnerChecks.Safe (runPrefix (RxHistory.syscall call) w h).2 ∧
      match (runPrefix (RxHistory.syscall call) w h).1 with
      | .error _=>True
      | .ok (result,v)=>∃next,(rule call).relation cs w h result v
          (runPrefix (RxHistory.syscall call) w h).2 next ∧
          HolderEntry.Inv next [] (runPrefix (RxHistory.syscall call) w h).2 v := by
  obtain ⟨suffix,hist,safe,_⟩ := OwnerSyscalls.syscall call w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run:(runPrefix (RxHistory.syscall call) w h).1 with
  | error reason=>trivial
  | ok out=>exact normal call hi (Prod.ext run rfl)

end Leanux.Proofs.WG.Queues.RxCredits.ConservationSyscall
