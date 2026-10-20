import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueDump
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueLifecycle
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueNapi
import Leanux.Proofs.WG.Origins.OwnerControlCalls
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

/-! Native administrative controls frame the handshake input ring. Device
creation and destruction have separate invariant contracts because their ring
can disappear or be freshly initialized. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Control
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

theorem store {a : Leanux.M α} (same : SameProductStore a) : SameView productView a :=
  same.of_factor (fun s : ProductStore43=>s.2.2.2.dev.map (·.handshakeQueue)) productView (fun _=>rfl)
theorem native {a : WG.M α} (same : SameView view a) : SameView productView (liftWG a) :=
  sameView_liftWG productView view a same (fun _ _ _ h=>h)
theorem fs (a : FS.M α) : SameView productView (liftFS a) :=
  fun initial=>productFS_spec a (fun w=>productView w=initial) (fun _ _ _ _ h=>h)
theorem task (a : TaskM α) : SameView productView (liftTask a) :=
  fun initial=>productTask_spec a (fun w=>productView w=initial) (fun _ _ _ h=>h)
theorem seccomp (a : Seccomp.M α) : SameView productView (liftSeccomp a) :=
  fun initial=>productSeccomp_spec a (fun w=>productView w=initial) (fun _ _ _ _ h=>h)
theorem route (a : Net.M α) : SameView productView (monadLift a : Leanux.M α) :=
  store (fun initial=>productRouting_spec a (·=initial))
theorem read : SameView productView (get : Leanux.M World) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v run
  cases run
  rfl
theorem edit (f : World → World) (same : ∀w, productView (f w)=productView w) :
    SameView productView (_root_.modify f : Leanux.M Unit) := by
  intro initial
  apply hoare_modify
  intro w before
  exact (same w).trans before

theorem env (f : EnvWorld → EnvWorld) : SameView productView (modifyEnv f) :=
  edit _ (fun _=>rfl)
theorem readWG : SameView productView (getWG : Leanux.M WGWorld) := store (fun initial=>productGetWG_spec (·=initial))
theorem readRoute : SameView productView (getRouting : Leanux.M Net.Routing) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v run
  cases run
  rfl
theorem files_read : SameView productView (getFiles : Leanux.M FilesStruct) := by
  unfold getFiles getTask
  exact (fs _).bind (fun _=>SameView.pure _ _)
theorem task_read (t : TaskRef) : SameView productView (getTask t : Leanux.M Task) :=
  fs (monadLift (TaskM.getTask t) : FS.M Task)
theorem files_edit (f : FilesStruct→FilesStruct) : SameView productView (modifyFiles f : Leanux.M Unit) :=
  fs (monadLift (TaskM.modifyTask .task (fun t=>{t with files:=f t.files})) : FS.M Unit)
theorem route_edit (f : Net.Routing→Net.Routing) : SameView productView (modifyRouting f : Leanux.M Unit) :=
  route _
theorem idle : SameView productView Env.requireIdleDevice :=
  store (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store)
theorem inet_destroy : SameView productView Env.inetdevDestroy :=
  store (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store)

theorem pre_exit : SameView view WG.netnsPreExit := by
  handshake_cell_source [WG.netnsPreExit] using [socket_reinit_cell,clear_endpoint_cell]

theorem cleanup : SameView productView Env.netnsCleanup := by
  have routing {α : Type} (a : Net.M α) := route a
  handshake_poll_source [Env.netnsCleanup,Env.runWorker,Env.pendingDevice,peekUnit,resolveUnit,skipCut,unsupported]
    using [routing,readRoute,env] with [pre_exit]

theorem mtu (n : Nat) : SameView productView (Env.setMtu n) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v run
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v run
  simpa only [productView,view,envScalarView,envScalarStore,envScalarDevice,
    productStoreView,wgStoreView,Option.map_map,Function.comp_def] using
    congrArg (fun s : ProductStore43=>s.2.2.2.dev.map (·.handshakeQueue)) same

macro "handshake_control_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]"
    "with" "[" natives:ident,* "]" : tactic => `(tactic|
  (have routes {α : Type} (a : Net.M α) := route a
   have files {α : Type} (a : FS.M α) := fs a
   have tasks {α : Type} (a : TaskM α) := task a
   have seccomps {α : Type} (a : Seccomp.M α) := seccomp a
   have edits (f : World→World) (h : ∀w,productView (f w)=productView w) := edit f h
   handshake_poll_source [$fs,*] using [routes,files,tasks,seccomps,read,edits,env,readWG,readRoute,files_read,task_read,files_edit,route_edit,idle,inet_destroy,$facts,*]
     with [$natives,*]
   all_goals first | rfl | exact fs _ | exact task _ | exact seccomp _ | (apply edit; intro w; rfl)))

theorem up : SameView productView Env.wgUp := by
  handshake_control_source [Env.wgUp,skipCut] using [] with [up_cell]

theorem down : SameView productView Env.wgDown := by
  handshake_control_source [Env.wgDown,skipCut,modifyRouting] using [] with [down_cell]

theorem socket (fd : Nat) (body : Leanux.M Int) (same : SameView productView body) :
    SameView productView (socketCallOn fd body) := by
  handshake_control_source [socketCallOn] using [same] with []

theorem rtnetlink (body : Leanux.M Int) (same : SameView productView body) :
    SameView productView (rtnetlinkRequest body) := by
  have sockets := fun fd body same=>socket fd body same
  handshake_control_source [rtnetlinkRequest,skipCut] using [sockets,same] with []

theorem netlink (body : Leanux.M Int) (same : SameView productView body) :
    SameView productView (netlinkRequest body) := by
  have sockets := fun fd body same=>socket fd body same
  handshake_control_source [netlinkRequest,socketCall,skipCut] using [sockets,same] with []

theorem delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    SameView productView (Env.wgDelroute family named dst plen oif typeCode metric) := by
  handshake_control_source [Env.wgDelroute,unsupported] using [] with []
theorem addroute (dst plen oif typeCode metric mtu flags : Nat) :
    SameView productView (Env.wgAddroute dst plen oif typeCode metric mtu flags) := by
  handshake_control_source [Env.wgAddroute,invariant] using [] with []
theorem addaddr (addr plen : Nat) : SameView productView (Env.wgAddaddr addr plen) := by
  handshake_control_source [Env.wgAddaddr,unsupported] using [] with []

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Control
