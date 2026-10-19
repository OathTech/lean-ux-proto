import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueJournalConfiguration
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueDispatch
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverControl
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Actual outer source transport combines physical input validity and retained
history on the existing Driver and initialized Runner, including Stop prefixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity
variable {E : Type} {Valid : List UInt8 → Prop} {Safe : List E → Prop}
  {hooks : Driver.Hooks E} {ρ : E → Option TransmitSecurity.Journal.Event}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem wg_stable_outer (h : List E) (w v : World) (same : wgStoreView v.wg=wgStoreView w.wg)
    (before : ProductInv Valid Safe h w) : ProductInv Valid Safe h v :=
  ⟨transport (w:=w.wg) (v:=v.wg) (congrArg (fun s : WGStoreView=>s.dev.map (fun (d : Device)=>d.handshakeQueue)) same) before.1,before.2⟩

theorem product_control (action : Leanux.M α) (same : SameView HandshakeLengths.productView action) :
    ProductSafe Valid Safe (liftPrefix action) := product_lift _ _ action (product_frame same)

theorem product_fs (action : FS.M α) : ProductSafe Valid Safe (liftPrefix (liftFS action)) :=
  product_control _ (Control.fs action)
theorem product_seccomp (action : Seccomp.M α) : ProductSafe Valid Safe (liftPrefix (liftSeccomp action)) :=
  product_control _ (Control.seccomp action)
theorem product_task (action : TaskM α) : ProductSafe Valid Safe (liftPrefix (liftTask action)) :=
  product_control _ (Control.task action)
theorem product_routing (action : Net.M α) : ProductSafe Valid Safe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_control _ (Control.route action)
theorem product_read : ProductSafe Valid Safe (liftPrefix (get : Leanux.M World)) :=
  product_control _ Control.read
theorem product_modify (f : World→World) (same : ∀w, HandshakeLengths.productView (f w)=HandshakeLengths.productView w) :
    ProductSafe Valid Safe (liftPrefix (_root_.modify f)) := product_control _ (Control.edit f same)
theorem product_editEnv (f : EnvWorld→EnvWorld) : ProductSafe Valid Safe (liftPrefix (modifyEnv f)) :=
  product_control _ (Control.env f)
theorem product_readFiles : ProductSafe Valid Safe (liftPrefix (getFiles : Leanux.M FilesStruct)) :=
  product_control _ Control.files_read
theorem product_readTask (t : TaskRef) : ProductSafe Valid Safe (liftPrefix (getTask t : Leanux.M Task)) :=
  product_control _ (Control.task_read t)
theorem product_modifyFiles (f : FilesStruct→FilesStruct) : ProductSafe Valid Safe (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  product_control _ (Control.files_edit f)

macro "handshake_journal_outer_base" : tactic => `(tactic| first
  | origin_carrier_join_let
  | origin_carrier_join_use
  | (scheduler_preserve_at liftSeccomp; exact product_seccomp _)
  | (scheduler_preserve_at liftFS; exact product_fs _)
  | (scheduler_preserve_at liftTask; exact product_task _)
  | (scheduler_preserve_at get; exact product_read)
  | (scheduler_preserve_at getFiles; exact product_readFiles)
  | (scheduler_preserve_at getTask; exact product_readTask _)
  | (scheduler_preserve_at modifyFiles; exact product_modifyFiles _)
  | (scheduler_preserve_at modify; apply product_modify; intro w; rfl)
  | (scheduler_preserve_at skipCut; exact product_ambient _ _ _)
  | (scheduler_preserve_at unsupported; exact product_ambient _ _ _)
  | (scheduler_preserve_at modifyEnv; exact product_editEnv _)
  | (scheduler_preserve_at modifyRouting; exact product_routing _)
  | (scheduler_preserve_at Env.requireIdleDevice; exact product_control _ Control.idle)
  | (scheduler_preserve_at Env.inetdevDestroy; exact product_control _ Control.inet_destroy)
  | (scheduler_preserve_at liftPrefix; first
     | exact product_seccomp _ | exact product_fs _ | exact product_task _ | exact product_routing _)
  | origin_carrier_reduce)

macro "handshake_journal_outer_step " c:ident : tactic => `(tactic| first
  | handshake_journal_outer_base
  | handshake_journal_deferred_step $c)

theorem socket_call (fd : Nat) (body : PrefixM E Int) (hb : ProductSafe Valid Safe body) :
    ProductSafe Valid Safe (socketCallOnWith (fun {_} a=>liftPrefix a) fd body) := by
  change PrefixPreserves (ProductInv Valid Safe) Safe _
  unfold socketCallOnWith
  exact (product_fs (fdget fd)).bind fun f=>PrefixPreserves.ite _
    (fun _=>product_pure _ _ _) (fun _=>hb.bind fun ret=>(product_fs (fdput f)).bind fun _=>product_pure _ _ ret)

theorem netlink (body : PrefixM E Int) (hb : ProductSafe Valid Safe body) :
    ProductSafe Valid Safe (netlinkRequestWith (fun {_} a=>liftPrefix a) body) := by
  change PrefixPreserves (ProductInv Valid Safe) Safe _
  unfold netlinkRequestWith
  exact (socket_call _ _ ((product_ambient _ _ (AmbientM.skipCut allocCuts)).bind fun _=>
    hb.bind fun ret=>(product_ambient _ _ (AmbientM.skipCut allocCuts)).bind fun _=>product_pure _ _ ret)).bind
      fun ret=>socket_call _ _ (product_pure _ _ 0) |>.bind (fun _=>product_pure _ _ ret)

theorem rtnetlink (body : PrefixM E Int) (hb : ProductSafe Valid Safe body) :
    ProductSafe Valid Safe (rtnetlinkRequestWith (fun {_} a=>liftPrefix a) body) := by
  change PrefixPreserves (ProductInv Valid Safe) Safe _
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (scheduler_preserve_at socketCallOnWith; apply socket_call
       change PrefixPreserves (ProductInv Valid Safe) Safe _)
    | handshake_journal_outer_base
    | (nonce_product_head Pure.pure; exact product_pure _ _ _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | maintenance_intro
    | (with_reducible split)
    | dsimp (config:={failIfUnchanged:=true}) only

theorem retained (c : Contracts Valid Safe hooks ρ) (call : Syscall) (kept : DispatchRetained call) :
    ProductSafe Valid Safe (Driver.retainedObserved hooks call) := by
  have history : Driver.ProductHistorySafe Safe (Driver.retainedObserved hooks call) :=
    (show Driver.retainedObserved (quietHooks hooks) call=Driver.retainedObserved hooks call from rfl) ▸
      Driver.retained_history c.quiet call
  have projected:=Projection.product (Driver.retained_projects c.projects call) (Driver.retained_projects TransmitSecurity.Journal.hooks_projects call)
  rw [Driver.nonce_retainedObserved_eq] at projected
  exact product_native history projected (Nonce.retainedObserved_erases call) (product_frame (Control.retained call kept))

theorem env_delete (c : Contracts Valid Safe hooks ρ) : ProductSafe Valid Safe (Driver.envDeleteObserved hooks) := by
  change PrefixPreserves (ProductInv Valid Safe) Safe _
  unfold Driver.envDeleteObserved HandshakeSecurity.SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' first
    | (scheduler_preserve_at Driver.downObserved; exact state_product (down c))
    | (scheduler_preserve_at Driver.destructObserved; exact state_product (destroy c))
    | (scheduler_preserve_at mayHaveSlept; exact product_wg _ (kernel mayHaveSlept_sameWGStore))
    | handshake_journal_outer_step c

theorem observe (c : Contracts Valid Safe hooks ρ) : ProductSafe Valid Safe (Driver.observeObserved hooks) := by
  unfold Driver.observeObserved
  apply (idle_timers c).bind
  intro _
  have projected:=AuthenticatedEffects.DeliverySource.observe_projects ρ _ _ c.projects.deliver
  change ProjectsPrefix ρ id _ (AuthenticatedEffects.DeliverySource.observeWith (liftPrefix Env.deliverSent)) at projected
  rw [AuthenticatedEffects.DeliverySource.observe_native] at projected
  exact product_native
    (AuthenticatedEffects.DeliverySource.observe_history Safe _ c.quiet.deliver)
    projected (erasesPrefix_lift _) (product_frame (Control.store observeTail_sameKernel))

theorem dispatch_observe (c : Contracts Valid Safe hooks ρ) : ProductSafe Valid Safe (Driver.dispatchObserveObserved hooks) := by
  unfold Driver.dispatchObserveObserved
  apply (observe c).bind
  rintro ⟨ret,json⟩
  exact (product_ambient _ _ _).bind fun _=>socket_call _ _ (product_pure _ _ ret)

theorem dispatch (c : Contracts HeaderLength.Valid Safe hooks ρ) (call : Syscall) :
    ProductSafe HeaderLength.Valid Safe (Driver.dispatchObserved hooks call) := by
  apply dispatchWith_preserves
  · exact retained c
  · intro attrs; exact netlink _ (state_product (config_device c attrs))
  · apply rtnetlink
    exact product_lift _ _ _ (PublicationPoll.native_product _ _ (create HeaderLength.Valid))
  · exact rtnetlink _ (env_delete c)
  · exact syscall_xmit c
  · intro family port message tos ll dest
    exact socket_call _ _ (inject c family port message tos ll dest)
  · exact flood c
  · exact batch c
  · exact dispatch_observe c

theorem syscall (c : Contracts HeaderLength.Valid Safe hooks ρ) (call : Syscall) :
    ProductSafe HeaderLength.Valid Safe (Driver.syscallObserved hooks call) :=
  SyscallSource.preserves (I:=ProductInv HeaderLength.Valid Safe) (S:=Safe)
    (fun _ _ before=>before.2) wg_stable_outer call _ _ _ _ _ _ _
    (dispatch c call) (send_workers c) (idle_timers c)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit c) (after_advance c)
    (product_control _ Control.cleanup)

/-- Header-validated queue inputs and checked actual pops suffice to preserve a
history property through the original initialized Runner, including Stop. Every
observer contract is explicit here; concrete cookie history discharges them. -/
theorem initialized (c : Contracts HeaderLength.Valid Safe hooks ρ) (empty : Safe [])
    (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Driver.executeObserved hooks trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith (ProductInv HeaderLength.Valid Safe) Safe
    (fun _ _ before=>before.2) wg_stable_outer (Driver.syscallObserved hooks) (syscall c) trace placeholders
  intro w same
  exact ⟨transport (w:=Runner.initialWG trace.net trace.bare) (v:=w.wg) (congrArg (fun s : WGStoreView=>s.dev.map (fun (d : Device)=>d.handshakeQueue)) same)
    (fixture_valid trace.net trace.bare),empty⟩

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
