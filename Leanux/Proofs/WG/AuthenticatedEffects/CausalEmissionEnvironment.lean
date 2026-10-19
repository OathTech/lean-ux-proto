import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCarrierConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionEnvironmentFrames

/-! Environment lifecycle and syscall wrappers preserve sent occurrences and
delivery certificates. Actual queued sends are retained inside lifecycle calls. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity
open Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem fs (action : FS.M α) : ProductSafe (liftPrefix (liftFS action)) :=
  native _ (EmissionOuter.fs action)
theorem seccomp (action : Seccomp.M α) : ProductSafe (liftPrefix (liftSeccomp action)) :=
  native _ (EmissionOuter.seccomp action)
theorem task (action : TaskM α) : ProductSafe (liftPrefix (liftTask action)) :=
  native _ (EmissionOuter.task action)
theorem routing (action : Net.M α) : ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  native _ (EmissionOuter.routing action)
theorem read : ProductSafe (liftPrefix (get : Leanux.M World)) := native _ EmissionOuter.read

theorem edit (f : World → World) (same : ∀ w, EmissionOuter.Sent (f w) = EmissionOuter.Sent w) :
    ProductSafe (liftPrefix (modify f)) := native _ (EmissionOuter.edit f same)

theorem env (f : EnvWorld → EnvWorld) : ProductSafe (liftPrefix (modifyEnv f)) :=
  native _ (EmissionOuter.env f)

theorem read_files : ProductSafe (liftPrefix (getFiles : Leanux.M FilesStruct)) := by
  apply native
  intro initial
  change Preserves (fun w : World => EmissionOuter.Sent w = initial) _
  have taskFrame (a : TaskM Task) : Preserves (fun w : World => EmissionOuter.Sent w = initial)
      (monadLift a : Leanux.M Task) := EmissionOuter.fs (monadLift a : FS.M Task) initial
  routing_tx_source [getFiles,getTask] using [taskFrame]

theorem read_task (t : TaskRef) : ProductSafe (liftPrefix (getTask t : Leanux.M Task)) :=
  fs (monadLift (TaskM.getTask t) : FS.M Task)

theorem edit_files (f : FilesStruct → FilesStruct) : ProductSafe (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  fs (monadLift (TaskM.modifyTask .task (fun t => {t with files := f t.files})) : FS.M Unit)

macro "emission_outer_step" : tactic => `(tactic| first
  | (emission_carrier_native_head liftSeccomp; exact seccomp _)
  | (emission_carrier_native_head liftFS; exact fs _)
  | (emission_carrier_native_head liftTask; exact task _)
  | (emission_carrier_native_head get; exact read)
  | (emission_carrier_native_head getFiles; exact read_files)
  | (emission_carrier_native_head getTask; exact read_task _)
  | (emission_carrier_native_head modifyFiles; exact edit_files _)
  | (emission_carrier_native_head modify; exact edit _ (fun _ => rfl))
  | (emission_carrier_native_head skipCut; exact ambient _)
  | (emission_carrier_native_head modifyEnv; exact env _)
  | (emission_carrier_native_head liftRouting; exact routing _)
  | solve | emission_deferred_native
  | (emission_carrier_head liftPrefix; exact routing _)
  | emission_carrier_product_step)

theorem env_up : ProductSafe (envUpObserved hooks) := by
  unfold envUpObserved
  repeat' first
    | (emission_carrier_head upObserved; exact product_state up)
    | emission_outer_step

theorem env_down : ProductSafe (envDownObserved hooks) := by
  unfold envDownObserved envDownWith
  repeat' first
    | (emission_carrier_head downObserved; exact product_state down)
    | (emission_carrier_native_head Env.requireIdleDevice; exact native _ EmissionFrames.idle_device)
    | emission_outer_step

theorem env_delete : ProductSafe (envDeleteObserved hooks) := by
  unfold envDeleteObserved HandshakeSecurity.SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' first
    | (emission_carrier_head downObserved; exact product_state down)
    | (emission_carrier_head destructObserved; exact product_state destruct)
    | (emission_carrier_native_head Env.requireIdleDevice; exact native _ EmissionFrames.idle_device)
    | (emission_carrier_native_head mayHaveSlept; exact wg _ EmissionFrames.slept)
    | (emission_carrier_native_head Env.inetdevDestroy; exact native _ EmissionFrames.inetdev_destroy)
    | emission_outer_step

theorem socket_call (fd : Nat) (body : PrefixM Event Int) (hb : ProductSafe body) :
    ProductSafe (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply product_bind (fs (fdget fd))
  intro f
  apply product_ite
  · intro _; exact product_pure _
  · intro _
    exact product_bind hb (fun ret => product_bind (fs (fdput f)) (fun _ => product_pure ret))

theorem netlink (body : PrefixM Event Int) (hb : ProductSafe body) :
    ProductSafe (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply product_bind (socket_call _ _ (product_bind (ambient (AmbientM.skipCut allocCuts))
    (fun _ => product_bind hb (fun ret => product_bind (ambient (AmbientM.skipCut allocCuts))
      (fun _ => product_pure ret)))))
  intro ret
  exact product_bind (socket_call _ _ (product_pure 0)) (fun _ => product_pure ret)

theorem rtnetlink (body : PrefixM Event Int) (hb : ProductSafe body) :
    ProductSafe (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (emission_carrier_head socketCallOnWith; apply socket_call)
    | emission_outer_step

theorem retained (call : Syscall) (kept : DispatchRetained call) : ProductSafe (retainedObserved hooks call) := by
  by_cases opened : call = .wgUp
  · subst call; exact socket_call _ _ env_up
  · by_cases stopped : call = .wgDown
    · subst call; exact socket_call _ _ env_down
    · have same : retainedObserved hooks call = RetirementSecurity.NestedPeerRelease.dumpDispatch (nestedOps hooks) call := by
        cases call <;> simp_all only [retainedObserved] <;> contradiction
      rw [same]
      exact product_combine _
        (Emissions.product_native_callback _
          (CallbackFrames.dump_dispatch_quiet contributing? (fun _ => rfl) call)
          (CallbackFrames.dump_dispatch_erases call) (EmissionDispatch.quiet call kept opened stopped))
        (CallbackQuiet.product_safe (CallbackFrames.dump_dispatch_quiet delivery? (fun _ => rfl) call)
          (fun _ _ safe quiet => safe.quiet quiet))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
