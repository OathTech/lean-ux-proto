import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverSource
import Leanux.Proofs.WG.HandshakeSecurity.NativeDriver

namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open Origins.HandshakeSources Driver

open Lean Meta Elab Tactic in
elab "exchange_project_callback " source:ident " using " proof:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateProjectsPrefix do throwError "not a projection"
  let args := target.getAppArgs
  let action := args[args.size - 2]!.consumeMData.headBeta
  let .fvar fn := action.getAppFn | throwError "not a callback"
  unless (← fn.getDecl).userName.eraseMacroScopes == source.getId.eraseMacroScopes do
    throwError "different callback"
  evalTactic (← `(tactic| exact $proof _))

private theorem response_projects
    (sg : PeerId → WGPrefix Exchange.Event Bool) (sa : PeerId → WGPrefix Empty Bool)
    (kg : PeerId → WGPrefix Exchange.Event Unit) (ka : PeerId → WGPrefix Empty Unit)
    (hs : ∀ pid, StateProjectsPrefix NativeDriver.erase id (sg pid) (sa pid)) (pid : PeerId) :
    StateProjectsPrefix NativeDriver.erase id (responseWith (receiveOps sg kg) pid)
      (responseWith (AuthenticatedEffects.HandshakeWorker.ops sa ka) pid) := by
  let rho : Exchange.Event → Option Empty := NativeDriver.erase
  change StateProjectsPrefix rho id _ _
  unfold responseWith
  simp only [receiveOps,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (maintenance_head Exchange.createResponse; exact NativeDriver.state_erasure (Exchange.createResponse_erases _))
    | exchange_project_callback sg using hs
    | driver_state_step rho

private theorem after_mac_projects
    (sg : PeerId → WGPrefix Exchange.Event Bool) (sa : PeerId → WGPrefix Empty Bool)
    (kg : PeerId → WGPrefix Exchange.Event Unit) (ka : PeerId → WGPrefix Empty Unit)
    (hs : ∀ pid, StateProjectsPrefix NativeDriver.erase id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix NativeDriver.erase id (kg pid) (ka pid))
    (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StateProjectsPrefix NativeDriver.erase id (afterMacWith (receiveOps sg kg) msg src loaded mac)
      (afterMacWith (AuthenticatedEffects.HandshakeWorker.ops sa ka) msg src loaded mac) := by
  let rho : Exchange.Event → Option Empty := NativeDriver.erase
  change StateProjectsPrefix rho id _ _
  unfold afterMacWith
  simp only [receiveOps,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (maintenance_head Exchange.consumeInitiation; exact NativeDriver.state_erasure (Exchange.consumeInitiation_erases _))
    | (maintenance_head Exchange.consumeResponse; exact NativeDriver.state_erasure (Exchange.consumeResponse_erases _))
    | (maintenance_head responseWith; exact response_projects sg sa kg ka hs _)
    | exchange_project_callback sg using hs
    | exchange_project_callback kg using hk
    | driver_state_step rho

private theorem reception_projects
    (sg : PeerId → WGPrefix Exchange.Event Bool) (sa : PeerId → WGPrefix Empty Bool)
    (kg : PeerId → WGPrefix Exchange.Event Unit) (ka : PeerId → WGPrefix Empty Unit)
    (hs : ∀ pid, StateProjectsPrefix NativeDriver.erase id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix NativeDriver.erase id (kg pid) (ka pid))
    (msg : List UInt8) (src : SkbSource) :
    StateProjectsPrefix NativeDriver.erase id (receptionWith (receiveOps sg kg) msg src)
      (receptionWith (AuthenticatedEffects.HandshakeWorker.ops sa ka) msg src) := by
  let rho : Exchange.Event → Option Empty := NativeDriver.erase
  change StateProjectsPrefix rho id _ _
  unfold receptionWith
  simp only [receiveOps,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (maintenance_head afterMacWith; exact after_mac_projects sg sa kg ka hs hk _ _ _ _)
    | driver_state_step rho

theorem worker_projects
    (sg : PeerId → WGPrefix Exchange.Event Bool) (sa : PeerId → WGPrefix Empty Bool)
    (kg : PeerId → WGPrefix Exchange.Event Unit) (ka : PeerId → WGPrefix Empty Unit)
    (hs : ∀ pid, StateProjectsPrefix NativeDriver.erase id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix NativeDriver.erase id (kg pid) (ka pid)) :
    StateProjectsPrefix NativeDriver.erase id (worker sg kg)
      (AuthenticatedEffects.HandshakeWorker.source sa ka) := by
  change StateProjectsPrefix NativeDriver.erase id (worker sg kg)
    (stepWith (AuthenticatedEffects.HandshakeWorker.ops sa ka))
  let rho : Exchange.Event → Option Empty := NativeDriver.erase
  change StateProjectsPrefix rho id _ _
  unfold worker stepWith
  simp only [receiveOps,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (maintenance_head receptionWith; exact reception_projects sg sa kg ka hs hk _ _)
    | driver_state_step rho

theorem native_projection : Driver.HooksProjects NativeDriver.erase hooks NativeDriver.hooks where
  deliver := projectsPrefix_lift NativeDriver.erase _
  keepalivePrepare := fun _ => TransmitSecurity.Driver.Projection.state_lift NativeDriver.erase _
  handshake := worker_projects
  fixture := ⟨id,fun _ => Driver.Projection.state_pure NativeDriver.erase 0,
    fun _ => Driver.Projection.state_pure NativeDriver.erase ()⟩
  armTimer := fun _ _ _ _ => Driver.Projection.state_lift NativeDriver.erase _
  queueSend := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  flushedSend := fun pid => NativeDriver.state_erasure (flushed_erases pid)
  candidate := ⟨id,fun _ _ => projectsPrefix_pure NativeDriver.erase id 0,
    fun _ => projectsPrefix_pure NativeDriver.erase id (),
    (fun _ _ _ projected => projected)⟩
  prepare := projectsPrefix_lift NativeDriver.erase _
  counterCheck := fun _ _ => (Driver.Projection.state_lift NativeDriver.erase _).liftWGObserver NativeDriver.erase id
  timer := ⟨id,fun _ _ _ _ _ => projectsPrefix_pure NativeDriver.erase id 0,
    fun _ => projectsPrefix_pure NativeDriver.erase id ()⟩
  selection := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  confirmation := fun _ _ => Driver.Projection.state_lift NativeDriver.erase _
  session := fun pid => NativeDriver.state_erasure (Exchange.session_erases pid)
  reserve := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  allocate := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  create := fun _ _ => Driver.Projection.state_lift NativeDriver.erase _
  front := fun _ _ _ _ => Driver.Projection.state_lift NativeDriver.erase _
  poll := projectsPrefix_lift NativeDriver.erase _
  encrypt := fun _ => projectsPrefix_lift NativeDriver.erase _
  transmit := fun _ => projectsPrefix_lift NativeDriver.erase _

theorem execute_erases (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (execute trace placeholders) (Runner.executeTrace trace placeholders) :=
  NativeDriver.projects_erases hooks native_projection trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriver
