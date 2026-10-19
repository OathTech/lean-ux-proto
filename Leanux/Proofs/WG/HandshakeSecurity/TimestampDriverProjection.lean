import Leanux.Proofs.WG.HandshakeSecurity.TimestampDriverSource
import Leanux.Proofs.WG.HandshakeSecurity.NativeDriver

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampDriver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open Origins.HandshakeSources Driver

open Lean Meta Elab Tactic in
elab "timestamp_project_callback " source:ident " using " proof:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateProjectsPrefix do throwError "not a projection"
  let args := target.getAppArgs
  let action := args[args.size - 2]!.consumeMData.headBeta
  let .fvar fn := action.getAppFn | throwError "not a callback"
  unless (← fn.getDecl).userName.eraseMacroScopes == source.getId.eraseMacroScopes do
    throwError "different callback"
  evalTactic (← `(tactic| exact $proof _))

private theorem response_projects
    (sg : PeerId → WGPrefix TimestampReceipt Bool) (sa : PeerId → WGPrefix Empty Bool)
    (kg : PeerId → WGPrefix TimestampReceipt Unit) (ka : PeerId → WGPrefix Empty Unit)
    (hs : ∀ pid, StateProjectsPrefix NativeDriver.erase id (sg pid) (sa pid)) (pid : PeerId) :
    StateProjectsPrefix NativeDriver.erase id (responseWith (ops sg kg) pid)
      (responseWith (AuthenticatedEffects.HandshakeWorker.ops sa ka) pid) := by
  let rho : TimestampReceipt → Option Empty := NativeDriver.erase
  change StateProjectsPrefix rho id _ _
  unfold responseWith
  simp only [ops,Worker.ops,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | timestamp_project_callback sg using hs
    | driver_state_step rho

private theorem after_mac_projects
    (sg : PeerId → WGPrefix TimestampReceipt Bool) (sa : PeerId → WGPrefix Empty Bool)
    (kg : PeerId → WGPrefix TimestampReceipt Unit) (ka : PeerId → WGPrefix Empty Unit)
    (hs : ∀ pid, StateProjectsPrefix NativeDriver.erase id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix NativeDriver.erase id (kg pid) (ka pid))
    (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StateProjectsPrefix NativeDriver.erase id (afterMacWith (ops sg kg) msg src loaded mac)
      (afterMacWith (AuthenticatedEffects.HandshakeWorker.ops sa ka) msg src loaded mac) := by
  let rho : TimestampReceipt → Option Empty := NativeDriver.erase
  change StateProjectsPrefix rho id _ _
  unfold afterMacWith
  simp only [ops,Worker.ops,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (maintenance_head consumeObserved; exact NativeDriver.state_erasure (consume_erases _))
    | (maintenance_head responseWith; exact response_projects sg sa kg ka hs _)
    | timestamp_project_callback sg using hs
    | timestamp_project_callback kg using hk
    | driver_state_step rho

private theorem reception_projects
    (sg : PeerId → WGPrefix TimestampReceipt Bool) (sa : PeerId → WGPrefix Empty Bool)
    (kg : PeerId → WGPrefix TimestampReceipt Unit) (ka : PeerId → WGPrefix Empty Unit)
    (hs : ∀ pid, StateProjectsPrefix NativeDriver.erase id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix NativeDriver.erase id (kg pid) (ka pid))
    (msg : List UInt8) (src : SkbSource) :
    StateProjectsPrefix NativeDriver.erase id (receptionWith (ops sg kg) msg src)
      (receptionWith (AuthenticatedEffects.HandshakeWorker.ops sa ka) msg src) := by
  let rho : TimestampReceipt → Option Empty := NativeDriver.erase
  change StateProjectsPrefix rho id _ _
  unfold receptionWith
  simp only [ops,Worker.ops,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (maintenance_head afterMacWith; exact after_mac_projects sg sa kg ka hs hk _ _ _ _)
    | driver_state_step rho

theorem worker_projects
    (sg : PeerId → WGPrefix TimestampReceipt Bool) (sa : PeerId → WGPrefix Empty Bool)
    (kg : PeerId → WGPrefix TimestampReceipt Unit) (ka : PeerId → WGPrefix Empty Unit)
    (hs : ∀ pid, StateProjectsPrefix NativeDriver.erase id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix NativeDriver.erase id (kg pid) (ka pid)) :
    StateProjectsPrefix NativeDriver.erase id (worker sg kg)
      (AuthenticatedEffects.HandshakeWorker.source sa ka) := by
  change StateProjectsPrefix NativeDriver.erase id (worker sg kg)
    (stepWith (AuthenticatedEffects.HandshakeWorker.ops sa ka))
  let rho : TimestampReceipt → Option Empty := NativeDriver.erase
  change StateProjectsPrefix rho id _ _
  unfold worker stepWith
  simp only [ops,Worker.ops,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (maintenance_head receptionWith; exact reception_projects sg sa kg ka hs hk _ _)
    | driver_state_step rho

theorem native_projection : Driver.HooksProjects NativeDriver.erase hooks NativeDriver.hooks where
  handshake := worker_projects
  flushedSend := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  candidate := ⟨id,fun _ _ => projectsPrefix_pure NativeDriver.erase id 0,
    fun _ => projectsPrefix_pure NativeDriver.erase id ()⟩
  prepare := projectsPrefix_lift NativeDriver.erase _
  counterCheck := fun _ _ => (Driver.Projection.state_lift NativeDriver.erase _).liftWGObserver NativeDriver.erase id
  timerSelected := fun _ _ _ _ _ => projectsPrefix_pure NativeDriver.erase id ()
  selection := fun _ => Driver.Projection.state_lift NativeDriver.erase _
  confirmation := fun _ _ => Driver.Projection.state_lift NativeDriver.erase _
  session := fun _ => Driver.Projection.state_lift NativeDriver.erase _
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

end Leanux.Proofs.WG.HandshakeSecurity.TimestampDriver
