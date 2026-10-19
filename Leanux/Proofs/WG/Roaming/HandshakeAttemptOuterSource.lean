import Leanux.Proofs.WG.Roaming.HandshakeAttemptTrafficSource
import Leanux.Proofs.WG.Roaming.RemoteOuterRulesSource
import Leanux.Proofs.WG.Lifetimes.DispatchSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport
open Leanux Leanux.WG Leanux.Proofs.Logged Queues Lifetimes Configuration
variable {Attempt : Type} {valid : List Attempt → Prop}

namespace Outer

theorem socket_preserves (valid : List Attempt → Prop) (fd : Nat)
    (body : PrefixM (Event Attempt) Int)
    (checked : PrefixPreserves (fun h _=>Safe valid h) (Safe valid) body) :
    PrefixPreserves (fun h _=>Safe valid h) (Safe valid)
      (socketCallOnWith (fun {_} a=>liftPrefix a) fd body) :=
  RemoteOuterRules.socket (fun h _=>Safe valid h) (Safe valid) (fun _ _ hi=>hi)
    (fun action=>lifted valid (liftFS action)) fd body checked

def inject (r : Receive Attempt valid) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) : PrefixM (Event Attempt) Int :=
  socketCallOnWith (fun {_} a=>liftPrefix a) SENDER_FD
    (Traffic.inject r family port msg tos ll dest)

theorem inject_preserves (r : Receive Attempt valid) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h _=>Safe valid h) (Safe valid)
      (inject r family port msg tos ll dest) :=
  socket_preserves valid _ _ (Traffic.inject_preserves r family port msg tos ll dest)

theorem inject_projects (r : Receive Attempt valid) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsPrefix rxEvent id (inject r family port msg tos ll dest)
      (RxHistory.socketCallOn SENDER_FD (RxHistory.inject family port msg tos ll dest)) :=
  socketCallOnWith_projects rxEvent _ (Traffic.inject_projects r family port msg tos ll dest)

theorem inject_appends (r : Receive Attempt valid) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Appends (inject r family port msg tos ll dest) :=
  socketCallOnWith_appends _ (Traffic.inject_appends r family port msg tos ll dest)

def observe (r : Receive Attempt valid) : PrefixM (Event Attempt) Int := do
  Deferred.idle r
  let (ret,observed) ← liftPrefix Environment.observeTail
  liftPrefix (modifyAmbient fun w=>{w with extraOut:=
    (["datagrams","replies","stats"].map (fun k=>(k,observed.getObjValD k)))})
  socketCallOnWith (fun {_} a=>liftPrefix a) LISTEN4_FD (pure ret)

theorem observe_preserves (r : Receive Attempt valid) :
    PrefixPreserves (fun h _=>Safe valid h) (Safe valid) (observe r) := by
  unfold observe
  apply (Deferred.idle_preserves r).bind
  intro _
  apply (lifted valid Environment.observeTail).bind
  rintro ⟨ret,observed⟩
  exact (lifted valid _).bind
    (fun _=>socket_preserves valid _ _ (PrefixPreserves.pure (I:=fun h _=>Safe valid h) (S:=Safe valid) (fun _ _ hi=>hi) ret))

theorem observe_projects (r : Receive Attempt valid) :
    ProjectsPrefix rxEvent id (observe r) (RxHistory.syscallDispatch .wgObserve) := by
  change ProjectsPrefix rxEvent id (observe r) (do
    let (ret,observed) ← RxHistory.observe
    liftPrefix (modifyAmbient fun w=>{w with extraOut:=
      (["datagrams","replies","stats"].map (fun k=>(k,observed.getObjValD k)))})
    RxHistory.socketCallOn LISTEN4_FD (pure ret))
  unfold observe RxHistory.observe
  rw [bind_assoc]
  apply projectsPrefix_bind rxEvent id id (Deferred.idle_projects r)
  intro _
  apply projectsPrefix_bind rxEvent id id (projectsPrefix_lift rxEvent _)
  intro result
  exact projectsPrefix_bind rxEvent id id (projectsPrefix_lift rxEvent _)
    (fun _=>socketCallOnWith_projects rxEvent _ (projectsPrefix_pure rxEvent id result.1))

theorem observe_appends (r : Receive Attempt valid) : Appends (observe r) := by
  unfold observe
  exact (Deferred.idle_appends r).bind (fun _=>(Appends.lift _).bind
    (fun result=>(Appends.lift _).bind
      (fun _=>socketCallOnWith_appends _ (Appends.pure result.1))))

end Outer

namespace Dispatch

def call (r : Receive Attempt valid) (c : Syscall) : PrefixM (Event Attempt) Int :=
  dispatchWith (fun c=>old (RxHistory.syscallDispatch c))
    (fun attrs=>old (RxHistory.syscallDispatch (.wgSet attrs)))
    (old (RxHistory.syscallDispatch .wgCreate)) (old (RxHistory.syscallDispatch .wgDelete))
    (fun family addr payload opts=>old (RxHistory.syscallDispatch (.wgXmit family addr payload opts)))
    (Outer.inject r) (Traffic.flood r) (Traffic.batch r) (Outer.observe r) c

theorem call_preserves (r : Receive Attempt valid) (c : Syscall) :
    PrefixPreserves (fun h _=>Safe valid h) (Safe valid) (call r c) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _
    (fun _ _=>old_preserves valid _) (fun _=>old_preserves valid _)
    (old_preserves valid _) (old_preserves valid _) (fun _ _ _ _=>old_preserves valid _)
    (Outer.inject_preserves r) (Traffic.flood_preserves r) (Traffic.batch_preserves r)
    (Outer.observe_preserves r) c

theorem call_projects (r : Receive Attempt valid) (c : Syscall) :
    ProjectsPrefix rxEvent id (call r c) (RxHistory.syscallDispatch c) := by
  rw [rxDispatch_source]
  exact dispatchWith_projects _ _ _ _ _ _ _ _ _ rxEvent _ _ _ _ _ _ _ _ _
    (fun c _=>old_projects _ (RxHistory.syscallDispatch_appends c))
    (fun attrs=>old_projects _ (RxHistory.syscallDispatch_appends (.wgSet attrs)))
    (old_projects _ (RxHistory.syscallDispatch_appends .wgCreate))
    (old_projects _ (RxHistory.syscallDispatch_appends .wgDelete))
    (fun family addr payload opts=>old_projects _ (RxHistory.syscallDispatch_appends (.wgXmit family addr payload opts)))
    (Outer.inject_projects r) (Traffic.flood_projects r) (Traffic.batch_projects r)
    (Outer.observe_projects r) c

theorem call_appends (r : Receive Attempt valid) (c : Syscall) : Appends (call r c) := by
  cases c
  case wgInject family port msg tos ll dest => exact Outer.inject_appends r family port msg tos ll dest
  case wgFlood count port family msgs => exact Traffic.flood_appends r count port family msgs
  case wgBatch items _ => exact Traffic.batch_appends r items
  case wgObserve => exact Outer.observe_appends r
  all_goals exact old_appends _

theorem call_erases (r : Receive Attempt valid) (c : Syscall) :
    ErasesPrefix (call r c) (Leanux.dispatch c) :=
  projects_erases (call_projects r c) (RxHistory.syscallDispatch_erases c)

end Dispatch


end Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport
