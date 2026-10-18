import Leanux.Proofs.WG.Roaming.RemoteDriverOuterSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Outer
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration

def xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : PrefixM Event Int :=
  syscallXmitWith Traffic.multicast Traffic.transmit family addr payload opts

theorem xmit_preserves (entry : RemoteMap) (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (Inv entry) Safe (xmit family addr payload opts) :=
  syscallXmitWith_preserves (safe entry) (wg_store_inv entry) _ _
    (Traffic.multicast_preserves entry) (Traffic.transmit_preserves entry) family addr payload opts

theorem xmit_projects (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProjectsPrefix rxEvent id (xmit family addr payload opts) (RxHistory.syscallDispatch (.wgXmit family addr payload opts)) := by
  rw [rxDispatch_xmit_factor]
  unfold RxHistory.audit
  rw [← syscallXmitWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _=>rfl)
    xmitMulticastLoopAudit
    (fun family addr packets mtu=>auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu)))
    xmitMulticastLoopAudit_appends (fun _ _ _ _=>Appends.focus _ _ _)]
  exact syscallXmitWith_projects rxEvent _ _ _ _ Traffic.multicast_projects Traffic.transmit_projects family addr payload opts

theorem xmit_appends (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Appends (xmit family addr payload opts) :=
  syscallXmitWith_appends _ _ Traffic.multicast_appends Traffic.transmit_appends family addr payload opts

def inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) : PrefixM Event Int :=
  socketCallOnWith (fun {_} a=>liftPrefix a) SENDER_FD (Traffic.inject family port msg tos ll dest)

theorem inject_preserves (entry : RemoteMap) (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (Inv entry) Safe (inject family port msg tos ll dest) :=
  socket entry _ _ (Traffic.inject_preserves entry family port msg tos ll dest)

theorem inject_projects (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsPrefix rxEvent id (inject family port msg tos ll dest)
      (RxHistory.socketCallOn SENDER_FD (RxHistory.inject family port msg tos ll dest)) :=
  socketCallOnWith_projects rxEvent _ (Traffic.inject_projects family port msg tos ll dest)

theorem inject_appends (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Appends (inject family port msg tos ll dest) :=
  socketCallOnWith_appends _ (Traffic.inject_appends family port msg tos ll dest)

def observe : PrefixM Event Int := do
  Deferred.idle
  let (ret, observed) ← liftPrefix Environment.observeTail
  liftPrefix (modifyAmbient fun w=>{w with extraOut:=["datagrams","replies","stats"].map fun k=>(k,observed.getObjValD k)})
  socketCallOnWith (fun {_} a=>liftPrefix a) LISTEN4_FD (pure ret)

theorem observe_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe observe := by
  unfold observe
  apply (Deferred.idle_preserves entry).bind
  intro _
  apply (lift_store entry Environment.observeTail observeTail_sameKernel).bind
  rintro ⟨ret,observed⟩
  have same : SameProductStore (modifyAmbient fun w=>{w with
      extraOut:=["datagrams","replies","stats"].map fun k=>(k,observed.getObjValD k)}) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value v run
    cases run
    rfl
  exact (lift_store entry _ same).bind
    (fun _=>socket entry _ _ (PrefixPreserves.pure (safe entry) ret))

theorem observe_projects : ProjectsPrefix rxEvent id observe (RxHistory.syscallDispatch .wgObserve) := by
  change ProjectsPrefix rxEvent id observe (do
    let (ret, observed) ← RxHistory.observe
    liftPrefix (modifyAmbient fun w=>{w with extraOut:=["datagrams","replies","stats"].map fun k=>(k,observed.getObjValD k)})
    RxHistory.socketCallOn LISTEN4_FD (pure ret))
  unfold observe RxHistory.observe
  rw [bind_assoc]
  apply projectsPrefix_bind rxEvent id id Deferred.idle_projects
  intro _
  apply projectsPrefix_bind rxEvent id id (projectsPrefix_lift rxEvent _)
  intro result
  exact projectsPrefix_bind rxEvent id id (projectsPrefix_lift rxEvent _)
    (fun _=>socketCallOnWith_projects rxEvent _ (projectsPrefix_pure rxEvent id result.1))

theorem observe_appends : Appends observe := by
  unfold observe
  exact Deferred.idle_appends.bind (fun _=>(Appends.lift _).bind
    (fun result=>(Appends.lift _).bind (fun _=>socketCallOnWith_appends _ (Appends.pure result.1))))

end Leanux.Proofs.WG.Roaming.RemoteDriver.Outer
