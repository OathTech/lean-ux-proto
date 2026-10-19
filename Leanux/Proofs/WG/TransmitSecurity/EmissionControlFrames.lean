import Leanux.Proofs.WG.TransmitSecurity.EmissionOuterFrames
import Leanux.Proofs.WG.TransmitSecurity.EmissionDumpFrames
import Leanux.Proofs.WG.Lifetimes.DispatchSource

/-! Quiet native controls retain the actual sent buffer. Timer execution and
send callbacks remain separate observed operations. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EmissionControl
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues AuthenticatedEffects EmissionOuter

theorem device_read : SameView WGWorld.sent getDev := by
  sent_frame [] using []

theorem native_mtu (mtu : Int) : SameView WGWorld.sent (WG.setMtu mtu) := by
  sent_frame [WG.setMtu] using []

macro "control_source" "[" fs:ident,* "]" : tactic => `(tactic|
  (intro initial
   change Preserves (fun w : World => Sent w = initial) _
   have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => Sent w = initial)
       (monadLift a : Leanux.M α) := ambient a initial
   have routes {α : Type} (a : Net.M α) : Preserves (fun w : World => Sent w = initial)
       (monadLift a : Leanux.M α) := routing a initial
   have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Sent w = initial)
       (monadLift a : Leanux.M α) := fs a initial
   have worldRead : Preserves (fun w : World => Sent w = initial) (get : Leanux.M World) := read initial
   have wgRead : Preserves (fun w : World => Sent w = initial) (getWG : Leanux.M WGWorld) := read_wg initial
   have devRead : Preserves (fun w : World => Sent w = initial)
       (monadLift getDev : Leanux.M Device) := wg _ device_read initial
   have mtuWrite (mtu : Int) : Preserves (fun w : World => Sent w = initial)
       (monadLift (WG.setMtu mtu) : Leanux.M Int) := wg _ (native_mtu mtu) initial
   have envEdit (f : EnvWorld → EnvWorld) : Preserves (fun w : World => Sent w = initial)
       (modifyEnv f) := env f initial
   routing_tx_source [$fs,*] using [effects,routes,files,worldRead,wgRead,devRead,mtuWrite,envEdit]
   all_goals first | exact hoare_throw _ | exact edit _ (fun _ => rfl) initial))

theorem add_route (dst plen oif typeCode metric mtu nlflags : Nat) :
    SameView Sent (Env.wgAddroute dst plen oif typeCode metric mtu nlflags) := by
  control_source [Env.wgAddroute,invariant]

theorem add_addr (addr plen : Nat) : SameView Sent (Env.wgAddaddr addr plen) := by
  control_source [Env.wgAddaddr,getRouting,modifyRouting,unsupported]

theorem del_route (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    SameView Sent (Env.wgDelroute family named dst plen oif typeCode metric) := by
  control_source [Env.wgDelroute,getRouting,modifyRouting,unsupported]

theorem del_addr (family : Nat) : SameView Sent (Env.wgDeladdr family) := by
  control_source [Env.wgDeladdr,getRouting,modifyRouting,unsupported]

theorem advance (ticks : Nat) : SameView Sent (Env.advance ticks) := by
  control_source [Env.advance,getAmbient,hidden,unsupported,modifyWG]

theorem mtu (value : Nat) : SameView Sent (Env.setMtu value) := by
  control_source [Env.setMtu,Env.inetdevDestroy,getRouting,modifyRouting,unsupported,skipCut]

theorem netns_close : SameView Sent Leanux.netnsClose := by
  control_source [Leanux.netnsClose,getRouting,getEnv,unsupported,invariant]

end Leanux.Proofs.WG.TransmitSecurity.EmissionControl
