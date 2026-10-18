import Leanux.Proofs.WG.Noise.DriverTagOuterSource
import Leanux.Proofs.WG.Noise.DriverTagEnvironmentSource
import Leanux.Proofs.WG.Noise.DriverTagTrafficSource
import Leanux.Proofs.WG.Noise.DriverTagDumpSource
import Leanux.Proofs.WG.Noise.DriverTagConfigurationSource
import Leanux.Proofs.WG.Lifetimes.DispatchSource
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Syscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Leanux.Proofs.WG.Configuration

theorem lift_bind {α β : Type} (a : Leanux.M α) (f : α → Leanux.M β) :
    (liftPrefix (a >>= f) : ProductObs β) = (liftPrefix a >>= fun x => liftPrefix (f x)) := by
  funext w h
  change runPrefix (liftPrefix (a >>= f)) w h =
    runPrefix (liftPrefix a >>= fun x => liftPrefix (f x)) w h
  rw [runPrefix_lift,runPrefix_bind,runPrefix_lift]
  cases run : a.run w <;> simp [StateT.run_bind,run]

theorem lift_pure {α : Type} (x : α) : (liftPrefix (pure x) : ProductObs α) = pure x := rfl

theorem socket_lift (fd : Nat) (body : Leanux.M Int) :
    (liftPrefix (Leanux.socketCallOn fd body) : ProductObs Int) =
      socketCallOnWith (m := ProductObs) (fun {_} a => liftPrefix a) fd (liftPrefix body) := by
  simp only [Leanux.socketCallOn,socketCallOnWith,lift_bind]
  congr 1
  funext f
  split <;> simp only [lift_bind,lift_pure] <;> rfl

theorem netlink_lift (body : Leanux.M Int) :
    (liftPrefix (Leanux.netlinkRequest body) : ProductObs Int) =
      netlinkRequestWith (m := ProductObs) (fun {_} a => liftPrefix a) (liftPrefix body) := by
  simp only [Leanux.netlinkRequest,Leanux.socketCall,netlinkRequestWith,lift_bind,socket_lift,lift_pure]

theorem dump_lift (entry : TagMap) (call : NetlinkDumpCall) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (liftWG call.original)) :=
  Scheduler.lift_kept entry _ (fun initial =>
    PublicationPoll.native_product _ _ (Dump.native call initial))

theorem dump_frame {α : Type} (entry : TagMap) (action : WG.M α) (frame : SameDump action) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (liftWG action)) :=
  lift_product_frame entry _ (native_product_frame action
    (frame.of_factor (fun s => responseTagMap s.dev) tagView (fun _ => rfl)))

theorem scalar_lift (entry : TagMap) (mtu : Nat) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (Env.setMtu mtu)) := by
  apply lift_product_frame
  apply (setMtu_sameEnvScalar mtu).of_factor
    (fun s : ProductStore43 => responseTagMap s.2.2.2.dev)
  intro w
  change responseTagMap w.wg.dev = responseTagMap (w.wg.dev.map envScalarDevice)
  cases w.wg.dev <;> rfl


end Leanux.Proofs.WG.Noise.DriverTags.Syscalls
