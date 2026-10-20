import Leanux.Proofs.WG.Origins.RetainingConfiguration
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! Original dump callbacks and transport retain the complete receiving-material
view. Cursor references may be acquired or released; no cursor validity,
peer residency or successful completion is assumed. Stops have no endpoint. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.NetlinkDump Std.Do
set_option pp.structureInstances false

/-- The conditional transport retains arbitrary actual action domains. The
socket mask is exactly the original seven-field WG store projection. -/
theorem dump_material {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => dumpView (project s)) a) :
    SameView (fun s => view (project s)) a := by
  apply ha.of_factor (fun k : WGStoreView => k.dev.map materialState) _
  intro w
  rfl

theorem wgGetDeviceDone_material (ctx : DumpCtx) :
    SameView view (wgGetDeviceDone ctx) := by
  intro initial
  unfold wgGetDeviceDone
  try material_lower
  repeat' configuration_basic (fun t => t = initial)

theorem deviceDumpHeader_material (d : Device) (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    SameView view (deviceDumpHeaderSource d ctx seq skb) :=
  sameView_of_sameWG (project := id) (deviceDumpHeader_sameWGStore d ctx seq skb)

theorem deviceDumpTail_material (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    SameView view (deviceDumpTailSource d ctx skb flags attrs) := by
  intro initial
  unfold deviceDumpTailSource
  try material_lower
  repeat' first
    | (index_material_head getPeerDump
       exact ((getPeerDump_sameWGWorld _ _ _).factor view).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem wgGetDeviceDump_material (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    SameView view (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  intro initial
  repeat' first
    | (index_material_head deviceDumpHeaderSource
       exact (deviceDumpHeader_material _ _ _ _).wp (fun t => t = initial))
    | (index_material_head deviceDumpTailSource
       exact (deviceDumpTail_material _ _ _ _ _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem netlinkDump_material (fd : Nat) : SameView view (netlinkDump fd) := by
  intro initial
  unfold netlinkDump
  repeat' first
    | (index_material_head getNlSock
       exact ((getNlSock_sameWGWorld _).factor view).wp (fun t => t = initial))
    | (index_material_head setNlSock
       exact (dump_material (project := id) (setNlSock_sameDump _ _)).wp (fun t => t = initial))
    | (index_material_head wgGetDeviceDump
       exact (wgGetDeviceDump_material _ _ _).wp (fun t => t = initial))
    | (index_material_head wgGetDeviceDone
       exact (wgGetDeviceDone_material _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem netlinkDumpStart_material (fd : Nat) (ref : DeviceRef) :
    SameView view (netlinkDumpStart fd ref) := by
  intro initial
  unfold netlinkDumpStart
  try material_lower
  repeat' first
    | (index_material_head getNlSock
       exact ((getNlSock_sameWGWorld _).factor view).wp (fun t => t = initial))
    | (index_material_head setNlSock
       exact (dump_material (project := id) (setNlSock_sameDump _ _)).wp (fun t => t = initial))
    | (index_material_head lookupInterface
       exact ((lookupInterface_sameWGWorld _).factor view).wp (fun t => t = initial))
    | (index_material_head netlinkDump
       exact (netlinkDump_material _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem netlinkRecvmsg_material (fd : Nat) : SameView view (netlinkRecvmsg fd) := by
  intro initial
  unfold netlinkRecvmsg
  repeat' first
    | (index_material_head getNlSock
       exact ((getNlSock_sameWGWorld _).factor view).wp (fun t => t = initial))
    | (index_material_head setNlSock
       exact (dump_material (project := id) (setNlSock_sameDump _ _)).wp (fun t => t = initial))
    | (index_material_head netlinkDump
       exact (netlinkDump_material _).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

theorem wgGetDevice_material (ref : DeviceRef) : SameView view (wgGetDevice ref) := by
  intro initial
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  try material_lower
  repeat' first
    | (index_material_head netlinkDumpStart
       exact (netlinkDumpStart_material _ _).wp (fun t => t = initial))
    | (index_material_head netlinkRecvmsg
       exact (netlinkRecvmsg_material _).wp (fun t => t = initial))
    | (index_material_head coalesce
       exact ((coalesce_sameWGWorld _).factor view).wp (fun t => t = initial))
    | configuration_basic (fun t => t = initial)

end Leanux.Proofs.WG.Origins.Retaining
