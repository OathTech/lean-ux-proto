import Leanux.Proofs.Framing.Syscalls
import Leanux.Proofs.WG.Keypairs.Frames.FS
import Leanux.Proofs.WG.Keypairs.OrdinaryRules

/-! Ordinary framing through syscall wrappers with an explicit contract for
the enclosed action; namespace descriptor closure preserves the snapshot. -/

namespace Leanux.Proofs.WG.Keypairs.SyscallFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open Leanux.Proofs.WG.Keypairs.KernelFrames Leanux.Proofs.WG.Keypairs.FSFrames

set_option maxHeartbeats 800000
set_option pp.structureInstances false

theorem socketCallOn_ordinary (fd : Nat) (body : M Int) (hb : OrdinaryAction body) :
    OrdinaryAction (socketCallOn fd body) := by
  have body_spec (P : Snapshot → Prop) (hp : Stable P) := hb.wp P hp
  frame_ordinary [socketCallOn] using [fdget_spec, fdput_spec] ordinary [body_spec]

theorem socketCallOn_spec (P : Snapshot → Prop) (hp : Stable P)
    (fd : Nat) (body : M Int) (hb : OrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ socketCallOn fd body
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (socketCallOn_ordinary fd body hb).wp P hp

theorem socketCall_ordinary (body : M Int) (hb : OrdinaryAction body) :
    OrdinaryAction (socketCall body) := socketCallOn_ordinary _ body hb

theorem socketCall_spec (P : Snapshot → Prop) (hp : Stable P)
    (body : M Int) (hb : OrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ socketCall body
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (socketCall_ordinary body hb).wp P hp

theorem netlinkRequest_ordinary (body : M Int) (hb : OrdinaryAction body) :
    OrdinaryAction (netlinkRequest body) := by
  have body_spec (P : Snapshot → Prop) (hp : Stable P) := hb.wp P hp
  frame_ordinary [netlinkRequest, socketCall, socketCallOn]
    using [fdget_spec, fdput_spec, skipCut_spec] ordinary [body_spec]

theorem netlinkRequest_spec (P : Snapshot → Prop) (hp : Stable P)
    (body : M Int) (hb : OrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ netlinkRequest body
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (netlinkRequest_ordinary body hb).wp P hp

theorem rtnetlinkRequest_ordinary (body : M Int) (hb : OrdinaryAction body) :
    OrdinaryAction (rtnetlinkRequest body) := by
  have body_spec (P : Snapshot → Prop) (hp : Stable P) := hb.wp P hp
  frame_ordinary [rtnetlinkRequest, socketCallOn]
    using [fdget_spec, fdput_spec, skipCut_spec, setFile_spec, freeFile_spec,
      setFdtSlot_spec, setFdtOpen_spec, setFdtCloexec_spec] ordinary [body_spec]

theorem rtnetlinkRequest_spec (P : Snapshot → Prop) (hp : Stable P)
    (body : M Int) (hb : OrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ rtnetlinkRequest body
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (rtnetlinkRequest_ordinary body hb).wp P hp

theorem netnsClose_sameSnapshot : SameSnapshot netnsClose := by
  exact sameSnapshot_of_sameWGKernel Framing.SyscallFrames.netnsClose_sameWGKernel

theorem netnsClose_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ netnsClose
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := netnsClose_sameSnapshot.wp P

end Leanux.Proofs.WG.Keypairs.SyscallFrames
