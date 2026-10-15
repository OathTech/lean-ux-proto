import Leanux.Proofs.WG.Index.ConsumeFrames
import Leanux.Proofs.WG.Index.SendSource
import Leanux.WG.Receive

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Every original early return and failure-side peer release remains in the
consumer. This is table safety, not a statement of successful authentication. -/
theorem consumeInitiation_tables (msg : List UInt8) : Ensures (consumeInitiation msg)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hl := pubkeyLookup_tables
  have hf := peerPut_tables
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  have he := messageEphemeral_kernel_spec TablesSafeKernel
  have hd := mixDh_kernel_spec TablesSafeKernel
  have hs := mixPrecomputedDh_kernel_spec TablesSafeKernel
  have hm := messageDecrypt_kernel_spec TablesSafeKernel
  have hp := setPeer_tables
  rw [ensures_iff]
  mvcgen -trivial [consumeInitiation, WG.orM, getPeer, getDev, getK,
    branch, branchCmp, invariant, hl, hf, hh, he, hd, hs, hm, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals trivial

theorem consumeResponse_tables (msg : List UInt8) : Ensures (consumeResponse msg)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hl := indexLookup_tables
  have hf := peerPut_tables
  have he := messageEphemeral_kernel_spec TablesSafeKernel
  have hd := mixDh_kernel_spec TablesSafeKernel
  have hk := kdf_kernel_spec TablesSafeKernel
  have ho := kdfOut_kernel_spec TablesSafeKernel
  have hm := messageDecrypt_kernel_spec TablesSafeKernel
  have hp := setPeer_tables
  rw [ensures_iff]
  mvcgen [consumeResponse, getPeer, getDev, getK,
    branch, invariant, hl, hf, he, hd, hk, ho, hm, hp]

theorem cookieMessageConsume_tables (msg : List UInt8) : Ensures (cookieMessageConsume msg)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hl := indexLookup_tables
  have hf := peerPut_tables
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  have hp := setPeer_tables
  rw [ensures_iff]
  mvcgen [cookieMessageConsume, getPeer, getDev, getK,
    branch, invariant, hl, hf, hh, hp]

end Leanux.Proofs.WG.Index
