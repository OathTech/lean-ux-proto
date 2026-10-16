import Leanux.WG.Timers

/-! The zero-key timer's immediate action is a queue operation, not a
clearance of transport keys. This contract concerns the callback only. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def keypairStore (w : World) : Option (Std.TreeMap KeypairId Keypair) :=
  w.k.wg.map (·.keypairs)

theorem expiredZeroKeyMaterial_store (pid : PeerId) :
    SameView keypairStore (expiredZeroKeyMaterial pid) := by
  apply SameView.of_wp
  intro before
  have countInc := fun old => (SameView.of_sameKernel
    (fun k => k.wg.map (·.keypairs)) (refcountInc_sameKernel old)).wp
      (fun s => s = before)
  have countDec := fun old => (SameView.of_sameKernel
    (fun k => k.wg.map (·.keypairs)) (refcountDecAndTest_sameKernel old)).wp
      (fun s => s = before)
  have queued := ((KernelFrames.recordQueued_sameWGKernel .clearPeerWorker pid).factor
    (fun s => s.wg.map (·.keypairs))).wp (fun s => s = before)
  simp only [expiredZeroKeyMaterial, peerPut, indexRemove_eq]
  mvcgen [indexUnhash, peerGet, requireNotPending, getPeer,
    getDev, getK, setPeer, modifyDev, modifyK, indexRemove, retirePeerUnits,
    branch, invariant, unsupported, countInc, countDec, queued]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [keypairStore, wgKernelView, WGKernelView.ofKernel,
    Option.map_map, Function.comp_def]

end Leanux.Proofs.WG.KeyTimes
