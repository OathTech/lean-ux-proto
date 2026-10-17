import Leanux.Proofs.WG.Index.TablePeerFrames
import Leanux.Proofs.WG.Noise.SlotFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

section
set_option maxHeartbeats 800000

/-- An arbitrary peer write leaves the hashed table and allocation cursor unchanged. -/
theorem modifyPeer_tables (pid : PeerId) (f : Peer → Peer) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ Noise.modifyPeer pid f
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  change Ensures (do let p ← getPeer pid; setPeer pid (f p))
    TablesSafeWG (fun _ => TablesSafeWG)
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
  · intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  · intro p
    exact (ensures_iff _ _ _).mpr (setPeer_tables pid (f p))

theorem handshakeZero_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ handshakeZero pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold handshakeZero
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
  · intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  · intro p
    exact (ensures_iff _ _ _).mpr (setPeer_tables pid _)

/-- Clear-work queue bookkeeping changes neither table nor cursor. -/
theorem modifyClearWorkQueue_tables (f : List PeerId → List PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄
      modifyDev (fun d => { d with clearWorkQueue := f d.clearWorkQueue })
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
    {d with clearWorkQueue := f d.clearWorkQueue})}), ambient) = _ at run
  cases run
  apply tablesSafe_of_cursor _ _ _ pre
  cases device : g.dev <;> simp [TimerDiscipline.tableCursor]

end

end Leanux.Proofs.WG.Index
