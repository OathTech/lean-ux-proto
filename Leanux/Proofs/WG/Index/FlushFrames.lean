import Leanux.Proofs.WG.Index.TablePeerFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do


/-- Send-work queue bookkeeping changes neither table nor allocation cursor. -/
theorem modifySendWorkQueue_tables (f : List PeerId → List PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄
      modifyDev (fun d => { d with sendWorkQueue := f d.sendWorkQueue })
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
    {d with sendWorkQueue := f d.sendWorkQueue})}), ambient) = _ at run
  cases run
  apply tablesSafe_of_cursor _ _ _ pre
  cases device : g.dev <;> simp [TimerDiscipline.tableCursor]

/-- Peer-count accounting leaves the table and allocation cursor unchanged. -/
theorem decrementNumPeers_tables :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄
      modifyDev (fun d => { d with numPeers := d.numPeers - 1 })
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
    {d with numPeers := d.numPeers - 1})}), ambient) = _ at run
  cases run
  apply tablesSafe_of_cursor _ _ _ pre
  cases device : g.dev <;> simp [TimerDiscipline.tableCursor]

end Leanux.Proofs.WG.Index
