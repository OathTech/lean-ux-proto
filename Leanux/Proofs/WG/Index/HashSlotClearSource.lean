import Leanux.Proofs.WG.Index.HashSlotClearEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

-- Source
/-- Every normal original clear supplies its actual entry peer and ordered
three-slot certificate. Missing device/key/peer and reference failures remain
the original Stops; this derives no total-success assertion. -/
theorem keypairsClear_normal_cuts (pid : PeerId) (g out : WGWorld)
    (ambient after : Ambient) (result : Unit)
    (run : ((keypairsClear pid).run g).run ambient = .ok ((result,out),after)) :
    ∃ d p final, g.dev = some d ∧ d.peers[pid]? = some p ∧
      out.dev = some final ∧ ClearRun pid d [.next,.previous,.current] final ∧
      final.peers[pid]? = some (Config.emptyKeysPeer p) := by
  cases device : g.dev with
  | none =>
    simp [keypairsClear,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [keypairsClear,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨final,present,steps⟩ := keypairsClear_effect pid d p resident
        g ambient result out after device run
      have peer := keypairsClear_peer pid p g ambient result out after
        (by simp [peerAt,device,resident]) run
      exact ⟨d,p,final,rfl,resident,present,steps,
        by simpa [peerAt,present,Config.emptyKeysPeer] using peer⟩


end Leanux.Proofs.WG.Index
