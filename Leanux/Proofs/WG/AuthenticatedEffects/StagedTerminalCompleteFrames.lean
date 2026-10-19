import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteFacts

/-! Source-shape facts for terminal demands. Counted arity comes from the
native staged prefix partition, and supported endpoint results are not a
second terminal after the inner socket result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedProvenance HandshakeSecurity.StagedDisposal

theorem overflow_demand (part : Partition pid r.before r.after) :
    demand position (.stagedDisposal (.overflow pid r)) =
      some ⟨.counted position .overflow,part.removed⟩ := by
  simp only [demand,stagedLength,part.before,part.after,Option.map_some,Option.getD_some,List.length_drop]
  have count : part.packets.length - (part.packets.length-part.removed) = part.removed := by
    have bounded := part.bounded
    omega
  rw [count]

theorem purge_demand (part : Partition pid r.before r.after) (whole : part.removed = part.packets.length) :
    demand position (.stagedDisposal (.purge pid r)) = some ⟨.counted position .purge,part.removed⟩ := by
  simp only [demand,stagedLength,part.before,Option.map_some,Option.getD_some,whole]

theorem release_none_quiet (empty : r.value = none) : Quiet (.stagedDisposal (.release peer r)) := by
  intro position
  simp only [demand,empty,Option.map_none]

theorem release_some_demand (result : r.value = some (pid,p)) :
    demand position (.stagedDisposal (.release peer r)) = some ⟨.counted position .finalRelease,p.staged.length⟩ := by
  simp only [demand,result,Option.map_some]

theorem supported_result_quiet
    (supported : endpointFamily r.run.before.wg r.pid = AF_INET ∨ endpointFamily r.run.before.wg r.pid = AF_INET6) :
    Quiet (.sendResult r) := by
  intro position
  simp only [demand,ite_eq_left supported]

theorem unsupported_result_demand
    (unsupported : ¬(endpointFamily r.run.before.wg r.pid = AF_INET ∨ endpointFamily r.run.before.wg r.pid = AF_INET6)) :
    demand position (.sendResult r) = some ⟨.sendRefused position,1⟩ := by
  simp only [demand,ite_eq_right unsupported]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
