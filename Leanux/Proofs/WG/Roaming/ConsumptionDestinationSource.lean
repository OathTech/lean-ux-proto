import Leanux.Proofs.WG.Roaming.ConsumptionDestinationModel
import Leanux.Proofs.WG.Roaming.RemoteCompletionSource
import Leanux.Proofs.WG.Roaming.ConsumptionAuthenticationClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise
open Noise.ConfirmationOrder Noise.ConsumeConfirmation

theorem consumption_final_remotes (trace : Runner.Trace) (placeholders : Bool)
    (q : Record) (occurs : OccursAt trace placeholders q) :
    ConsumptionFinalRemotes q := by
  obtain ⟨pre,post,r,position,index,matched⟩ := occurs
  obtain ⟨valid,c,allocation,source,key,qeq⟩ := matched
  have obsEq : q.observation = projects r c := congrArg Record.observation qeq
  have endpoint := ConsumedEndpoint.initialized_endpoint trace placeholders pre post
    q.occurrence q.skb q.packetStamp r position
  have family : r.endpoint.family = AF_INET ∨ r.endpoint.family = AF_INET6 := by
    rw [endpoint.1]
    rcases endpoint.2 with ipv4 | ipv6
    · exact Or.inl (by simp [sourceEndpoint,ipv4])
    · exact Or.inr (by simp [sourceEndpoint,ipv6])
  have final := RemoteCompletion.consumeDataDone_remotes (destinationAt r.run.before)
    r.peer r.packet r.endpoint family r.run.before r.run.ambientBefore
    r.run.value r.run.after r.run.ambientAfter rfl valid
  unfold ConsumptionFinalRemotes
  rw [obsEq]
  change RemoteRetained (updateRemote (destinationAt r.run.before) r.peer
    (destination (sourceEndpoint r.packet.source))) (destinationAt r.run.after)
  simpa only [endpoint.1] using final


end Leanux.Proofs.WG.Roaming
