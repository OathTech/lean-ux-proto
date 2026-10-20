import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointLookup

/-! Receive timer helpers retain each metadata write and hidden clock read. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal


noncomputable def deleteShape (pid : PeerId) (timer : PeerTimer) : Shape (wg (delTimer pid timer)) := by
  exact .native (.metadata _ (PeerMetadata.timerDeleteShape pid timer))

noncomputable def handshakeTimerShape (pid : PeerId) :
    Shape (wg (timersHandshakeComplete pid .walltimeLastHandshakeData)) := by
  apply Shape.marked (.handshakeTimer pid)
  unfold timersHandshakeComplete
  repeat' first
    | consume_leaf_update
    | consume_leaf_update_then
    | (consume_leaf_wg_head delTimer; exact deleteShape _ _)
    | consume_leaf_shape

noncomputable def authenticatedShape (pid : PeerId) : Shape (wg (timersAnyAuthenticatedPacketReceived pid)) := by
  apply Shape.marked (.authenticated pid)
  exact deleteShape pid .newHandshake

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
