import Leanux.Proofs.WG.TransmitSecurity.StagedTransferFrames
import Leanux.Proofs.WG.TransmitSecurity.RoutingFinal

/-! Routing admission is the actual tail splice into the selected peer's staged
queue. Its existing prefix and newly normalized sequence remain distinct and
ordered; a later stopped send does not undo this completed source cut. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 600000
set_option pp.structureInstances false

/-- A successful front appends every supplied packet, in order and with the
single supplied MTU, to the actual queue present at its splice. -/
theorem admission (receipt : Journal.RoutingHistory.Receipt) (valid : receipt.Valid)
    (pid : PeerId) (selected : receipt.run.value = .ok pid) :
    ∃ stamp retained,
      stagedAt receipt.run.after pid =
        some (stamp,retained ++ receipt.packets.map (fun p => {p with mtu := receipt.mtu})) := by
  obtain ⟨cut,_⟩ := receipt.selection valid pid selected
  obtain ⟨u,q,r,a,b,c,_,_,_,spliceRun⟩ := cut
  let run : WGRunWitness Unit :=
    ⟨(),r,receipt.run.after,c,receipt.run.ambientAfter⟩
  have native : run.Valid (Lifetimes.xmitSplice pid
      (receipt.packets.map (fun p => {p with mtu := receipt.mtu}))) := by
    change ((Lifetimes.xmitSplice pid (receipt.packets.map (fun p => {p with mtu := receipt.mtu}))).run r).run c =
      .ok (((),receipt.run.after),receipt.run.ambientAfter)
    exact spliceRun
  with_reducible exact splice_projection pid (receipt.packets.map (fun p => {p with mtu := receipt.mtu})) run native

/-- Every routing admission in the final initialized journal has this exact
ordered splice, including a receipt before a later Stop. -/
theorem initialized_admission (trace : Runner.Trace) (placeholders : Bool)
    (receipt : Journal.RoutingHistory.Receipt)
    (member : receipt ∈ ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.old?).filterMap Journal.RoutingHistory.routed?)
    (pid : PeerId) (selected : receipt.run.value = .ok pid) :
    ∃ stamp retained,
      stagedAt receipt.run.after pid =
        some (stamp,retained ++ receipt.packets.map (fun p => {p with mtu := receipt.mtu})) :=
  admission receipt (Journal.RoutingHistory.final_initialized trace placeholders receipt member) pid selected

end Leanux.Proofs.WG.TransmitSecurity.Staged
