import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalDebt

/-! The original post-socket accounting continuation changes peer byte
counters only. It cannot lose pending cells or cleanup debt, and its observed
prefix retains the preceding first terminal even if accounting Stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

def accountingNative (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) : Leanux.M Bool := do
  let sent := ret == 0
  if ← liftWG (branch .sendSkbOk sent) then
    liftWG (do
      let peer ← getPeer pid
      setPeer pid {peer with txBytes := peer.txBytes + packet.value.bytes.length})
  return sent

theorem accounting_erases (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) :
    ErasesPrefix (CompletionFirstTerminal.afterSocket pid packet ret) (accountingNative pid packet ret) := by
  unfold CompletionFirstTerminal.afterSocket accountingNative
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro sent
  cases sent
  · exact erasesPrefix_pure _
  · exact erasesPrefix_bind (Completion.access_erases (modifyPeerKeysPrefix_erases pid _))
      (fun _ => erasesPrefix_pure _)

private theorem peer_snapshot (pid : PeerId) : SameView PacketOrigins.snapshot (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg PacketOrigins.snapshot (Peers.getPeer_current pid w v p a b run).1

private theorem peer_account_snapshot (pid : PeerId) (size : Nat) :
    SameView PacketOrigins.snapshot (do
      let peer ← getPeer pid
      setPeer pid {peer with txBytes := peer.txBytes + size}) := by
  intro initial
  apply preserves_bind (peer_snapshot pid initial)
  intro peer
  exact PacketOrigins.modify
    (fun d => {d with peers := d.peers.insert pid {peer with txBytes := peer.txBytes + size}})
    (fun _ => rfl) (fun _ => rfl) initial

private theorem branch_snapshot (decision : Decision) (value : Bool) :
    SameView PacketOrigins.snapshot (branch decision value : WG.M Bool) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  rfl

theorem accounting_snapshot (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) :
    SameView (fun w : World => PacketOrigins.snapshot w.wg) (accountingNative pid packet ret) := by
  have lift_frame {α} (action : WG.M α) (frame : SameView PacketOrigins.snapshot action) :=
    sameView_liftWG (fun w : World => PacketOrigins.snapshot w.wg)
      PacketOrigins.snapshot action frame (fun _ _ _ same => same)
  intro initial
  unfold accountingNative
  apply preserves_bind (lift_frame _ (branch_snapshot .sendSkbOk (ret == 0)) initial)
  intro sent
  cases sent
  · exact preserves_pure _
  · apply preserves_bind (lift_frame _ (peer_account_snapshot pid packet.value.bytes.length) initial)
    intro _
    exact preserves_pure _

/-- The actual accounting suffix keeps the same pending/debt ledger and all
physical coverage. Its history suffix is from this focused source execution,
so the earlier inner result is never reclassified as an outer refusal. -/
theorem accounting_support (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int)
    (w v : World) (history suffix : List CausalJournal.Event) (sent : Bool)
    (performed : runPrefix (focused (CompletionFirstTerminal.afterSocket pid packet ret)) w history =
      (.ok (sent,v),history ++ suffix))
    (support : Support births history ledger debts w.wg) :
    Support births (history ++ suffix) ledger debts v.wg := by
  have erases := focusPrefix_erases encode CausalJournal.completion? (accounting_erases pid packet ret)
  have native := (erases w history).symm.trans (congrArg Prod.fst performed)
  have same := (ProjectedAction.iff_run _ _ _).mp (accounting_snapshot pid packet ret) w sent v native
  obtain ⟨epoch,cells⟩ := Prod.mk.inj same
  exact (support.views epoch cells).append suffix

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
