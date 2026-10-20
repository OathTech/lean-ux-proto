import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSendFrontSource

/-! Actual peer capture and family decisions retain the pending packet.
Only the real send receipt settles it, with the original cleanup obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSendFront
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal CompleteCarrier Staged.Obligations StagedTerminalComplete

theorem Stage.same_wg (stage : Stage) (w : World) : (stage.world w).wg=w.wg := by
  cases stage with
  | read | fourNo | unsupported | refused=>rfl
  | selected ipv4=>cases ipv4 <;> rfl

theorem ReadEntry.accounted (entry : ReadEntry context.pid w h) (stage : Stage)
    (before : Owned context (.sending (skb::rest)) h ledger debts w) (complete : Complete h ledger) :
    Accounted entry.history ledger debts (⟨.selected,context.pid,context.items⟩::context.locals)
      (stage.world entry.world).wg := by
  have same := (stage.same_wg entry.world).trans
    (FirstTerminal.peer_cut_world context.pid w entry.world entry.peer _ _ entry.read)
  have kept := (before.append (entry.events.map FirstTerminal.encode) (by
    intro event member
    obtain ⟨e,_,rfl⟩:=List.mem_map.mp member
    exact completion_encode_births e)).sameWG same
  have paired := Converse.extension complete rfl
    (mapped_quiet_suffix (read_ledger_quiet context.pid) w h entry.events (congrArg Prod.snd entry.read))
  exact ⟨kept.entry,paired⟩

/-- Security: family guards and unsupported-family refusal keep the selected
packet on its original ledger until the mandatory receipt; a completed send
settles exactly that packet and retains the corresponding cleanup debt. -/
theorem Point.evidence
    (before : Owned context (.sending (skb::rest)) h ledger debts w)
    (complete : Complete h ledger) (packetAt : PacketAt skb packet w)
    (point : Point context.pid skb packet w h u middle) : TxSocket.Evidence context ledger debts middle u := by
  cases point with
  | guarded entry stage allowed=>exact .accounted ledger debts (.refl _) (entry.accounted stage before complete)
  | returned performed=>
      obtain ⟨_,_,normal⟩:=Converse.send_checked context skb rest packet ledger debts w h ⟨before,complete,packetAt⟩
      rw [performed] at normal
      obtain ⟨chosen,member,head,outcome,terminal,owned,paired⟩:=normal
      have pending := (before.cursor.assigned chosen member).1 (by simp [head])
      let support : FirstTerminal.Support (births h) h ledger debts w.wg:=
        ⟨before.entry.core.physical,before.entry.core.valid⟩
      exact .accounted _ _ (support.settle pending outcome).1 ⟨owned.entry,paired⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSendFront
