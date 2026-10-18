import Leanux.Proofs.WG.Queues.TxItemSeparation

/-! Exact packet-value binding of the original staged batch allocator. The
shared nextSkb frontier supplies occurrence identity; allocation does not
substitute a different payload, peer, key word or nonce. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketAllocation
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition

theorem records (packets : List DataPacket) {w v : WGWorld} {d : Device}
    {a b : Ambient} {item : List SkbId} (device : w.dev = some d)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((item,v),b)) :
    ∀ (n : Nat) packet, packets[n]? = some packet → ∃ id, item[n]? = some id ∧ txPackets v id = some packet := by
  induction packets generalizing w v d a b item with
  | nil =>
    simp only [List.mapM_nil] at run
    cases run
    simp
  | cons packet packets ih =>
    simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨id,u,clock,head,tail⟩ := run
    rw [Packets.newTxSkb_run w a d packet device] at head
    cases head
    obtain ⟨ids,last,lastClock,rest,finish⟩ := tail
    cases finish
    let next := {d with txSkbs := d.txSkbs.insert d.nextSkb packet, nextSkb := d.nextSkb + 1}
    have hd : (Packets.update w (fun v => {v with txSkbs := v.txSkbs.insert d.nextSkb packet, nextSkb := d.nextSkb + 1})).dev = some next := by simp [Packets.update,device,next]
    have previous := (ItemSeparation.allocate_result packets hd rest).2.2
    obtain ⟨_,_,_,_,kept⟩ := previous
    intro n found atIndex
    cases n with
    | zero =>
      have eq : packet = found := by simpa using atIndex
      subst found
      refine ⟨d.nextSkb,rfl,?_⟩
      rw [kept d.nextSkb (Nat.lt_succ_self d.nextSkb)]
      simp [txPackets,Packets.update,device]
    | succ n =>
      obtain ⟨id,atItem,resident⟩ := ih hd rest n found (by simpa using atIndex)
      exact ⟨id,by simpa using atItem,resident⟩


end Leanux.Proofs.WG.TransmitSecurity.PacketAllocation
