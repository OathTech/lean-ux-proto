import Leanux.Proofs.WG.RetirementSecurity.Transfer

/-! The actual confirmation path transfers the next reference to current,
the current reference to previous, and pays only the displaced previous.
Authentication of its caller is a separate campaign-3 outcome. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

def confirmedPeer (p : Peer) (received : KeypairId) : Peer :=
  {p with keypairPrevious := p.keypairCurrent, keypairCurrent := some received, keypairNext := none}

def SlotLoans.confirm (loans : SlotLoans) : SlotLoans :=
  ⟨none,loans.current,loans.next⟩

theorem SlotLoans.confirm_aligned {loans : SlotLoans} {p : Peer} (aligned : loans.Aligned p)
    (next : p.keypairNext = some received) :
    loans.confirm.Aligned (confirmedPeer p received) :=
  ⟨rfl,aligned.2.2,aligned.1.trans next⟩

/-- On the real next-key branch, confirmation transfers two existing slot
references and pays the displaced previous occurrence exactly once. -/
theorem confirmation_account (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (remaining : Credits.Ledger) (received : KeypairId) (aligned : loans.Aligned p)
    (next : p.keypairNext = some received) :
    Hoare (receivedWithKeypair pid received)
      (PeerAccount pid p (loans.credits ++ remaining))
      (fun result w => result = true ∧
        PeerAccount pid (confirmedPeer p received) (loans.confirm.credits ++ remaining) w) := by
  have firstOrder : (loans.credits ++ remaining).Perm
      (loans.previous.toList ++ (loans.next.toList ++ (loans.current.toList ++ remaining))) := by
    simpa only [SlotLoans.credits,List.append_assoc] using
      (List.perm_append_comm (l₁ := loans.next.toList) (l₂ := loans.previous.toList)).append_right
        (loans.current.toList ++ remaining)
  apply hoare_consequence (P := PeerAccount pid p
    (loans.previous.toList ++ (loans.next.toList ++ (loans.current.toList ++ remaining)))) ?_
    (fun _ h => h.perm firstOrder) (fun _ _ h => h)
  unfold receivedWithKeypair
  apply read_bind_account pid p _
  apply branch_bind
  simp only [next,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply read_bind_account pid p _
  apply branch_bind
  simp only [next,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply read_bind_account pid p _
  apply hoare_bind _ _ (update_peer_account pid p _
    (fun q => {q with keypairPrevious := q.keypairCurrent}))
  intro _
  have pay := put_peer_account pid {p with keypairPrevious := p.keypairCurrent}
    loans.previous (loans.next.toList ++ (loans.current.toList ++ remaining)) true
  rw [aligned.2.1] at pay
  apply hoare_bind _ _ pay
  intro _
  apply hoare_bind _ _ (update_peer_account pid {p with keypairPrevious := p.keypairCurrent} _
    (fun q => {q with keypairCurrent := some received, keypairNext := none}))
  intro _
  apply hoare_consequence (hoare_pure true _)
    (fun _ h => h) (fun _ _ h => ?_)
  refine ⟨h.1,h.2.perm ?_⟩
  simpa only [SlotLoans.confirm,SlotLoans.credits,Option.toList_none,List.nil_append,
    List.append_assoc] using
    (List.perm_append_comm (l₁ := loans.next.toList) (l₂ := loans.current.toList)).append_right remaining

/-- A non-next key is refused before any reference or slot changes. -/
theorem confirmation_refused_account (pid : PeerId) (p : Peer) (credits : Credits.Ledger)
    (received : KeypairId) (different : p.keypairNext ≠ some received) :
    Hoare (receivedWithKeypair pid received) (PeerAccount pid p credits)
      (fun result w => result = false ∧ PeerAccount pid p credits w) := by
  unfold receivedWithKeypair
  apply read_bind_account pid p credits
  apply branch_bind
  have test : (p.keypairNext != some received) = true := by simp [different]
  simpa only [test,↓reduceIte] using hoare_pure false (PeerAccount pid p credits)

end Leanux.Proofs.WG.RetirementSecurity
