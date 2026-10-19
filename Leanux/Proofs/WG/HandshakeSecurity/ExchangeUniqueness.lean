import Leanux.Proofs.WG.HandshakeSecurity.ExchangeReplay

/-! Security consequences of the common native exchange carrier. The History
premise remains explicit until the initialized Driver transport is discharged. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged

def ResponseAt (pre : List Event) (pid epoch : Nat) : Prop :=
  ∃ entry, replay pre pid = some entry ∧ entry.epoch = epoch ∧ entry.phase = .initiationCreated

def InstallAt (pre : List Event) (pid epoch : Nat) : Prop :=
  ∃ entry, replay pre pid = some entry ∧ entry.epoch = epoch ∧
    (entry.phase = .responseCreated ∨ entry.phase = .responseConsumed)

theorem History.response_epoch {h : List Event} {l : Ledger} (safe : History h l)
    (pre post : List Event) (msg : List UInt8) (r : WGRunWitness (Option PeerId))
    (position : h = pre ++ Event.consumeResponse msg r :: post)
    (pid : PeerId) (success : r.value = some pid) : ∃ epoch, ResponseAt pre pid epoch := by
  obtain ⟨entry,found,phase⟩ := (safe.checked pre post (.consumeResponse msg r) position).2 pid success
  exact ⟨entry.epoch,entry,found,rfl,phase⟩

theorem History.install_epoch {h : List Event} {l : Ledger} (safe : History h l)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : h = pre ++ Event.session pid r :: post) (success : r.value = true) :
    ∃ epoch, InstallAt pre pid epoch := by
  rcases (safe.checked pre post (.session pid r) position).2 success with created | consumed
  · obtain ⟨entry,found,phase⟩ := created
    exact ⟨entry.epoch,entry,found,rfl,Or.inl phase⟩
  · obtain ⟨entry,found,phase⟩ := consumed
    exact ⟨entry.epoch,entry,found,rfl,Or.inr phase⟩

theorem response_epoch_increases {h : List Event} {l : Ledger} (safe : History h l)
    (pre between post : List Event) (first second : List UInt8)
    (r s : WGRunWitness (Option PeerId)) (pid epoch₁ epoch₂ : Nat)
    (position : h = pre ++ Event.consumeResponse first r :: between ++ Event.consumeResponse second s :: post)
    (accepted₁ : r.value = some pid)
    (bound₁ : ResponseAt pre pid epoch₁)
    (bound₂ : ResponseAt (pre ++ Event.consumeResponse first r :: between) pid epoch₂) : epoch₁ < epoch₂ := by
  obtain ⟨entry₁,found₁,stamp₁,_⟩ := bound₁
  obtain ⟨entry₂,found₂,stamp₂,phase₂⟩ := bound₂
  have earlier : History (pre ++ Event.consumeResponse first r :: between)
      (replay (pre ++ Event.consumeResponse first r :: between)) :=
    safe.prefix _ (Event.consumeResponse second s :: post) (by simpa only [List.append_assoc] using position)
  have progress := earlier.prefix_mono (pre ++ [Event.consumeResponse first r]) between
    (by simp only [List.append_assoc,List.singleton_append]) pid
  simp only [replay_append,transition,accepted₁,Ledger.score,advance,↓reduceIte,found₁,found₂,
    Option.map_some,Option.elim_some,Entry.score,stamp₁,stamp₂,phase₂,Phase.rank] at progress
  omega

theorem install_epoch_increases {h : List Event} {l : Ledger} (safe : History h l)
    (pre between post : List Event) (r s : WGRunWitness Bool) (pid epoch₁ epoch₂ : Nat)
    (position : h = pre ++ Event.session pid r :: between ++ Event.session pid s :: post)
    (accepted₁ : r.value = true)
    (bound₁ : InstallAt pre pid epoch₁)
    (bound₂ : InstallAt (pre ++ Event.session pid r :: between) pid epoch₂) : epoch₁ < epoch₂ := by
  obtain ⟨entry₁,found₁,stamp₁,_⟩ := bound₁
  obtain ⟨entry₂,found₂,stamp₂,phase₂⟩ := bound₂
  have earlier : History (pre ++ Event.session pid r :: between)
      (replay (pre ++ Event.session pid r :: between)) :=
    safe.prefix _ (Event.session pid s :: post) (by simpa only [List.append_assoc] using position)
  have progress := earlier.prefix_mono (pre ++ [Event.session pid r]) between
    (by simp only [List.append_assoc,List.singleton_append]) pid
  rcases phase₂ with phase₂ | phase₂ <;>
    simp only [replay_append,transition,accepted₁,↓reduceIte,Ledger.score,advance,found₁,found₂,
      Option.map_some,Option.elim_some,Entry.score,stamp₁,stamp₂,phase₂,Phase.rank] at progress <;> omega

/-- Once the native exchange history is established, a response can be
consumed only once for its initiation epoch, even across intervening clears,
peer deletion, recreated numeric slots and other handshake calls. -/
theorem response_no_repeat {h : List Event} {l : Ledger} (safe : History h l)
    (pre between post : List Event) (first second : List UInt8)
    (r s : WGRunWitness (Option PeerId)) (pid : PeerId)
    (position : h = pre ++ Event.consumeResponse first r :: between ++ Event.consumeResponse second s :: post)
    (accepted₁ : r.value = some pid) (accepted₂ : s.value = some pid) :
    ∃ epoch₁ epoch₂, ResponseAt pre pid epoch₁ ∧
      ResponseAt (pre ++ Event.consumeResponse first r :: between) pid epoch₂ ∧ epoch₁ < epoch₂ := by
  obtain ⟨epoch₁,bound₁⟩ := safe.response_epoch pre
    (between ++ Event.consumeResponse second s :: post) first r
    (by simpa only [List.cons_append,List.append_assoc] using position) pid accepted₁
  obtain ⟨epoch₂,bound₂⟩ := safe.response_epoch (pre ++ Event.consumeResponse first r :: between) post second s
    (by simpa only [List.append_assoc] using position) pid accepted₂
  exact ⟨epoch₁,epoch₂,bound₁,bound₂,response_epoch_increases safe pre between post first second r s
    pid epoch₁ epoch₂ position accepted₁ bound₁ bound₂⟩

/-- Two successful installations for one peer require strictly different
native exchange epochs. H1 separately supplies the exact one-key allocation
count for each completed native session callback. -/
theorem install_no_repeat {h : List Event} {l : Ledger} (safe : History h l)
    (pre between post : List Event) (r s : WGRunWitness Bool) (pid : PeerId)
    (position : h = pre ++ Event.session pid r :: between ++ Event.session pid s :: post)
    (accepted₁ : r.value = true) (accepted₂ : s.value = true) :
    ∃ epoch₁ epoch₂, InstallAt pre pid epoch₁ ∧
      InstallAt (pre ++ Event.session pid r :: between) pid epoch₂ ∧ epoch₁ < epoch₂ := by
  obtain ⟨epoch₁,bound₁⟩ := safe.install_epoch pre
    (between ++ Event.session pid s :: post) pid r
    (by simpa only [List.cons_append,List.append_assoc] using position) accepted₁
  obtain ⟨epoch₂,bound₂⟩ := safe.install_epoch (pre ++ Event.session pid r :: between) post pid s
    (by simpa only [List.append_assoc] using position) accepted₂
  exact ⟨epoch₁,epoch₂,bound₁,bound₂,install_epoch_increases safe pre between post r s
    pid epoch₁ epoch₂ position accepted₁ bound₁ bound₂⟩

theorem installation_count (H1 : H1SessionEffects) {h : List Event} {l : Ledger} (safe : History h l)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : h = pre ++ Event.session pid r :: post) (success : r.value = true) :
    r.after.keypairCounter = r.before.keypairCounter + 1 := by
  have valid := (safe.checked pre post (.session pid r) position).1
  have count := (H1 pid r.before r.after r.ambientBefore r.ambientAfter r.value valid).2.2
  simpa only [success,↓reduceIte] using count

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
