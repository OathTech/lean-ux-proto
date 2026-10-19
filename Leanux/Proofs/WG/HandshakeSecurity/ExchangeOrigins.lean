import Leanux.Proofs.WG.HandshakeSecurity.ExchangeUniqueness

/-! An epoch denotes an actual earlier native exchange start, not merely a
fresh abstract counter or a numeric peer identifier. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged

def Event.Started (pid : PeerId) : Event → Prop
  | .createInitiation peer r => peer = pid ∧ r.value.isSome
  | .consumeInitiation _ r => r.value = some pid
  | _ => False

def Origin (h : List Event) (pid : PeerId) (epoch : Nat) : Prop :=
  ∃ pre event post, h = pre ++ event :: post ∧ pre.length+1 = epoch ∧ event.Started pid ∧ event.Valid

private theorem set_origin (n : Nat) (l : Ledger) (pid target : PeerId) (phase : Phase)
    (entry : Entry) (found : set l pid ⟨n+1,phase⟩ target = some entry) :
    (∃ old, l target = some old ∧ old.epoch = entry.epoch) ∨
      (pid = target ∧ entry.epoch = n+1) := by
  by_cases same : target = pid
  · have equal : entry = ⟨n+1,phase⟩ := by simpa [set,same] using found.symm
    exact Or.inr ⟨same.symm,congrArg Entry.epoch equal⟩
  · exact Or.inl ⟨entry,by simpa [set,same] using found,rfl⟩

private theorem advance_origin (l : Ledger) (pid target : PeerId) (phase : Phase)
    (entry : Entry) (found : advance l pid phase target = some entry) :
    ∃ old, l target = some old ∧ old.epoch = entry.epoch := by
  by_cases same : target = pid
  · subst target
    obtain ⟨old,ho,equal⟩ := Option.map_eq_some_iff.mp (by simpa [advance] using found)
    exact ⟨old,ho,by simpa only [] using congrArg Entry.epoch equal⟩
  · exact ⟨entry,by simpa [advance,same] using found,rfl⟩

theorem transition_origin (n : Nat) (l : Ledger) (event : Event) (pid : PeerId)
    (entry : Entry) (found : transition n l event pid = some entry) :
    (∃ old, l pid = some old ∧ old.epoch = entry.epoch) ∨
      (event.Started pid ∧ entry.epoch = n+1) := by
  cases event with
  | createInitiation peer r =>
    cases hr : r.value with
    | none => exact Or.inl ⟨entry,by simpa [transition,hr] using found,rfl⟩
    | some msg =>
      rcases set_origin n l peer pid .initiationCreated entry (by simpa [transition,hr] using found) with old | fresh
      · exact Or.inl old
      · exact Or.inr ⟨⟨fresh.1,by simp [hr]⟩,fresh.2⟩
  | consumeInitiation msg r =>
    cases hr : r.value with
    | none => exact Or.inl ⟨entry,by simpa [transition,hr] using found,rfl⟩
    | some peer =>
      rcases set_origin n l peer pid .initiationConsumed entry (by simpa [transition,hr] using found) with old | fresh
      · exact Or.inl old
      · exact Or.inr ⟨by simpa [Event.Started,hr] using fresh.1,fresh.2⟩
  | createResponse peer r =>
    cases hr : r.value with
    | none => exact Or.inl ⟨entry,by simpa [transition,hr] using found,rfl⟩
    | some msg => exact Or.inl (advance_origin l peer pid .responseCreated entry (by simpa [transition,hr] using found))
  | consumeResponse msg r =>
    cases hr : r.value with
    | none => exact Or.inl ⟨entry,by simpa [transition,hr] using found,rfl⟩
    | some peer => exact Or.inl (advance_origin l peer pid .responseConsumed entry (by simpa [transition,hr] using found))
  | session peer r =>
    cases hr : r.value with
    | false => exact Or.inl ⟨entry,by simpa [transition,hr] using found,rfl⟩
    | true => exact Or.inl (advance_origin l peer pid .installed entry (by simpa [transition,hr] using found))

theorem History.origin {h : List Event} {l : Ledger} (safe : History h l)
    (pid : PeerId) (entry : Entry) (found : l pid = some entry) : Origin h pid entry.epoch := by
  induction safe generalizing entry with
  | nil => cases found
  | @snoc h l prior event valid allowed ih =>
    rcases transition_origin h.length l event pid entry found with old | fresh
    · obtain ⟨old,resident,stamp⟩ := old
      obtain ⟨pre,start,post,position,epoch,started,source⟩ := ih old resident
      exact ⟨pre,start,post ++ [event],by simp only [position,List.append_assoc,List.cons_append],
        epoch.trans stamp,started,source⟩
    · exact ⟨h,event,[],by simp,fresh.2.symm,fresh.1,valid⟩

theorem History.response_origin {h : List Event} {l : Ledger} (safe : History h l)
    (pre post : List Event) (msg : List UInt8) (r : WGRunWitness (Option PeerId))
    (position : h = pre ++ Event.consumeResponse msg r :: post)
    (pid epoch : Nat) (binding : ResponseAt pre pid epoch) : Origin pre pid epoch := by
  obtain ⟨entry,resident,stamp,_⟩ := binding
  have prior := safe.prefix pre (Event.consumeResponse msg r :: post) position
  simpa only [stamp] using prior.origin pid entry resident

theorem History.install_origin {h : List Event} {l : Ledger} (safe : History h l)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : h = pre ++ Event.session pid r :: post)
    (epoch : Nat) (binding : InstallAt pre pid epoch) : Origin pre pid epoch := by
  obtain ⟨entry,resident,stamp,_⟩ := binding
  have prior := safe.prefix pre (Event.session pid r :: post) position
  simpa only [stamp] using prior.origin pid entry resident

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
