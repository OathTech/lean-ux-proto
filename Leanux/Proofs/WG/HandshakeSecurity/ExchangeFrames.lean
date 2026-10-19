import Leanux.Proofs.WG.HandshakeSecurity.ExchangeHistory

/-! Native tag projection is kept separate from the exchange journal. The
only H1 dependencies here are exact normal-call source edges. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged

private theorem tag_injective (a b : Phase) (same : a.tag = b.tag) : a = b := by
  cases a <;> cases b <;>
    simp_all [Phase.tag,HANDSHAKE_ZEROED,HANDSHAKE_CREATED_INITIATION,
      HANDSHAKE_CONSUMED_INITIATION,HANDSHAKE_CREATED_RESPONSE,HANDSHAKE_CONSUMED_RESPONSE]

private theorem nonzero (phase : Phase) (h : phase ≠ .installed) : phase.tag ≠ HANDSHAKE_ZEROED := by
  cases phase <;>
    simp_all [Phase.tag,HANDSHAKE_ZEROED,HANDSHAKE_CREATED_INITIATION,
      HANDSHAKE_CONSUMED_INITIATION,HANDSHAKE_CREATED_RESPONSE,HANDSHAKE_CONSUMED_RESPONSE]

theorem Coherent.has_phase {l : Ledger} {w : WGWorld} (hi : Coherent l w)
    (pid : PeerId) (phase : Phase) (hn : phase ≠ .installed)
    (tag : handshakeTagAt w pid = some phase.tag) : HasPhase l pid phase := by
  obtain ⟨entry,found,equal⟩ := hi pid phase.tag tag (nonzero phase hn)
  exact ⟨entry,found,tag_injective entry.phase phase equal⟩

theorem allowed (H1 : H1ExchangeEdges) (l : Ledger) (event : Event)
    (hi : Coherent l event.before) (valid : event.Valid) : Allowed l event := by
  cases event with
  | createInitiation pid r => trivial
  | consumeInitiation msg r => trivial
  | createResponse pid r =>
    intro success
    exact hi.has_phase pid .initiationConsumed (by decide)
      ((H1.createResponse pid r.before r.after r.ambientBefore r.ambientAfter r.value valid).1 success)
  | consumeResponse msg r =>
    intro pid success
    exact hi.has_phase pid .initiationCreated (by decide)
      ((H1.consumeResponse msg r.before r.after r.ambientBefore r.ambientAfter r.value valid).1 pid success)
  | session pid r =>
    intro success
    rcases (H1.session pid r.before r.after r.ambientBefore r.ambientAfter r.value valid).1 success with created | consumed
    · exact Or.inl (hi.has_phase pid .responseCreated (by decide) created)
    · exact Or.inr (hi.has_phase pid .responseConsumed (by decide) consumed)

theorem Coherent.same {l : Ledger} {w v : WGWorld} (hi : Coherent l w)
    (tags : ∀ pid, handshakeTagAt v pid = handshakeTagAt w pid) : Coherent l v := by
  intro pid tag found nonzero
  exact hi pid tag ((tags pid) ▸ found) nonzero

private theorem changed {l next : Ledger} {w v : WGWorld} (hi : Coherent l w)
    (pid : PeerId) (phase : Phase)
    (entry : ∃ e, next pid = some e ∧ e.phase = phase)
    (others : ∀ target, target ≠ pid → next target = l target)
    (tags : ∀ target, handshakeTagAt v target =
      if target = pid then some phase.tag else handshakeTagAt w target) : Coherent next v := by
  intro target tag found hn
  by_cases same : target = pid
  · subst target
    obtain ⟨e,he,hp⟩ := entry
    have equal : phase.tag = tag := by simpa using (tags pid).symm.trans found
    exact ⟨e,he,hp ▸ equal⟩
  · have old : handshakeTagAt w target = some tag := by simpa [same] using (tags target).symm.trans found
    obtain ⟨e,he,hp⟩ := hi target tag old hn
    exact ⟨e,(others target same).trans he,hp⟩

private theorem set_coherent {l : Ledger} {w v : WGWorld} (hi : Coherent l w)
    (pid : PeerId) (epoch : Nat) (phase : Phase)
    (tags : ∀ target, handshakeTagAt v target =
      if target = pid then some phase.tag else handshakeTagAt w target) :
    Coherent (set l pid ⟨epoch,phase⟩) v :=
  changed hi pid phase ⟨⟨epoch,phase⟩,by simp [set],rfl⟩
    (fun target different => by simp [set,different]) tags

private theorem advance_coherent {l : Ledger} {w v : WGWorld} (hi : Coherent l w)
    (pid : PeerId) (old phase : Phase) (prior : HasPhase l pid old)
    (tags : ∀ target, handshakeTagAt v target =
      if target = pid then some phase.tag else handshakeTagAt w target) :
    Coherent (advance l pid phase) v := by
  obtain ⟨e,he,_⟩ := prior
  apply changed hi pid phase
    ⟨{e with phase},by simp [advance,he],rfl⟩
    (fun target different => by simp [advance,different]) tags

theorem coherent_transition (H1 : H1ExchangeEdges) (n : Nat) (l : Ledger) (event : Event)
    (hi : Coherent l event.before) (valid : event.Valid) :
    Coherent (transition n l event) event.after := by
  have enabled := allowed H1 l event hi valid
  cases event with
  | createInitiation pid r =>
    simp only [Event.before,Event.after] at hi ⊢
    have tags := H1.createInitiation pid r.before r.after r.ambientBefore r.ambientAfter r.value valid
    cases hr : r.value with
    | none =>
      simp only [transition,hr,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
      exact hi.same (by simpa [hr] using tags)
    | some msg =>
      simp only [transition,hr,Option.isSome_some,↓reduceIte]
      apply set_coherent hi pid (n+1) .initiationCreated
      simpa [hr,Phase.tag] using tags
  | consumeInitiation msg r =>
    simp only [Event.before,Event.after] at hi ⊢
    have tags := H1.consumeInitiation msg r.before r.after r.ambientBefore r.ambientAfter r.value valid
    cases hr : r.value with
    | none =>
      simp only [transition,hr]
      exact hi.same (by simpa [hr] using tags)
    | some pid =>
      simp only [transition,hr]
      apply set_coherent hi pid (n+1) .initiationConsumed
      simpa [hr,Phase.tag,eq_comm] using tags
  | createResponse pid r =>
    simp only [Event.before,Event.after] at hi ⊢
    have tags := (H1.createResponse pid r.before r.after r.ambientBefore r.ambientAfter r.value valid).2
    cases hr : r.value with
    | none =>
      simp only [transition,hr,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
      exact hi.same (by simpa [hr] using tags)
    | some msg =>
      simp only [transition,hr,Option.isSome_some,↓reduceIte]
      apply advance_coherent hi pid .initiationConsumed .responseCreated (enabled (by simp [hr]))
      simpa [hr,Phase.tag] using tags
  | consumeResponse msg r =>
    simp only [Event.before,Event.after] at hi ⊢
    have tags := (H1.consumeResponse msg r.before r.after r.ambientBefore r.ambientAfter r.value valid).2
    cases hr : r.value with
    | none =>
      simp only [transition,hr]
      exact hi.same (by simpa [hr] using tags)
    | some pid =>
      simp only [transition,hr]
      apply advance_coherent hi pid .initiationCreated .responseConsumed (enabled pid hr)
      simpa [hr,Phase.tag,eq_comm] using tags
  | session pid r =>
    simp only [Event.before,Event.after] at hi ⊢
    have tags := (H1.session pid r.before r.after r.ambientBefore r.ambientAfter r.value valid).2.1
    cases hr : r.value with
    | false =>
      simp only [transition,hr,Bool.false_eq_true,↓reduceIte]
      exact hi.same (by simpa [hr] using tags)
    | true =>
      simp only [transition,hr,↓reduceIte]
      rcases enabled hr with created | consumed
      · apply advance_coherent hi pid .responseCreated .installed created
        simpa [hr,Phase.tag] using tags
      · apply advance_coherent hi pid .responseConsumed .installed consumed
        simpa [hr,Phase.tag] using tags

theorem append (H1 : H1ExchangeEdges) (h : List Event) (event : Event)
    (hi : StateInv h event.before) (valid : event.Valid) : StateInv (h ++ [event]) event.after := by
  obtain ⟨l,history,coherent⟩ := hi
  exact ⟨transition h.length l event,history.snoc event valid (allowed H1 l event coherent valid),
    coherent_transition H1 h.length l event coherent valid⟩

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
