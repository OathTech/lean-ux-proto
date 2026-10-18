import PairInsertSource

namespace Binary.Pair.Insert.Source
open Leanux Leanux.WG

abbrev DrawAcc := Option Nat × Unit

def attempt (owner : IndexOwner) (_a : DrawAcc) : M (ForInStep DrawAcc) := do
  let index ← hiddenU64 .indexDraw
  if ← hasBucket .idxInsWalk1 .idxInsCollide1 index then return .yield (none,())
  if ← hasBucket .idxInsWalk2 .idxInsCollide2 index then
    unsupported "an index stolen during insertion"
  modifyDev fun d => {d with indexTable := ⟨index,owner⟩::d.indexTable}
  return .done (some index,())

def attempts (owner : IndexOwner) : Nat → DrawAcc → M DrawAcc
  | 0,a => pure a
  | fuel+1,a => do
    match ← attempt owner a with
    | .done out => pure out
    | .yield out => attempts owner fuel out

def finish (a : DrawAcc) : M Nat :=
  match a.1 with
  | some value => pure value
  | none => budgetExhausted "index draws"

theorem range_attempts (owner : IndexOwner) (fuel start : Nat) (a : DrawAcc) :
    forIn (List.range' start fuel) a (fun _ a => attempt owner a)=attempts owner fuel a := by
  induction fuel generalizing start a with
  | zero => rfl
  | succ fuel ih =>
    simp only [List.range'_succ,List.forIn_cons,attempts]
    congr 1
    funext step
    cases step <;> simp only [ih]

/-- Normalize the compiler's early-return loop, preserving the actual
mirror body and refusal paths. The fuel is its recorded-input budget. -/
theorem presentation_loop (owner : IndexOwner) :
    presentation owner=(do
      unhash owner
      let fuel ← recordBudget
      let out ← attempts owner fuel (none,())
      finish out) := by
  unfold presentation
  congr 1
  funext ⟨⟩
  congr 1
  funext fuel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    show ([:fuel] : Std.Legacy.Range).size=fuel from by simp [Std.Legacy.Range.size]]
  rw [←range_attempts owner fuel 0]
  unfold attempt hiddenU64 finish
  simp only [bind_assoc]
  congr 1
  funext a
  rcases a with ⟨result,⟨⟩⟩
  cases result <;> rfl

#print axioms presentation_loop

/-- A finite source retry path, retaining the actual draw and walk states.
These are extracted from an accepted execution, not assumed at binary entry. -/
inductive RetryPath (owner : IndexOwner) : World → Nat → World → Prop
  | found {w index drawn first second final} :
      (hiddenU64 .indexDraw).run w=.ok (index,drawn) →
      (hasBucket .idxInsWalk1 .idxInsCollide1 index).run drawn=.ok (false,first) →
      (hasBucket .idxInsWalk2 .idxInsCollide2 index).run first=.ok (false,second) →
      (modifyDev fun d => {d with indexTable := ⟨index,owner⟩::d.indexTable}).run second=.ok ((),final) →
      RetryPath owner w index final
  | collision {w draw drawn middle index final} :
      (hiddenU64 .indexDraw).run w=.ok (draw,drawn) →
      (hasBucket .idxInsWalk1 .idxInsCollide1 draw).run drawn=.ok (true,middle) →
      RetryPath owner middle index final → RetryPath owner w index final

theorem attempt_effect {owner w a step final}
    (accepted : (attempt owner a).run w=.ok (step,final)) :
    (∃ index drawn first second,
      step=.done (some index,()) ∧
      (hiddenU64 .indexDraw).run w=.ok (index,drawn) ∧
      (hasBucket .idxInsWalk1 .idxInsCollide1 index).run drawn=.ok (false,first) ∧
      (hasBucket .idxInsWalk2 .idxInsCollide2 index).run first=.ok (false,second) ∧
      (modifyDev fun d => {d with indexTable := ⟨index,owner⟩::d.indexTable}).run second=.ok ((),final)) ∨
    (∃ index drawn, step=.yield (none,()) ∧
      (hiddenU64 .indexDraw).run w=.ok (index,drawn) ∧
      (hasBucket .idxInsWalk1 .idxInsCollide1 index).run drawn=.ok (true,final)) := by
  unfold attempt at accepted
  rw [StateT.run_bind] at accepted
  obtain ⟨⟨index,drawn⟩,input,accepted⟩ := bind_ok accepted
  change ((hasBucket .idxInsWalk1 .idxInsCollide1 index).run drawn >>= _) = _ at accepted
  obtain ⟨⟨hit,first⟩,walk,accepted⟩ := bind_ok accepted
  cases hit with
  | true =>
    change Except.ok (.yield (none,()),first)=Except.ok (step,final) at accepted
    cases Except.ok.inj accepted
    exact .inr ⟨index,drawn,rfl,input,walk⟩
  | false =>
    change ((hasBucket .idxInsWalk2 .idxInsCollide2 index).run first >>= _) = _ at accepted
    obtain ⟨⟨stolen,second⟩,locked,accepted⟩ := bind_ok accepted
    cases stolen with
    | true => cases accepted
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte] at accepted
      change ((modifyDev fun d => {d with indexTable := ⟨index,owner⟩::d.indexTable}).run second >>=
        fun p => .ok (.done (some index,()),p.2)) = .ok (step,final) at accepted
      obtain ⟨⟨⟨⟩,last⟩,updated,accepted⟩ := bind_ok accepted
      change Except.ok (.done (some index,()),last)=Except.ok (step,final) at accepted
      cases Except.ok.inj accepted
      exact .inl ⟨index,drawn,first,second,rfl,input,walk,locked,updated⟩

theorem attempts_path {owner fuel w out final}
    (accepted : (attempts owner fuel (none,())).run w=.ok (out,final)) :
    out=(none,()) ∨
      ∃ index, out=(some index,()) ∧ RetryPath owner w index final := by
  induction fuel generalizing w out final with
  | zero =>
    change Except.ok ((none,()),w)=Except.ok (out,final) at accepted
    cases Except.ok.inj accepted
    exact .inl rfl
  | succ fuel ih =>
    rw [attempts,StateT.run_bind] at accepted
    obtain ⟨⟨step,middle⟩,one,accepted⟩ := bind_ok accepted
    rcases attempt_effect one with ⟨index,drawn,first,second,equal,input,walk,locked,updated⟩ |
      ⟨draw,drawn,equal,input,walk⟩
    · subst step
      change Except.ok ((some index,()),middle)=Except.ok (out,final) at accepted
      cases Except.ok.inj accepted
      exact .inr ⟨index,rfl,.found input walk locked updated⟩
    · subst step
      rcases ih accepted with empty | ⟨index,equal,path⟩
      · exact .inl empty
      · exact .inr ⟨index,equal,.collision input walk path⟩

theorem finish_accepted {out w index final}
    (accepted : (finish out).run w=.ok (index,final)) :
    out=(some index,()) ∧ final=w := by
  rcases out with ⟨answer,⟨⟩⟩
  cases answer with
  | none =>
    simp only [finish,budgetExhausted,StateT.run_bind] at accepted
    cases present : w.hidden.isSome <;>
      simp [present,invariant,unsupported] at accepted <;> cases accepted
  | some value =>
    change Except.ok (value,w)=Except.ok (index,final) at accepted
    cases Except.ok.inj accepted
    exact ⟨rfl,rfl⟩

/-- Every accepted actual insertion is an unhash followed by a finite
collision prefix and a successful insertion attempt. There is no fixed
bound or assumed second-walk result in this statement. -/
theorem source_path {owner w d index final}
    (device : w.k.wg=some d)
    (accepted : (WG.indexInsert owner).run w=.ok (index,final)) :
    RetryPath owner (unlinkedWorld w d owner) index final := by
  rw [indexInsert_eq,presentation_loop,StateT.run_bind,unhash_run w d owner device] at accepted
  let initial := unlinkedWorld w d owner
  let fuel := match initial.hidden with | some rs => rs.length+1 | none => DOMAIN_FILTER_TURNS
  change ((attempts owner fuel (none,())).run initial >>= fun p => (finish p.1).run p.2)=_ at accepted
  obtain ⟨⟨out,middle⟩,loop,finished⟩ := bind_ok accepted
  obtain ⟨answer,equal⟩ := finish_accepted finished
  subst final
  rcases attempts_path loop with exhausted | ⟨value,someValue,path⟩
  · simp [exhausted] at answer
  · rw [someValue] at answer
    have same : value=index := by simpa using answer
    subst value
    exact path

#print axioms source_path

end Binary.Pair.Insert.Source
