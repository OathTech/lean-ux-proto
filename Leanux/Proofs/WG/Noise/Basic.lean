import Leanux.WG.Handshake
import Std.Tactic.Do

set_option pp.structureInstances false

/-! Small peer projections for the Noise contracts. This module deliberately
does not depend on the receive-window refinement. -/
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

def peerAt (w : World) (pid : PeerId) : Option Peer :=
  w.k.wg.bind fun d => d.peers[pid]?

structure Slots where
  previous : Option KeypairId
  current : Option KeypairId
  next : Option KeypairId
  deriving DecidableEq, Repr

def slots (p : Peer) : Slots :=
  ⟨p.keypairPrevious, p.keypairCurrent, p.keypairNext⟩

/-- All three arms of noise.c's add_new_keypair, including an initiator
displacing a pending responder session. -/
def rotate (s : Slots) (initiator : Bool) (newKey : KeypairId) : Slots :=
  if initiator then
    ⟨if s.next.isSome then s.next else s.current, some newKey, none⟩
  else ⟨none, s.current, some newKey⟩

def confirm (s : Slots) (received : KeypairId) : Bool × Slots :=
  if s.next == some received then
    (true, ⟨s.current, some received, none⟩)
  else (false, s)

/-- Normal-completion contract; exceptions do not provide a final World. -/
def Ensures (a : M α) (P : World → Prop) (Q : α → World → Prop) : Prop :=
  ∀ w x w', P w → a.run w = .ok (x, w') → Q x w'

theorem ensures_bind (a : M α) (f : α → M β)
    (ha : Ensures a P Q) (hf : ∀ x, Ensures (f x) (Q x) R) :
    Ensures (a >>= f) P R := by
  intro w y w' hp hr
  simp only [StateT.run_bind] at hr
  cases he : a.run w with
  | error e => rw [he] at hr; cases hr
  | ok out =>
    rcases out with ⟨x, v⟩
    simp only [he, Except.bind] at hr
    exact hf x v y w' (ha w x v hp he) hr

theorem ensures_iff (a : M α) (P : World → Prop) (Q : α → World → Prop) :
    Ensures a P Q ↔ ⦃fun w => ⌜P w⌝⦄ a ⦃⇓? x w => ⌜Q x w⌝⦄ := by
  constructor
  · intro h w hp
    cases hr : a w with
    | error e => simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.true, ExceptConds.const, hr]
    | ok out =>
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.true, ExceptConds.const, hr] using h w out.1 out.2 hp hr
  · intro h w x w' hp hr
    have hh := h w hp
    change a w = .ok (x, w') at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using hh

@[spec high] theorem except_throw_wp {ε α : Type} (e : ε)
    (Q : PostCond α (.except ε .pure)) :
    Triple (ps := .except ε .pure) (MonadExceptOf.throw e : Except ε α)
      (spred(Q.2.1 e)) Q := by simp [Triple.iff]

theorem getPeer_spec (pid : PeerId) (P : World → Prop) :
    ⦃fun w => ⌜P w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P w ∧ peerAt w pid = some p⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all [peerAt]

theorem setPeer_spec (pid : PeerId) (p : Peer) (P : Peer → Prop) :
    ⦃fun w => ⌜(peerAt w pid).isSome ∧ P p⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜∃ p', peerAt w pid = some p' ∧ P p'⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals dsimp +zetaDelta only at *
  all_goals rename_i w h t
  all_goals cases hw : w.k.wg <;>
    simp_all [peerAt, Std.TreeMap.getElem?_insert]

private def normalizeName : Lean.Name → Lean.Name
  | .str p "0" => .num (normalizeName p) 0
  | .str p s => .str (normalizeName p) s
  | .num p n => .num (normalizeName p) n
  | .anonymous => .anonymous

macro "noise_const " n:ident : term =>
  pure (Lean.mkCIdent (normalizeName n.getId))

macro "noise_vcgen" "[" ns:ident,* "]" : tactic => do
  let args := ns.getElems.map fun n =>
    let ident := if n.getId.toString.startsWith "_private." then
      Lean.mkCIdent (normalizeName n.getId) else n
    (⟨Lean.Syntax.node .none ``Lean.Parser.Tactic.simpLemma
      #[Lean.Syntax.missing, Lean.Syntax.missing, ident.raw]⟩ :
      Lean.TSyntax [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
        ``Lean.Parser.Tactic.simpLemma])
  `(tactic| mvcgen [$args,*])

end Leanux.Proofs.WG.Noise
