import Leanux.Proofs.WG.Noise.Model
import Leanux.WG.Handshake
import Std.Tactic.Do

set_option pp.structureInstances false

/-! Small peer projections for the Noise contracts. This module deliberately
does not depend on the receive-window refinement. -/
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

def peerAt (g : WGWorld) (pid : PeerId) : Option Peer :=
  g.dev.bind fun d => d.peers[pid]?

/-- Normal completion over an actual native state and Ambient. The predicate
observes the native state; ambient inputs and outputs remain unrestricted.
Product callbacks use their separate product contracts. -/
def Ensures (a : StateT σ AmbientM α) (P : σ → Prop) (Q : α → σ → Prop) : Prop :=
  ∀ s ambient x s' ambient', P s →
    (a.run s).run ambient = .ok ((x, s'), ambient') → Q x s'

theorem ensures_bind (a : StateT σ AmbientM α) (f : α → StateT σ AmbientM β)
    (ha : Ensures a P Q) (hf : ∀ x, Ensures (f x) (Q x) R) :
    Ensures (a >>= f) P R := by
  intro s ambient y s' ambient' hp hr
  change ((a.run s).run ambient >>= fun ((x, t), b) => ((f x).run t).run b) = _ at hr
  cases he : (a.run s).run ambient with
  | error e => rw [he] at hr; cases hr
  | ok out =>
    rcases out with ⟨⟨x, t⟩, b⟩
    simp only [he] at hr
    exact hf x t b y s' ambient' (ha s ambient x t b hp he) hr

theorem ensures_iff (a : StateT σ AmbientM α) (P : σ → Prop) (Q : α → σ → Prop) :
    Ensures a P Q ↔ ⦃fun s => ⌜P s⌝⦄ a ⦃⇓? x s => ⌜Q x s⌝⦄ := by
  constructor
  · intro h s ambient hp
    cases hr : (a.run s).run ambient with
    | error e =>
      dsimp only [StateT.run] at hr
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.true, ExceptConds.const, hr]
    | ok out =>
      rcases out with ⟨⟨x, s'⟩, ambient'⟩
      dsimp only [StateT.run] at hr
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.true, ExceptConds.const, hr] using h s ambient x s' ambient' hp hr
  · intro h s ambient x s' ambient' hp hr
    have hh := h s ambient hp
    dsimp only [StateT.run] at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using hh

namespace Product

/-- Partial correctness over an arbitrary actual state/error computation.
This includes every original product action and full-state predicate. -/
def Ensures (a : StateT σ (Except Stop) α) (P : σ → Prop) (Q : α → σ → Prop) : Prop :=
  ∀ w x w', P w → a.run w = .ok (x, w') → Q x w'

theorem ensures_bind (a : StateT σ (Except Stop) α) (f : α → StateT σ (Except Stop) β)
    (ha : Ensures a P Q) (hf : ∀ x, Ensures (f x) (Q x) R) :
    Ensures (a >>= f) P R := by
  intro w y w' hp hr
  simp only [StateT.run_bind] at hr
  cases he : a.run w with
  | error e => rw [he] at hr; cases hr
  | ok out =>
    rcases out with ⟨x, v⟩
    simp only [he] at hr
    exact hf x v y w' (ha w x v hp he) hr

theorem ensures_iff (a : StateT σ (Except Stop) α) (P : σ → Prop) (Q : α → σ → Prop) :
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

end Product

@[spec high] theorem except_throw_wp {ε α : Type} (e : ε)
    (Q : PostCond α (.except ε .pure)) :
    Triple (ps := .except ε .pure) (MonadExceptOf.throw e : Except ε α)
      (spred(Q.2.1 e)) Q := by simp [Triple.iff]

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
