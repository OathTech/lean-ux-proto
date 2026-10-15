import Leanux.Proofs.WG.TimerDiscipline.Jitter
import Leanux.Proofs.WG.Config.Returns

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- The two one-byte rejection-sampling sites in the timer paths. -/
inductive JitterSite where
  | retransmit
  | newHandshake

def JitterSite.hiddenSite : JitterSite → HiddenSite
  | .retransmit => .retransmitJitter
  | .newHandshake => .newHandshakeJitter

def jitterRecord (site : JitterSite) (byte : UInt8) : HiddenRecord :=
  { site := site.hiddenSite.info.id, bytes := [byte, 0, 0, 0, 0, 0, 0, 0] }

abbrev jitterAccepted (byte : UInt8) : Prop :=
  (HZ / 3 * byte.toNat) % 256 ≥ 256 % (HZ / 3)

def jitterValue (byte : UInt8) : Nat := HZ / 3 * byte.toNat / 256

theorem hiddenJitter_run (site : JitterSite) (byte : UInt8) (rest : List HiddenRecord)
    (w : World) (records : w.hidden = some (jitterRecord site byte :: rest)) :
    (hidden site.hiddenSite).run w = .ok ([byte], { w with hidden := some rest }) := by
  have retransmitPassive : HiddenSite.passive 14 = false := by decide
  have newPassive : HiddenSite.passive 16 = false := by decide
  cases site <;>
    simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      records, jitterRecord, JitterSite.hiddenSite, HiddenSite.info, retransmitPassive, newPassive,
      Worker.sectionId, Worker.index, Except.pure, Except.bind]

def jitterStep (site : HiddenSite) (_ : Nat) (_ : Option Nat × Unit) : M (ForInStep (Option Nat × Unit)) := do
  let r := (← hidden site)[0]!.toNat
  if (HZ / 3 * r) % 256 ≥ 256 % (HZ / 3) then return .done (some (HZ / 3 * r / 256), ())
  return .yield (none, ())

def jitterLoop (site : HiddenSite) (turns : List Nat) : M (Option Nat × Unit) :=
  forIn turns (none, ()) (jitterStep site)

def jitterFinish (state : Option Nat × Unit) : M Nat :=
  match state.1 with
  | some n => pure n
  | none => budgetExhausted "jitter draws"

theorem jitter_source (site : HiddenSite) :
    jitterBelowRekeyTimeout site = (do
      let budget ← recordBudget
      let state ← forIn ([:budget] : Std.Legacy.Range) (none, ()) (jitterStep site)
      jitterFinish state) := by
  simp only [jitterBelowRekeyTimeout, jitterFinish]
  congr 1
  funext budget
  congr 1
  funext state
  cases state.1 <;> rfl

theorem jitterStep_rejected (site : JitterSite) (byte : UInt8) (rest : List HiddenRecord)
    (turn : Nat) (w : World) (records : w.hidden = some (jitterRecord site byte :: rest))
    (rejected : ¬jitterAccepted byte) :
    (jitterStep site.hiddenSite turn (none, ())).run w =
      .ok (.yield (none, ()), { w with hidden := some rest }) := by
  rw [jitterStep, StateT.run_bind, hiddenJitter_run site byte rest w records]
  change ((if jitterAccepted byte then pure (.done (some (jitterValue byte), ()))
    else pure (.yield (none, ()))) : M (ForInStep (Option Nat × Unit))).run
      { w with hidden := some rest } = _
  rw [if_neg rejected]
  rfl

theorem jitterStep_accepted (site : JitterSite) (byte : UInt8) (rest : List HiddenRecord)
    (turn : Nat) (w : World) (records : w.hidden = some (jitterRecord site byte :: rest))
    (accepted : jitterAccepted byte) :
    (jitterStep site.hiddenSite turn (none, ())).run w =
      .ok (.done (some (jitterValue byte), ()), { w with hidden := some rest }) := by
  rw [jitterStep, StateT.run_bind, hiddenJitter_run site byte rest w records]
  change ((if jitterAccepted byte then pure (.done (some (jitterValue byte), ()))
    else pure (.yield (none, ()))) : M (ForInStep (Option Nat × Unit))).run
      { w with hidden := some rest } = _
  rw [if_pos accepted]
  rfl

def jitterStream (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) := rejected.map (jitterRecord site) ++ jitterRecord site accepted :: rest

theorem jitterLoop_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) (turns : List Nat) (enough : rejected.length < turns.length)
    (w : World) (records : w.hidden = some (jitterStream site rejected accepted rest)) :
    (jitterLoop site.hiddenSite turns).run w =
      .ok ((some (jitterValue accepted), ()), { w with hidden := some rest }) := by
  induction rejected generalizing turns w with
  | nil =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
      rw [jitterStep_accepted site accepted rest turn w records good]
      rfl
  | cons byte bytes ih =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
      rw [jitterStep_rejected site byte (jitterStream site bytes accepted rest) turn w records
        (bad byte (by simp))]
      exact ih (fun b member => bad b (by simp [member])) turns (by simpa using enough)
        { w with hidden := some (jitterStream site bytes accepted rest) } rfl

theorem jitter_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) (w : World)
    (records : w.hidden = some (jitterStream site rejected accepted rest)) :
    (jitterBelowRekeyTimeout site.hiddenSite).run w =
      .ok (jitterValue accepted, { w with hidden := some rest }) := by
  let stream := jitterStream site rejected accepted rest
  have budget : recordBudget.run w = .ok (stream.length + 1, w) := by
    simp [recordBudget, StateT.run, bind, pure, get, getThe, MonadStateOf.get,
      StateT.bind, StateT.pure, StateT.get, Except.bind, Except.pure, records, stream]
  have loop : (forIn ([:stream.length + 1] : Std.Legacy.Range) (none, ())
      (jitterStep site.hiddenSite)).run w =
      .ok ((some (jitterValue accepted), ()), { w with hidden := some rest }) := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    apply jitterLoop_records site rejected accepted rest bad good _ _ w records
    simp [stream, jitterStream]
    omega
  rw [jitter_source, StateT.run_bind, budget]
  change ((do
    let state ← forIn ([:stream.length + 1] : Std.Legacy.Range) (none, ()) (jitterStep site.hiddenSite)
    jitterFinish state).run w) = _
  rw [StateT.run_bind, loop]
  rfl

end Leanux.Proofs.WG.TimerDiscipline
