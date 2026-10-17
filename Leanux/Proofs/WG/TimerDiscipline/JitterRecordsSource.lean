import Leanux.Proofs.WG.TimerDiscipline.Model
import Leanux.Proofs.WG.TimerDiscipline.JitterFrames
import Leanux.Proofs.WG.Config.Returns

set_option autoImplicit false

/-! Recorded jitter's exact native effects. Both input states remain arbitrary:
WireGuard is unchanged, and only Ambient.hidden loses the specified prefix.
Product terminal observations retain their separate fixture obligations. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- The two one-byte rejection-sampling sites in the timer paths. -/
theorem hiddenJitter_run (site : JitterSite) (byte : UInt8) (rest : List HiddenRecord)
    (g : WGWorld) (w : Ambient) (records : w.hidden = some (jitterRecord site byte :: rest)) :
    ((hidden site.hiddenSite : WG.M (List UInt8)).run g).run w =
      .ok (([byte], g), {w with hidden := some rest}) := by
  have h : (AmbientM.hidden site.hiddenSite).run w =
      .ok ([byte], {w with hidden := some rest}) := by
    have retransmitPassive : HiddenSite.passive 14 = false := by decide
    have newPassive : HiddenSite.passive 16 = false := by decide
    cases site <;>
      simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
        get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
        records, jitterRecord, JitterSite.hiddenSite, HiddenSite.info, retransmitPassive, newPassive,
        Worker.sectionId, Worker.index, Except.pure, Except.bind]
  change ((AmbientM.hidden site.hiddenSite).run w >>= fun (value, next) =>
    Except.ok ((value, g), next)) = _
  rw [h]
  rfl

def jitterStep (site : HiddenSite) (_ : Nat) (_ : Option Nat × Unit) :
    WG.M (ForInStep (Option Nat × Unit)) := do
  let r := (← hidden site)[0]!.toNat
  if (HZ / 3 * r) % 256 ≥ 256 % (HZ / 3) then return .done (some (HZ / 3 * r / 256), ())
  return .yield (none, ())

def jitterLoop (site : HiddenSite) (turns : List Nat) : WG.M (Option Nat × Unit) :=
  forIn turns (none, ()) (jitterStep site)

def jitterFinish (state : Option Nat × Unit) : WG.M Nat :=
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
    (turn : Nat) (g : WGWorld) (w : Ambient)
    (records : w.hidden = some (jitterRecord site byte :: rest))
    (rejected : ¬jitterAccepted byte) :
    ((jitterStep site.hiddenSite turn (none, ())).run g).run w =
      .ok ((.yield (none, ()), g), {w with hidden := some rest}) := by
  simp only [jitterStep, StateT.run_bind]
  rw [hiddenJitter_run site byte rest g w records]
  change (((if jitterAccepted byte then pure (.done (some (jitterValue byte), ()))
    else pure (.yield (none, ()))) : WG.M (ForInStep (Option Nat × Unit))).run g).run
      {w with hidden := some rest} = _
  rw [ite_eq_right rejected]
  rfl

theorem jitterStep_accepted (site : JitterSite) (byte : UInt8) (rest : List HiddenRecord)
    (turn : Nat) (g : WGWorld) (w : Ambient)
    (records : w.hidden = some (jitterRecord site byte :: rest))
    (accepted : jitterAccepted byte) :
    ((jitterStep site.hiddenSite turn (none, ())).run g).run w =
      .ok ((.done (some (jitterValue byte), ()), g), {w with hidden := some rest}) := by
  simp only [jitterStep, StateT.run_bind]
  rw [hiddenJitter_run site byte rest g w records]
  change (((if jitterAccepted byte then pure (.done (some (jitterValue byte), ()))
    else pure (.yield (none, ()))) : WG.M (ForInStep (Option Nat × Unit))).run g).run
      {w with hidden := some rest} = _
  rw [ite_eq_left accepted]
  rfl

theorem jitterLoop_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) (turns : List Nat) (enough : rejected.length < turns.length)
    (g : WGWorld) (w : Ambient)
    (records : w.hidden = some (jitterStream site rejected accepted rest)) :
    ((jitterLoop site.hiddenSite turns).run g).run w =
      .ok (((some (jitterValue accepted), ()), g), {w with hidden := some rest}) := by
  induction rejected generalizing turns w with
  | nil =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
      rw [jitterStep_accepted site accepted rest turn g w records good]
      rfl
  | cons byte bytes ih =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
      rw [jitterStep_rejected site byte (jitterStream site bytes accepted rest) turn g w records
        (bad byte (by simp))]
      exact ih (fun b member => bad b (by simp [member])) turns (by simpa using enough)
        {w with hidden := some (jitterStream site bytes accepted rest)} rfl

theorem jitter_records (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (good : jitterAccepted accepted) (g : WGWorld) (w : Ambient)
    (records : w.hidden = some (jitterStream site rejected accepted rest)) :
    ((jitterBelowRekeyTimeout site.hiddenSite).run g).run w =
      .ok ((jitterValue accepted, g), {w with hidden := some rest}) := by
  let stream := jitterStream site rejected accepted rest
  have budget : ((recordBudget : WG.M Nat).run g).run w = .ok ((stream.length + 1, g), w) := by
    change Except.ok (((match w.hidden with
      | some rs => rs.length + 1
      | none => DOMAIN_FILTER_TURNS), g), w) = _
    rw [records]
  have loop : ((forIn ([:stream.length + 1] : Std.Legacy.Range) (none, ())
      (jitterStep site.hiddenSite)).run g).run w =
      .ok (((some (jitterValue accepted), ()), g), {w with hidden := some rest}) := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    apply jitterLoop_records site rejected accepted rest bad good _ _ g w records
    simp [stream, jitterStream]
    omega
  simp only [jitter_source, StateT.run_bind]
  rw [budget]
  change (((do
    let state ← forIn ([:stream.length + 1] : Std.Legacy.Range) (none, ()) (jitterStep site.hiddenSite)
    jitterFinish state).run g).run w) = _
  simp only [StateT.run_bind]
  rw [loop]
  rfl

end Leanux.Proofs.WG.TimerDiscipline
