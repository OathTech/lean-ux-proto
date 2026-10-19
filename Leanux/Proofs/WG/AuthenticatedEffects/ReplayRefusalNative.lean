import Leanux.Proofs.WG.AuthenticatedEffects.ReplayRefusalModel
import Leanux.Proofs.WG.Keypairs.LifetimeMirror

/-! Native replay refusal retains every WG field and every resident keypair
record, up to the irrelevant tree-map representation. The coherent-counter
entry premise stays explicit until initialized transport supplies it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayRefusal
open Leanux Leanux.WG CounterWindow Keypairs

def outsideKeys (w : WGWorld) : WGWorld :=
  {w with dev := w.dev.map fun d => {d with keypairs := ∅}}

def residentKeys (w : WGWorld) : KeypairId → Option Keypair :=
  fun id => w.dev.bind fun d => d.keypairs[id]?

def view (w : WGWorld) := (outsideKeys w,residentKeys w)

private theorem stored_existing (w : WGWorld) (d : Device) (id : KeypairId) (key : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some key) :
    view (store w id key) = view w := by
  unfold view
  apply Prod.ext
  · simp only [outsideKeys,store,device,Option.map_some]
  · funext other
    by_cases same : other = id
    · subst other
      simp [residentKeys,store,device,resident]
    · simp [residentKeys,store,device,Std.TreeMap.getElem?_insert,Ne.symm same]

private theorem execution_world (w : WGWorld) (a : Ambient) (id : KeypairId)
    (key : Keypair) (nonce : Nat) :
    (cExecution id nonce key w a).1.2 =
      if eligible key.receivingCounter nonce then
        store w id {key with receivingCounter := update key.receivingCounter nonce} else w := by
  by_cases allowed : eligible key.receivingCounter nonce
  · have h1 : ¬key.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1 := by have := allowed.1; omega
    have h2 : ¬nonce ≥ REJECT_AFTER_MESSAGES := by have := allowed.2.1; omega
    have h3 : ¬8128 + (nonce + 1) < key.receivingCounter.counter := by have := allowed.2.2; omega
    by_cases later : nonce + 1 > key.receivingCounter.counter
    · simp [cExecution,allowed,h1,h2,h3,later,update,prepared,Nat.max_eq_right (by omega : key.receivingCounter.counter ≤ nonce + 1)]
    · simp [cExecution,allowed,h1,h2,h3,later,update,prepared,Nat.max_eq_left (by omega : nonce + 1 ≤ key.receivingCounter.counter)]
  · rw [ite_eq_right allowed]
    by_cases h1 : key.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
    · simp [cExecution,h1]
    · by_cases h2 : nonce ≥ REJECT_AFTER_MESSAGES
      · simp [cExecution,h1,h2]
      · have h3 : 8128 + (nonce + 1) < key.receivingCounter.counter := by unfold eligible at allowed; omega
        simp [cExecution,h1,h2,h3]

theorem native_refusal (w v : WGWorld) (a b : Ambient) (id : KeypairId) (nonce : Nat)
    (d : Device) (key : Keypair) (device : w.dev = some d)
    (resident : d.keypairs[id]? = some key) (coherent : Coherent key.receivingCounter)
    (run : ((counterValidate id nonce).run w).run a = .ok ((false,v),b)) :
    view v = view w := by
  have exactRun := counterValidate_execution w a d id key nonce device resident coherent.1
  rw [run] at exactRun
  have world := congrArg (fun out => out.1.2) (Except.ok.inj exactRun)
  have value := congrArg (fun out => out.1.1) (Except.ok.inj exactRun)
  dsimp only at world value
  have refinement := (cExecution_refines_step w a d id key nonce device resident).1
  have refused : (step key.receivingCounter nonce).1 = false := refinement.symm.trans value.symm
  have unchanged := rejected_unchanged key.receivingCounter nonce coherent refused
  rw [world,execution_world]
  split
  · rename_i eligible
    simp only [step,ite_eq_left eligible] at unchanged
    rw [unchanged]
    exact stored_existing w d id key device resident
  · rfl

def SnapshotCoherent (s : Snapshot) : Prop :=
  ∀ id key, s.slots id = some key → Coherent key.counter

theorem snapshot_empty (frontier : Nat) : SnapshotCoherent ⟨frontier,fun _ => none⟩ := by
  intro id key absent
  cases absent

theorem ordinary_coherent (transition : Ordinary s t) (hi : SnapshotCoherent s) :
    SnapshotCoherent t := by
  induction transition with
  | refl => exact hi
  | erase s id =>
    intro other key resident
    by_cases same : other = id
    · subst other; simp at resident
    · exact hi other key (by simpa [same] using resident)
  | empty => intro id key absent; cases absent
  | fresh s id =>
    intro other key resident
    by_cases same : other = id
    · simp only [Snapshot.fresh,same,ite_true,Option.some.injEq] at resident
      subst key
      exact coherent_empty
    · exact hi other key (by simpa [Snapshot.fresh,same] using resident)
  | trans _ _ first second => exact second (first hi)

theorem evolution_coherent (transition : Evolution s h t history) (hi : SnapshotCoherent s) :
    SnapshotCoherent t := by
  induction transition with
  | refl => exact hi
  | ordinary transition => exact ordinary_coherent transition hi
  | validate resident nonce =>
    rename_i current initial prior id
    intro other key found
    by_cases same : other = id
    · subst other
      simp only [Keypairs.validate,put_here,Option.some.injEq] at found
      subst key
      exact coherent_step _ nonce (hi _ _ resident)
    · exact hi other key (by simpa [Keypairs.validate,same] using found)
  | trans _ _ first second => exact second (first hi)

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayRefusal
