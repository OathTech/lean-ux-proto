import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntrySource
import Leanux.Proofs.WG.Keypairs.Evolution.Syscalls

/-! Actual counter-entry certificates carried beside the replay projection.
The native state invariant is independent of the event history; its source
contracts cannot be replaced by an unconditional history-only counter rule. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Keypairs CounterWindow Lifetimes ReplayRefusal

def Inv (w : WGWorld) : Prop := SnapshotCoherent (snapshot w)
def Safe (history : List Event) : Prop := ∀ receipt ∈ history,
  Inv receipt.run.before.wg ∧ receipt.Valid

abbrev StateSafe (body : WGPrefix Event α) :=
  StatePrefixPreserves (fun h w _ => Inv w ∧ Safe h) Safe body
abbrev ProductSafe (body : PrefixM Event α) :=
  PrefixPreserves (fun h w => Inv w.wg ∧ Safe h) Safe body

theorem safe_empty : Safe [] := by simp [Safe]

theorem Safe.append (before : Safe h) (coherent : Inv receipt.run.before.wg) (valid : receipt.Valid) :
    Safe (h ++ [receipt]) := by
  intro other member
  rcases List.mem_append.mp member with old | added
  · exact before other old
  · simpa using List.mem_singleton.mp added ▸ And.intro coherent valid

theorem state_pure (value : α) : StateSafe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)

theorem state_native (action : WG.M α) (frame : OrdinaryAction action) :
    StateSafe (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.2) (fun _ w a result v b hi run =>
    ⟨ordinary_coherent ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run) hi.1,hi.2⟩)

theorem state_same (action : WG.M α) (frame : SameSnapshot action) :
    StateSafe (liftWGPrefix action) := state_native action (SameView.ordinary frame)

theorem state_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (first : StateSafe body) (rest : ∀ value, StateSafe (next value)) :
    StateSafe (body >>= next) := StatePrefixEnsures.bind first rest

theorem product_pure (value : α) : ProductSafe (pure value) :=
  PrefixPreserves.pure (fun _ _ hi => hi.2) value

theorem product_native (action : Leanux.M α) (frame : ProductOrdinaryAction action) :
    ProductSafe (liftPrefix action) :=
  (PrefixEnsures.lift (P := fun h w => Inv w.wg ∧ Safe h) (S := Safe)
    (Q := fun _ h w => Inv w.wg ∧ Safe h) action (fun _ _ hi => hi.2) (fun _ w result v hi run =>
    ⟨ordinary_coherent ((ProjectedAction.iff_run _ _ _).mp frame w result v run) hi.1,hi.2⟩)).preserves

theorem product_same (action : Leanux.M α) (frame : SameView (fun w : World => snapshot w.wg) action) :
    ProductSafe (liftPrefix action) := product_native action (SameView.ordinary frame)

theorem product_bind {body : PrefixM Event α} {next : α → PrefixM Event β}
    (first : ProductSafe body) (rest : ∀ value, ProductSafe (next value)) :
    ProductSafe (body >>= next) := PrefixPreserves.bind first rest

theorem product_state {body : WGPrefix Event α} (preserves : StateSafe body) :
    ProductSafe (liftWGObserver body) := preserves.liftWGObserver

theorem validator (kid : KeypairId) (nonce : Nat) : Preserves Inv (counterValidate kid nonce) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases device : w.dev with
  | none =>
    simp [counterValidate,getKeypair,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.keypairs[kid]? with
    | none =>
      simp [counterValidate,getKeypair,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some key =>
      have entry := snapshot_lookup w d kid key device resident
      have coherent := hi kid (cell key) entry
      have native := counterValidate_execution w a d kid key nonce device resident coherent.1
      rw [run] at native
      have resultWorld := congrArg (fun out => out.1.2) (Except.ok.inj native)
      dsimp only at resultWorld
      change SnapshotCoherent (snapshot v)
      rw [resultWorld,cExecution_snapshot w a d kid key nonce device resident]
      exact evolution_coherent (h := []) (.validate entry nonce) hi

theorem counter (skb : SkbId) (packet : RxPacket) : ProductSafe (hooks.counterCheck skb packet) := by
  change ProductSafe (TransportDriver.counter id skb packet)
  intro w h hi
  rw [TransportDriver.counter_run]
  cases run : (liftWG (counterValidate packet.keypair packet.nonce)).run w with
  | error stop => exact ⟨[],by simp,hi.2,trivial⟩
  | ok out =>
    obtain ⟨value,v⟩ := out
    let receipt : Event := ⟨skb,packet,⟨value,w,v⟩⟩
    have certified : Safe (h ++ [receipt]) := hi.2.append hi.1 run
    have preserved : Inv v.wg := by
      rw [liftWG_run] at run
      cases native : ((counterValidate packet.keypair packet.nonce).run w.wg).run w.ambient with
      | error stop => simp [native,Except.map] at run
      | ok result =>
        obtain ⟨⟨value,u⟩,ambient⟩ := result
        simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        exact (hoare_iff_run_ambient _ _ _).mp (validator _ _) w.wg w.ambient value u ambient hi.1 native
    exact ⟨[receipt],rfl,certified,preserved,certified⟩

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
