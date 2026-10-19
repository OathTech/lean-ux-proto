import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionWake
import Init.Internal.Order.While

/-! A native loop frame requires an actual decreasing source-state measure;
no termination or suspension behavior is inferred from the loop syntax alone. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues Std.Do

theorem native {action : FS.M α} (frame : Keeps action)
    (run : ((action.run s).run t).run a=.ok (((result,s'),t'),a')) :
    a'.suspended=a.suspended := TxSuspension.native (frame s) run

theorem fs_bind_ok (action : FS.M α) (next : α→FS.M β)
    (s v : FSWorld) (t u : TaskWorld) (a c : Ambient) (result : β) :
    (((action >>= next).run s).run t).run a=.ok (((result,v),u),c) ↔
      ∃value fs task ambient,((action.run s).run t).run a=.ok (((value,fs),task),ambient) ∧
        (((next value).run fs).run task).run ambient=.ok (((result,v),u),c) := by
  simp only [StateT.run_bind]
  cases step:((action.run s).run t).run a with
  | error reason=>simp
  | ok out=>
    obtain ⟨⟨⟨value,fs⟩,task⟩,ambient⟩:=out
    simp only [Except.ok.injEq,Prod.mk.injEq]
    constructor
    · intro run; exact ⟨value,fs,task,ambient,⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,run⟩
    · rintro ⟨value,fs,task,ambient,⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,run⟩; exact run

theorem fs_hoare_iff (action : FS.M α) (P : FSWorld→Prop) (Q : α→FSWorld→Prop) :
    Hoare action P Q ↔ ∀s t a result v u c,P s →
      ((action.run s).run t).run a=.ok (((result,v),u),c) → Q result v := by
  constructor
  · intro h s t a result v u c hp run
    have hh:=h s t a hp
    dsimp only [StateT.run] at run
    simpa [WP.wp,PredTrans.pushArg,PredTrans.pushExcept,PredTrans.apply,
      StateT.run,Except.instWP._aux_1,ExceptT.run,Id.run,PredTrans.pure,
      Pure.pure,ExceptConds.true,ExceptConds.const,run] using hh
  · intro h s t a hp
    cases run:((action.run s).run t).run a with
    | error reason=>
      dsimp only [StateT.run] at run
      simp [WP.wp,PredTrans.pushArg,PredTrans.pushExcept,PredTrans.apply,
        StateT.run,Except.instWP._aux_1,ExceptT.run,Id.run,PredTrans.pure,
        Pure.pure,ExceptConds.true,ExceptConds.const,run]
    | ok out=>
      obtain ⟨⟨⟨result,v⟩,u⟩,c⟩:=out
      dsimp only [StateT.run] at run
      simpa [WP.wp,PredTrans.pushArg,PredTrans.pushExcept,PredTrans.apply,
        StateT.run,Except.instWP._aux_1,ExceptT.run,Id.run,PredTrans.pure,
        Pure.pure,ExceptConds.true,ExceptConds.const,run] using h s t a result v u c hp run

theorem loop (body : Unit→β→FS.M (ForInStep β)) (measure : β→FSWorld→Nat)
    (frame : ∀b,Keeps (body () b))
    (decreases : ∀b s t a b' s' t' a',
      (((body () b).run s).run t).run a=.ok (((.yield b',s'),t'),a') →
      measure b' s'<measure b s) (initial : β) :
    Keeps (forIn ({} : Lean.Loop) initial body) := by
  have transport : ∀n b s,measure b s=n → ∀t a result s' t' a',
      (((forIn ({} : Lean.Loop) b body).run s).run t).run a=
        .ok (((result,s'),t'),a') → a'.suspended=a.suspended := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih=>
      intro b s size t a result s' t' a' run
      change (((Lean.Loop.forIn ({} : Lean.Loop) b body).run s).run t).run a=_ at run
      rw [Lean.Loop.forIn_eq_of_monadTail] at run
      change ((((body () b).run s).run t).run a >>= fun ⟨⟨⟨step,fs⟩,task⟩,ambient⟩=>
        (((match step with
        | .done value=>(Pure.pure value : FS.M β)
        | .yield next=>Lean.Loop.forIn ({} : Lean.Loop) next body).run fs).run task).run ambient)=
          .ok (((result,s'),t'),a') at run
      cases first:(((body () b).run s).run t).run a with
      | error reason=>simp only [first] at run; cases run
      | ok out=>
        obtain ⟨⟨⟨step,u⟩,q⟩,c⟩:=out
        have kept:=native (frame b) first
        cases step with
        | done value=>
          simp only [first] at run
          cases run
          exact kept
        | yield next=>
          simp only [first] at run
          have less : measure next u<n := by rw [←size]; exact decreases _ _ _ _ _ _ _ _ first
          exact (ih (measure next u) less next u rfl q c result s' t' a' run).trans kept
  intro s t
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro a result a' run
  obtain ⟨⟨value,s'⟩,t'⟩:=result
  exact transport _ initial s rfl t a value s' t' a' run

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
