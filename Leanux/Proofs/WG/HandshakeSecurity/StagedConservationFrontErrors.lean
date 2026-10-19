import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationErrorPreludeFrames
import Leanux.Proofs.WG.Keypairs.MaterialOrigin

/-! Exact error charges belong to the original invocation, not each GSO segment. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Packets Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem error_charge (family : Nat) (first : Packet) (ret : Int)
    (r : WGRunWitness Int) (run : r.Valid (txError family first ret)) :
    r.value = ret ∧ errors r.after = (errors r.before).map (· + 1) := by
  unfold WGRunWitness.Valid at run
  rw [error_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,middle,clock,notify,tail⟩ := run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (notification_frame family first)
    r.before r.ambientBefore () middle clock notify
  change Except.ok ((ret,{middle with dev := middle.dev.map (fun d => {d with txErrors := d.txErrors + 1})}),clock) =
    Except.ok ((r.value,r.after),r.ambientAfter) at tail
  have value := congrArg (fun p => p.1.1) (Except.ok.inj tail)
  have after := congrArg (fun p => p.1.2) (Except.ok.inj tail)
  dsimp only at value after
  refine ⟨value.symm,?_⟩
  rw [← after]
  simpa only [errors,Option.map_map,Function.comp_def] using
    congrArg (fun o : Option Nat => o.map (· + 1)) frame



def ErrorResult (initial : Option Nat) (result : Except Int α) (w : WGWorld) : Prop :=
  match result with
  | .error code => (code = -ENOKEY ∨ code = -EDESTADDRREQ ∨ code = -ENOMEM) ∧
      errors w = initial.map (· + 1)
  | .ok _ => errors w = initial

private theorem bind_ite {m : Type → Type} [Monad m] (c : Prop) [Decidable c]
    (a b : m α) (f : α → m β) :
    ((if c then a else b) >>= f) = (if c then a >>= f else b >>= f) := by
  by_cases h : c <;> simp only [h,ite_true,ite_false]

theorem select_charge (family : Nat) (pkts : List Packet) (mtu : Nat)
    (peer : Option PeerId) (initial : Option Nat) :
    Hoare (txSelect family pkts mtu peer) (fun w => errors w = initial) (ErrorResult initial) := by
  let P := fun w => errors w = initial
  let post : Except Int (PeerId × List Packet) → WGWorld → Prop := ErrorResult initial
  have step {α : Type} (a : WG.M α) (f : α → WG.M (Except Int (PeerId × List Packet)))
      (frame : SameView errors a) (hf : ∀ x, Hoare (f x) P post) :
      Hoare (a >>= f) P post := hoare_bind _ _ (frame.wp (· = initial)) hf
  have decision (d : Decision) (b : Bool)
      (f : Bool → WG.M (Except Int (PeerId × List Packet))) (hf : Hoare (f b) P post) :
      Hoare (branch d b >>= f) P post := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v clock before run
    have hb (g : WGWorld) (ambient : Ambient) :
        ((branch d b : WG.M Bool).run g).run ambient =
          .ok ((b,g),CounterWindow.record ambient d b) := rfl
    simp only [StateT.run_bind,hb,CounterWindow.except_ok_bind] at run
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ before run
  have failed (code : Int) (named : code = -ENOKEY ∨ code = -EDESTADDRREQ ∨ code = -ENOMEM) :
      Hoare (do
        let result ← txError family (pkts.head?.getD {bytes := []}) code
        pure (Except.error result : Except Int (PeerId × List Packet))) P post := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨ret,u,clock,error,done⟩ := run
    have charge := error_charge family (pkts.head?.getD {bytes := []}) code ⟨ret,w,u,a,clock⟩ error
    have output : ((Except.error ret,u),clock) = ((result,v),b) := Except.ok.inj done
    have resultEq := congrArg (fun x => x.1.1) output
    have worldEq := congrArg (fun x => x.1.2) output
    dsimp only at resultEq worldEq charge
    rw [← resultEq,← worldEq]
    exact ⟨charge.1 ▸ named,charge.2.trans (congrArg (Option.map (· + 1)) before)⟩
  have done (value : PeerId × List Packet) : Hoare (pure (.ok value) : WG.M _) P post :=
    hoare_consequence (hoare_pure (Except.ok value : Except Int (PeerId × List Packet)) P) (fun _ h => h)
      (fun x w h => h.1 ▸ h.2)
  have conditional (p : Prop) [Decidable p] (yes no : WG.M (Except Int (PeerId × List Packet)))
      (hy : p → Hoare yes P post) (hn : ¬p → Hoare no P post) :
      Hoare (if p then yes else no) P post := by
    by_cases h : p
    · simpa only [ite_eq_left h] using hy h
    · simpa only [ite_eq_right h] using hn h
  change Hoare (txSelect family pkts mtu peer) P post
  cases peer <;> unfold txSelect WG.andM
  all_goals simp only [Option.isNone_none,Option.isNone_some,bind_assoc,bind_ite,pure_bind]
  all_goals repeat' first
    | contradiction
    | (packet_bind_head txError
       first
       | exact failed (-ENOKEY) (Or.inl rfl)
       | exact failed (-EDESTADDRREQ) (Or.inr (Or.inl rfl))
       | exact failed (-ENOMEM) (Or.inr (Or.inr rfl)))
    | (packet_bind_head branch; apply decision)
    | (packet_bind_head getPeer; refine step _ _ (getPeer_errors _) ?_; intro)
    | (packet_bind_head peerPut; refine step _ _ (peerPut_errors _) ?_; intro)
    | (packet_bind_head txWalk; refine step _ _ (walk_errors _ _ _) ?_; intro)
    | (packet_bind_head xmitTrim; refine step _ _ (trim_errors _) ?_; intro)
    | (packet_bind_head envOk; refine step _ _ (envOk_errors _) ?_; intro)
    | (packet_hoare_head Pure.pure; exact done _)
    | (packet_hoare_head ite; apply conditional; all_goals intro h)
    | simp only


theorem check_charge (family addr : Nat) (pkts : List Packet) (mtu : Nat) (initial : Option Nat) :
    Hoare (txCheck family addr pkts mtu) (fun w => errors w = initial)
      (fun accepted w => errors w = if accepted then initial else initial.map (· + 1)) := by
  let P := fun w => errors w = initial
  let post := fun (accepted : Bool) w => errors w = if accepted then initial else initial.map (· + 1)
  have decision (d : Decision) (b : Bool) (f : Bool → WG.M Bool) (hf : Hoare (f b) P post) :
      Hoare (branch d b >>= f) P post := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v clock before run
    have hb (g : WGWorld) (ambient : Ambient) :
        ((branch d b : WG.M Bool).run g).run ambient =
          .ok ((b,g),CounterWindow.record ambient d b) := rfl
    simp only [StateT.run_bind,hb,CounterWindow.except_ok_bind] at run
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ before run
  have rejected : Hoare (do
      modifyDev fun d => {d with txErrors := d.txErrors+1}
      pure false : WG.M Bool) P post := by
    have bump : Hoare (modifyDev fun d => {d with txErrors := d.txErrors+1}) P
        (fun _ w => errors w = initial.map (·+1)) := by
      apply hoare_modify
      intro w hi
      simpa only [P,errors,Option.map_map,Function.comp_def] using
        congrArg (fun n : Option Nat => n.map (·+1)) hi
    apply hoare_bind _ _ bump
    intro _
    exact hoare_consequence (hoare_pure false _) (fun _ h => h) (fun _ _ h => h.1 ▸ h.2)
  have accepted : Hoare (pure true : WG.M Bool) P post :=
    hoare_consequence (hoare_pure true P) (fun _ h => h) (fun _ _ h => h.1 ▸ h.2)
  have headers (f : Unit → WG.M Bool) (hf : ∀ x, Hoare (f x) P post) :
      Hoare (txHeaders family addr pkts >>= f) P post :=
    hoare_bind _ _ ((headers_errors family addr pkts).wp (· = initial)) hf
  have conditional (p : Prop) [Decidable p] (yes no : WG.M Bool)
      (hy : p → Hoare yes P post) (hn : ¬p → Hoare no P post) : Hoare (if p then yes else no) P post := by
    by_cases h : p
    · simpa only [ite_eq_left h] using hy h
    · simpa only [ite_eq_right h] using hn h
  change Hoare (txCheck family addr pkts mtu) P post
  cases pkts with
  | nil =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b _ run
    simp [txCheck,invariant,AmbientM.invariant] at run
    cases run
  | cons first rest =>
    simp only [txCheck,List.head?_cons,WG.andM,bind_assoc,bind_ite,pure_bind]
    repeat' first
      | contradiction
      | (packet_bind_head modifyDev; exact rejected)
      | (packet_bind_head branch; apply decision)
      | (packet_bind_head txHeaders; apply headers; intro)
      | (packet_hoare_head Pure.pure; exact accepted)
      | (packet_hoare_head ite; apply conditional; all_goals intro h)
      | simp only

def FrontResult (initial : Option Nat) (result : Except Int PeerId) (w : WGWorld) : Prop :=
  match result with
  | .error code => (code = -EPROTONOSUPPORT ∨ code = -ENOKEY ∨
      code = -EDESTADDRREQ ∨ code = -ENOMEM) ∧ errors w = initial.map (· + 1)
  | .ok _ => errors w = initial

theorem front_charge (family addr : Nat) (pkts : List Packet) (mtu : Nat) (initial : Option Nat) :
    Hoare (txFront family addr pkts mtu) (fun w => errors w = initial) (FrontResult initial) := by
  unfold txFront
  apply hoare_bind _ _ (check_charge family addr pkts mtu initial)
  intro accepted
  cases accepted with
  | false =>
    simp only [Bool.not_false,ite_true]
    apply hoare_consequence (hoare_pure (.error (-EPROTONOSUPPORT) : Except Int PeerId) _)
      (fun _ h => h)
    intro result w h
    rcases h with ⟨rfl,before⟩
    exact ⟨Or.inl rfl,before⟩
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false]
    apply hoare_bind _ _ ((lookup_errors family addr).wp (· = initial))
    intro peer
    apply hoare_bind _ _ (select_charge family pkts mtu peer initial)
    intro selected
    cases selected with
    | error code =>
      apply hoare_consequence (hoare_pure (.error code : Except Int PeerId) _) (fun _ h => h)
      intro result w h
      rcases h with ⟨rfl,named,count⟩
      exact ⟨Or.inr named,count⟩
    | ok pair =>
      rcases pair with ⟨pid,packets⟩
      apply hoare_bind _ _ ((splice_errors pid packets).wp (· = initial))
      intro _
      exact hoare_consequence (hoare_pure (.ok pid : Except Int PeerId) _)
        (fun _ h => h) (fun _ _ h => h.1 ▸ h.2)


end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
