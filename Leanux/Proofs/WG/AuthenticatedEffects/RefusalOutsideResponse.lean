import Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutsideFrames

/-! Original response refusal preserves every field outside the two resident maps. The actual lookup supplies the non-final repayment condition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutside
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def RefusalProtocol (initial : WGWorld) (result : Option PeerId) (w : WGWorld) : Prop :=
  result = none → view w = initial

private theorem chain {α β : Type} (P : WGWorld → Prop) (Q : β → WGWorld → Prop)
    (action : WG.M α) (next : α → WG.M β) (ha : Preserves P action)
    (tail : ∀ x, Hoare (next x) P Q) : Hoare (action >>= next) P Q :=
  hoare_bind action next ha tail

theorem response_tail (msg : Key) (identity : StaticIdentity)
    (pid : PeerId) (initial : WGWorld) :
    Hoare (responseTail msg identity pid)
      (fun w => view w = initial ∧ RepaySafe pid w) (RefusalProtocol initial) := by
  let P := fun w => view w = initial ∧ RepaySafe pid w
  have read (q : PeerId) : Preserves P (getPeer q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    rw [(Leanux.Proofs.WG.Queues.getPeer_normal q w v p a b run).1]
    exact hi
  have failed : Hoare (do peerPut (some pid); pure (none : Option PeerId)) P (RefusalProtocol initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run _
    rw [native_bind_run] at run
    cases paid : ((peerPut (some pid)).run w).run a with
    | error err => simp [paid] at run
    | ok out =>
      rcases out with ⟨⟨doneUnit,q⟩,c⟩
      cases doneUnit
      have frame := repay pid w q a c hi.2 paid
      rw [paid] at run
      cases run
      exact frame.trans hi.1
  have success (p : Peer) : Hoare (do setPeer pid p; pure (some pid)) P (RefusalProtocol initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run none
    simp only [setPeer,modifyDev,StateT.run_bind,StateT.run_modify,StateT.run_pure,
      except_ok_bind,except_pure] at run
    cases run
    cases none
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  have stop (message : String) : Hoare (invariant message : WG.M (Option PeerId)) P (RefusalProtocol initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    cases run
  unfold responseTail
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | with_reducible exact failed
    | with_reducible exact success _
    | with_reducible exact stop _
    | with_reducible exact read _
    | with_reducible exact ambient _
    | receive_crypto P
    | cookie_source_step
    | with_reducible apply chain P
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem response (msg : Key) (w v : WGWorld) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a = .ok ((none,v),b)) :
    view v = view w := by
  rw [consumeResponse_factor] at run
  cases hd : w.dev with
  | none => simp [getDev,hd,invariant,AmbientM.invariant,StateT.run_bind] at run; cases run
  | some device =>
    cases identity : device.staticIdentity.hasIdentity with
    | false =>
      simp [getDev,hd,identity,branch,branch_run,StateT.run_bind] at run
      obtain ⟨rfl,_⟩ := run
      rfl
    | true =>
      simp [getDev,hd,identity,branch,branch_run,StateT.run_bind] at run
      cases lookup : ((indexLookup [.handshake] (u32le msg 8)).run w).run
          (record a .crespNoIdentity false) with
      | error err => simp [lookup] at run
      | ok out =>
        rcases out with ⟨⟨entry,u⟩,c⟩
        have frame := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
          (RefusalOutside.lookup [.handshake] (u32le msg 8)) w _ entry u c lookup
        have loan := (hoare_iff_run_ambient _ _ _).mp
          (indexLookup_loan [.handshake] (u32le msg 8) w) w _ entry u c rfl lookup
        cases entry with
        | none =>
          simp [lookup] at run
          obtain ⟨rfl,_⟩ := run
          exact frame
        | some entry =>
          rcases entry with ⟨owner,pid⟩
          cases owner with
          | keypair kid => simp [lookup,invariant,AmbientM.invariant] at run; cases run
          | handshake owner =>
            simp only [lookup,except_ok_bind,Option.isNone_some] at run
            exact (hoare_iff_run_ambient _ _ _).mp
              (response_tail msg device.staticIdentity pid (view w))
              u _ none v b ⟨frame,loan_repay_safe w u pid loan⟩ run rfl

end Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutside
