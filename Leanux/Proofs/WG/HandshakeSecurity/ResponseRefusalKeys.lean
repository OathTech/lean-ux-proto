import Leanux.Proofs.WG.AuthenticatedEffects.RefusalPositiveKeys

/-! Native refused responses preserve full keypair records. The actual lookup
provides its loan; the failed lookup arm uses resident-peer positivity. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResponseKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.Cookies
open Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
open Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
open Leanux.Proofs.WG.AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def Restored (initial : WGWorld) (result : Option PeerId) (w : WGWorld) : Prop :=
  result = none → residentKeys w = residentKeys initial

private theorem chain {α β : Type} (P : WGWorld → Prop) (Q : β → WGWorld → Prop)
    (action : WG.M α) (next : α → WG.M β) (ha : Preserves P action)
    (tail : ∀ x, Hoare (next x) P Q) : Hoare (action >>= next) P Q :=
  hoare_bind action next ha tail

theorem tail (msg : Key) (identity : StaticIdentity) (pid : PeerId) (initial : WGWorld) :
    Hoare (responseTail msg identity pid)
      (fun w => Loan initial pid w ∧ residentKeys w = residentKeys initial) (Restored initial) := by
  let P := fun w => Loan initial pid w ∧ residentKeys w = residentKeys initial
  have read (q : PeerId) : Preserves P (getPeer q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    rw [(Queues.getPeer_normal q w v p a b run).1]
    exact hi
  have failed : Hoare (do peerPut (some pid); pure (none : Option PeerId)) P (Restored initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run _
    rw [native_bind_run] at run
    cases paid : ((peerPut (some pid)).run w).run a with
    | error err => simp [paid] at run
    | ok out =>
      rcases out with ⟨⟨doneUnit,q⟩,c⟩
      cases doneUnit
      have frame := (repay_keys initial w q pid a c hi.1 paid).trans hi.2
      rw [paid] at run
      cases run
      exact frame
  have success (p : Peer) : Hoare (do setPeer pid p; pure (some pid)) P (Restored initial) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run none
    simp only [setPeer,modifyDev,StateT.run_bind,StateT.run_modify,StateT.run_pure,
      except_ok_bind,except_pure] at run
    cases run
    cases none
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  have stop (message : String) : Hoare (invariant message : WG.M (Option PeerId)) P (Restored initial) := by
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

theorem refusal (msg : Key) (w v : WGWorld) (a b : Ambient)
    (positive : Positive w)
    (run : ((consumeResponse msg).run w).run a = .ok ((none,v),b)) :
    residentKeys v = residentKeys w := by
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
        cases entry with
        | none =>
          simp [lookup] at run
          obtain ⟨rfl,_⟩ := run
          exact (index_none _ _ _ _ _ _ positive lookup).2
        | some entry =>
          rcases entry with ⟨owner,pid⟩
          have loan := index_success [.handshake] (u32le msg 8) w u owner pid _ c lookup
          have keys := index_success_keys [.handshake] (u32le msg 8) w u owner pid _ c lookup
          cases owner with
          | keypair kid => simp [lookup,invariant,AmbientM.invariant] at run; cases run
          | handshake owner =>
            simp only [lookup,except_ok_bind,Option.isNone_some] at run
            exact (hoare_iff_run_ambient _ _ _).mp
              (tail msg device.staticIdentity pid w) u _ none v b ⟨loan,keys⟩ run rfl

end Leanux.Proofs.WG.HandshakeSecurity.ResponseKeys
