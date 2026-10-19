import Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoanView

/-! A source-acquired successful response loan restores every peer field on
refusal. This uses pointwise resident records and does not mask owner words or
reference counts. The unsuccessful lookup arm remains a distinct obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Cookies
open Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem repay (initial w v : WGWorld) (pid : PeerId) (a b : Ambient)
    (loan : Loan initial pid w)
    (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    residents v = residents initial := by
  obtain ⟨p,old,positive,peers⟩ := loan
  have selected : residents w pid = some {p with refcount := p.refcount + 1} := by
    simpa using peers pid
  obtain ⟨d,hd,hp⟩ := Option.bind_eq_some_iff.mp selected
  have nonzero : p.refcount ≠ 0 := by omega
  simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,refcountDecAndTest,
    branch,branchCmp,branch_run,branchCmp_run,hd,hp,nonzero,
    StateT.run_bind,StateT.run_pure,StateT.run_monadLift,except_ok_bind,except_pure] at run
  obtain ⟨rfl,_⟩ := run
  funext q
  by_cases equal : pid = q
  · subst q
    rw [old]
    simp [residents]
  · have outside := peers q
    simpa [residents,hd,Std.TreeMap.getElem?_insert,equal,Ne.symm equal] using outside

private def Restored (initial : WGWorld) (result : Option PeerId) (w : WGWorld) : Prop :=
  result = none → residents w = residents initial

private theorem chain {α β : Type} (P : WGWorld → Prop) (Q : β → WGWorld → Prop)
    (action : WG.M α) (next : α → WG.M β) (ha : Preserves P action)
    (tail : ∀ x, Hoare (next x) P Q) : Hoare (action >>= next) P Q :=
  hoare_bind action next ha tail

theorem response_tail (msg : Key) (identity : StaticIdentity) (pid : PeerId) (initial : WGWorld) :
    Hoare (responseTail msg identity pid) (Loan initial pid) (Restored initial) := by
  let P := Loan initial pid
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
      have frame := repay initial w q pid a c hi paid
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

end Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
