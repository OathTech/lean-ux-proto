import Leanux.Proofs.WG.RetirementSecurity.HolderConsumeInitiation

/-! Successful native handshake consumers retain the actual acquired peer's
strictly positive spare reference. The caller can therefore repay its own
acquisition without deleting a peer that owns key slots. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConsume
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem tail_acquired (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    Hoare (HandshakeLoans.responseTail msg identity pid) (Inv temporary pid)
      (Acquired temporary) := by
  have done : Hoare (pure (some pid) : WG.M (Option PeerId))
      (Inv temporary pid) (Acquired temporary) := by
    apply hoare_consequence (hoare_pure (some pid) _) (fun _ h => h)
    intro result w before
    obtain ⟨rfl,account,strong⟩ := before
    exact ⟨account,fun other equal => Option.some.inj equal ▸ strong⟩
  have failed : Hoare (do peerPut (some pid); pure none : WG.M (Option PeerId))
      (Inv temporary pid) (Acquired temporary) :=
    hoare_bind _ _ (payment pid) (fun _ => hoare_consequence (hoare_pure none _)
      (fun _ h => h) (fun _ _ h => ⟨h.2,by intro p eq; cases h.1.symm.trans eq⟩))
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_update_head
       apply update_bind
       · intro p; rfl
       · intro p; rfl
       intro x)
    | (loan_bind_head peerPut; exact failed)
    | (index_material_head invariant; exact stop _)
    | (index_material_head Pure.pure; first | exact done | exact preserves_pure _)
    | (index_material_head Bind.bind; apply hoare_bind)
    | (index_material_head getPeer; exact getPeer_preserves _ _)
    | loan_crypto (Inv temporary pid)
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

/-- Response authentication's actual acquisition and failure repayment preserve
the exact key ledger without any independent peer-funding premise. -/
theorem response_acquired (msg : List UInt8) : Hoare (consumeResponse msg) (HolderAccount temporary) (Acquired temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have branch_run (decision : Decision) (value : Bool) (g : WGWorld) (t : Ambient) :
      ((branch decision value : WG.M Bool).run g).run t =
        .ok ((value,g),CounterWindow.record t decision value) := rfl
  rw [HandshakeLoans.consumeResponse_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,read,c,getter,rest⟩ := run
  obtain ⟨same,ambient,_⟩ := DecryptCarrier.getDev_current a c getter
  subst read
  subst c
  simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind] at rest
  split at rest
  · cases rest; exact ⟨before,by intro p eq; cases eq⟩
  · rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨entry,acquired,e,lookup,rest⟩ := rest
    have account := (hoare_iff_run_ambient _ _ _).mp
      (indexLookup_holders [.handshake] (u32le msg 8) temporary)
      w _ entry acquired e before lookup
    have loan := (hoare_iff_run_ambient _ _ _).mp
      (indexLookup_loan [.handshake] (u32le msg 8) w)
      w _ entry acquired e rfl lookup
    cases entry with
    | none =>
      simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind,Option.isNone_none,ite_true] at rest
      cases rest
      exact ⟨account,by intro p eq; cases eq⟩
    | some entry =>
      obtain ⟨owner,pid⟩ := entry
      simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind,Option.isNone_some,
        Bool.false_eq_true,ite_false] at rest
      cases owner with
      | keypair id => cases rest
      | handshake id =>
        exact (hoare_iff_run_ambient _ _ _).mp (tail_acquired msg d.staticIdentity pid)
          acquired _ result v b ⟨account,strong_loan loan⟩ rest


theorem out_failed_acquired (pid : PeerId) : Hoare (HandshakeLoans.initiationOut (some pid) none)
    (Inv temporary pid) (Acquired temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  change ((do peerPut (some pid); pure none : WG.M (Option PeerId)).run w).run
    (CounterWindow.record a .consumeFailedPut true) = .ok ((result,v),b) at run
  have failed : Hoare (do peerPut (some pid); pure none : WG.M (Option PeerId))
      (Inv temporary pid) (Acquired temporary) :=
    hoare_bind _ _ (payment pid) (fun _ => hoare_consequence (hoare_pure none _)
      (fun _ h => h) (fun _ _ h => ⟨h.2,by intro p eq; cases h.1.symm.trans eq⟩))
  exact (hoare_iff_run_ambient _ _ _).mp failed w _ result v b before run

theorem out_success_acquired (pid : PeerId) : Hoare (HandshakeLoans.initiationOut (some pid) (some pid))
    (Inv temporary pid) (Acquired temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  change Except.ok ((some pid,w),CounterWindow.record a .consumeFailedPut false) =
    .ok ((result,v),b) at run
  cases run
  exact ⟨before.1,fun other eq => Option.some.inj eq ▸ before.2⟩

theorem out_none_acquired : Hoare (HandshakeLoans.initiationOut none none) (HolderAccount temporary) (Acquired temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  change Except.ok ((none,w),CounterWindow.record (CounterWindow.record a .consumeFailedPut true) .peerPutNull true) =
    .ok ((result,v),b) at run
  cases run
  exact ⟨before,by intro p eq; cases eq⟩

theorem initiation_tail_acquired (msg e ck hash : List UInt8) (pid : PeerId) :
    Hoare (HandshakeLoans.initiationTail msg e ck hash (some pid) pid) (Inv temporary pid)
      (Acquired temporary) := by
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_update_head
       apply update_bind
       · intro p; rfl
       · intro p; rfl
       intro x)
    | (index_material_head HandshakeLoans.initiationOut; first | exact out_failed_acquired pid | exact out_success_acquired pid)
    | (index_material_head invariant; exact stop _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply hoare_bind)
    | (index_material_head getPeer; exact getPeer_preserves _ _)
    | (index_material_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (Inv temporary pid))
    | loan_crypto (Inv temporary pid)
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

theorem after_lookup_acquired (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Hoare (HandshakeLoans.initiationAfterLookup msg e ck hash peer)
      (Acquired temporary peer) (Acquired temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases peer with
  | none =>
    change ((HandshakeLoans.initiationOut none none).run w).run
      (CounterWindow.record a .consumeNoPeer true) = .ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp out_none_acquired w _ result v b before.1 run
  | some pid =>
    change ((HandshakeLoans.initiationTail msg e ck hash (some pid) pid).run w).run
      (CounterWindow.record a .consumeNoPeer false) = .ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp (initiation_tail_acquired msg e ck hash pid)
      w _ result v b ⟨before.1,before.2 pid rfl⟩ run

theorem lookup_then_acquired (key : Key) (msg e ck hash : List UInt8) :
    Hoare (pubkeyLookup key >>= HandshakeLoans.initiationAfterLookup msg e ck hash)
      (HolderAccount temporary) (Acquired temporary) :=
  hoare_bind _ _ (pubkey key) (after_lookup_acquired msg e ck hash)

/-- Original initiation consumption transports the exact key account through
actual acquisition, replay/flood rejection and success, with no external peer
credit assumption substituted for its own acquisition. -/
theorem initiation_acquired (msg : List UInt8) : Hoare (consumeInitiation msg) (HolderAccount temporary) (Acquired temporary) := by
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_bind_head pubkeyLookup; exact lookup_then_acquired _ _ _ _ _)
    | (index_material_head HandshakeLoans.initiationOut; exact out_none_acquired)
    | (index_material_head invariant; exact stop _)
    | (index_material_head Bind.bind; apply hoare_bind)
    | (index_material_head getDev
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a d v b before run
       exact (DecryptCarrier.getDev_current a b run).1 ▸ before)
    | loan_crypto (HolderAccount temporary)
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match

end Leanux.Proofs.WG.RetirementSecurity.HolderConsume
