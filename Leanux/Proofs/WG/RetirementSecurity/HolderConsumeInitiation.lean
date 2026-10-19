import Leanux.Proofs.WG.RetirementSecurity.HolderConsumeResponse

/-! Initiation authentication's own public-key acquisition protects failure
repayment. Replay, flood and cryptographic rejection preserve key references;
successful consumption keeps only its actual peer loan for the caller. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConsume
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem pubkey_points (key : Key) : SameView ownershipPointView (pubkeyLookup key) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact (peerGetMaybe_ownership _).wp (· = initial))
    | ownership_source_step initial

def Acquired (temporary : Credits.Ledger) (result : Option PeerId) (w : WGWorld) :=
  HolderAccount temporary w ∧ ∀ pid, result = some pid → Strong pid w

theorem pubkey (key : Key) : Hoare (pubkeyLookup key)
    (HolderAccount temporary) (Acquired temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  refine ⟨before.points ((ProjectedAction.iff_run_ambient _ _ _).mp
    (pubkey_points key) w a result v b run),?_⟩
  intro pid returned
  subst result
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.pubkeyLookup_borrowed_spec key (wgStoreView w)) w a (some pid) v b rfl run
  obtain ⟨d,p,device,stored,positive,output⟩ := borrowed
  have final : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
    congrArg WGStoreView.dev output
  simpa [Strong,peerView,final] using (show 1 < p.refcount + 1 by omega)

theorem out_failed (pid : PeerId) : Hoare (HandshakeLoans.initiationOut (some pid) none)
    (Inv temporary pid) (fun _ => HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  change ((do peerPut (some pid); pure none : WG.M (Option PeerId)).run w).run
    (CounterWindow.record a .consumeFailedPut true) = .ok ((result,v),b) at run
  have failed : Hoare (do peerPut (some pid); pure none : WG.M (Option PeerId))
      (Inv temporary pid) (fun _ => HolderAccount temporary) :=
    hoare_bind _ _ (payment pid) (fun _ => hoare_consequence (hoare_pure none _)
      (fun _ h => h) (fun _ _ h => h.2))
  exact (hoare_iff_run_ambient _ _ _).mp failed w _ result v b before run

theorem out_success (pid : PeerId) : Hoare (HandshakeLoans.initiationOut (some pid) (some pid))
    (Inv temporary pid) (fun _ => HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  change Except.ok ((some pid,w),CounterWindow.record a .consumeFailedPut false) =
    .ok ((result,v),b) at run
  cases run
  exact before.1

theorem out_none : Preserves (HolderAccount temporary) (HandshakeLoans.initiationOut none none) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  change Except.ok ((none,w),CounterWindow.record (CounterWindow.record a .consumeFailedPut true) .peerPutNull true) =
    .ok ((result,v),b) at run
  cases run
  exact before

theorem initiation_tail (msg e ck hash : List UInt8) (pid : PeerId) :
    Hoare (HandshakeLoans.initiationTail msg e ck hash (some pid) pid) (Inv temporary pid)
      (fun _ => HolderAccount temporary) := by
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
    | (index_material_head HandshakeLoans.initiationOut; first | exact out_failed pid | exact out_success pid)
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

theorem after_lookup (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Hoare (HandshakeLoans.initiationAfterLookup msg e ck hash peer)
      (Acquired temporary peer) (fun _ => HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases peer with
  | none =>
    change ((HandshakeLoans.initiationOut none none).run w).run
      (CounterWindow.record a .consumeNoPeer true) = .ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp out_none w _ result v b before.1 run
  | some pid =>
    change ((HandshakeLoans.initiationTail msg e ck hash (some pid) pid).run w).run
      (CounterWindow.record a .consumeNoPeer false) = .ok ((result,v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp (initiation_tail msg e ck hash pid)
      w _ result v b ⟨before.1,before.2 pid rfl⟩ run

theorem lookup_then (key : Key) (msg e ck hash : List UInt8) :
    Preserves (HolderAccount temporary)
      (pubkeyLookup key >>= HandshakeLoans.initiationAfterLookup msg e ck hash) :=
  hoare_bind _ _ (pubkey key) (after_lookup msg e ck hash)

/-- Original initiation consumption transports the exact key account through
actual acquisition, replay/flood rejection and success, with no external peer
credit assumption substituted for its own acquisition. -/
theorem initiation (msg : List UInt8) : Preserves (HolderAccount temporary) (consumeInitiation msg) := by
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_bind_head pubkeyLookup; exact lookup_then _ _ _ _ _)
    | (index_material_head HandshakeLoans.initiationOut; exact out_none)
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
