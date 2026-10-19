import Leanux.Proofs.WG.AuthenticatedEffects.RefusalPositiveKeys

/-! The complementary refusal projection retains every native WG field outside
its two resident maps. Together with pointwise complete peer/keypair records it
omits only balanced-tree representation, not an index, timer or device field. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutside
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def device (d : Device) : Device := {d with peers := {}, keypairs := {}}
def view (w : WGWorld) : WGWorld := {w with dev := w.dev.map device}

theorem get_peer (pid : PeerId) (P : WGWorld → Prop) : Preserves P (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b initial run
  obtain ⟨rfl,_,_,_,_⟩ := Queues.getPeer_normal pid w v p a b run
  exact initial

theorem set_peer (pid : PeerId) (p : Peer) : SameView view (setPeer pid p) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  cases hd : w.dev <;> simp [view,device,hd]

theorem set_key (kid : KeypairId) (key : Keypair) : SameView view (setKeypair kid key) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  cases hd : w.dev <;> simp [view,device,hd]

theorem get_key (kid : KeypairId) (P : WGWorld → Prop) : Preserves P (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b initial run
  cases hd : w.dev with
  | none => simp [getKeypair,getDev,hd,invariant,AmbientM.invariant,StateT.run_bind] at run; cases run
  | some d =>
    cases hk : d.keypairs[kid]? with
    | none => simp [getKeypair,getDev,hd,hk,invariant,AmbientM.invariant,StateT.run_bind] at run; cases run
    | some k =>
      simp [getKeypair,getDev,hd,hk,StateT.run_bind] at run
      obtain ⟨⟨rfl,rfl⟩,_⟩ := run
      exact initial

theorem maybe (peer : Option PeerId) : SameView view (peerGetMaybeZero peer) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold peerGetMaybeZero
  simp only [requireNotPending,branch,refcountIncNotZero,branchCmp,invariant,unsupported]
  repeat' first
    | (cookie_source_head getPeer; exact get_peer _ _)
    | (cookie_source_head setPeer; exact (set_peer _ _).wp (fun v => v = initial))
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | cookie_source_step

theorem owner_word (owner : IndexOwner) (word : Option PeerId) :
    SameView view (owner.setPeerWord word) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  cases owner <;> unfold IndexOwner.setPeerWord
  all_goals repeat' first
    | (cookie_source_head getPeer; exact get_peer _ _)
    | (cookie_source_head getKeypair; exact get_key _ _)
    | (cookie_source_head setPeer; exact (set_peer _ _).wp (fun v => v = initial))
    | (cookie_source_head setKeypair; exact (set_key _ _).wp (fun v => v = initial))
    | cookie_source_step

theorem acquire (owner : IndexOwner) : SameView view (Affiliation.acquireOwner owner) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold Affiliation.acquireOwner
  repeat' first
    | (cookie_source_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
    | (cookie_source_head IndexOwner.setPeerWord; exact (owner_word _ _).wp (fun v => v = initial))
    | (cookie_source_head peerGetMaybeZero; exact (maybe _).wp (fun v => v = initial))
    | cookie_source_step

theorem lookup (kinds : List IndexKind) (index : Nat) : SameView view (indexLookup kinds index) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  rw [ResponseLoan.lookup_factor]
  apply preserves_bind ((ResponseLoan.scan_same_world kinds index).wp (fun w => view w = initial))
  intro state
  unfold ResponseLoan.lookupTail
  simp only [branch,invariant]
  repeat' first
    | (cookie_source_head Affiliation.acquireOwner; exact (acquire _).wp (fun v => v = initial))
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | cookie_source_step

theorem repay (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (safe : RepaySafe pid w)
    (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) : view v = view w := by
  obtain ⟨d,p,hd,hp,count⟩ := safe
  have positive : 0 < p.refcount := by omega
  have zero : p.refcount ≠ 0 := by omega
  have final : p.refcount ≠ 1 := by omega
  simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,refcountDecAndTest,
    branch,branchCmp,branch_run,branchCmp_run,hd,hp,positive,zero,final,
    StateT.run_bind,StateT.run_pure,StateT.run_monadLift,except_ok_bind,except_pure] at run
  obtain ⟨rfl,_⟩ := run
  simp [view,device,hd]

end Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutside
