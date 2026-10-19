import Leanux.Proofs.WG.RetirementSecurity.SessionPeerFunding

/-! A handshake response's failure payment cannot retire its acquired peer:
the actual nonzero acquisition leaves at least two peer references. This
source-local fact is independent of the initialized key-credit invariant. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConsume
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
variable {selected : PeerId}

def Strong (pid : PeerId) (w : WGWorld) : Prop :=
  1 < (((peerView w).2 pid).map (fun p => p.2.1)).getD 0

def Inv (temporary : Credits.Ledger) (pid : PeerId) (w : WGWorld) :=
  HolderAccount temporary w ∧ Strong pid w

theorem stop (why : String) : Hoare (invariant why : WG.M α) P Q := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases run

theorem strong_loan (loan : Loan w (some pid) v) : Strong pid v := by
  obtain ⟨d,p,device,stored,positive,peers,_⟩ := loan
  unfold Strong
  rw [peers]
  simpa [peerView,creditWorld] using (show 1 < p.refcount + 1 by omega)

theorem payment (pid : PeerId) : Hoare (peerPut (some pid))
    (Inv temporary pid) (fun _ => HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  apply before.1.peer_put ?_ a b run
  intro p found final
  have count := before.2
  unfold Strong at count
  have mapped : (peerView w).2 pid = some (p.internalId,p.refcount,p.rxQueue) := by
    simpa only [peerView,peerAt,Option.bind_map,Option.map_some] using congrArg
      (Option.map (fun p : Peer => (p.internalId,p.refcount,p.rxQueue))) found
  simp only [mapped,Option.map_some,Option.getD_some,final] at count
  omega

theorem update (pid : PeerId) (f : Peer → Peer)
    (fields : ∀ p, peerOwnership (f p) = peerOwnership p)
    (count : ∀ p, (f p).refcount = p.refcount) :
    Preserves (Inv temporary selected) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have keys := (ProjectedAction.iff_run_ambient _ _ _).mp
    (updatePeer_ownership pid f fields) w a result v b run
  refine ⟨before.1.ownership keys,?_⟩
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,getter,setter⟩ := run
  obtain ⟨rfl,rfl,d,device,stored⟩ := getPeer_normal pid w u p a c getter
  cases setter
  have old := before.2
  unfold Strong peerView at old ⊢
  by_cases same : pid = selected
  · subst selected
    simpa [device,stored,count] using old
  · simpa [device,Std.TreeMap.getElem?_insert,same] using old

theorem update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (fields : ∀ p, peerOwnership (f p) = peerOwnership p)
    (count : ∀ p, (f p).refcount = p.refcount)
    (rest : ∀ x, Hoare (tail x) (Inv temporary selected) Q) :
    Hoare (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) (Inv temporary selected) Q := by
  simpa only [bind_assoc] using hoare_bind _ _ (update pid f fields count) rest

theorem tail (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    Hoare (HandshakeLoans.responseTail msg identity pid) (Inv temporary pid)
      (fun _ => HolderAccount temporary) := by
  have done (value : Option PeerId) : Hoare (pure value : WG.M (Option PeerId))
      (Inv temporary pid) (fun _ => HolderAccount temporary) :=
    hoare_consequence (hoare_pure value _) (fun _ h => h)
      (fun _ _ h => h.2.1)
  have failed : Hoare (do peerPut (some pid); pure none : WG.M (Option PeerId))
      (Inv temporary pid) (fun _ => HolderAccount temporary) :=
    hoare_bind _ _ (payment pid) (fun _ => hoare_consequence (hoare_pure none _)
      (fun _ h => h) (fun _ _ h => h.2))
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
    | (index_material_head Pure.pure; first | exact done _ | exact preserves_pure _)
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
theorem response (msg : List UInt8) : Preserves (HolderAccount temporary) (consumeResponse msg) := by
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
  · cases rest; exact before
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
      exact account
    | some entry =>
      obtain ⟨owner,pid⟩ := entry
      simp only [StateT.run_bind,branch_run,CounterWindow.except_ok_bind,Option.isNone_some,
        Bool.false_eq_true,ite_false] at rest
      cases owner with
      | keypair id => cases rest
      | handshake id =>
        exact (hoare_iff_run_ambient _ _ _).mp (tail msg d.staticIdentity pid)
          acquired _ result v b ⟨account,strong_loan loan⟩ rest

end Leanux.Proofs.WG.RetirementSecurity.HolderConsume
