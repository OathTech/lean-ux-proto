import Leanux.Proofs.WG.RetirementSecurity.RxAdmissionHolders
import Leanux.Proofs.WG.RetirementSecurity.TxAcquireHolders

/-! Original receive admission's no-key and dead-peer returns repay their
actual lookup borrow. A refused key acquisition creates no key reference;
the dead-peer branch pays exactly the reference it just acquired. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem get_none_world (kp : Option KeypairId) (a b : Ambient)
    (run : ((keypairGet kp).run w).run a = .ok ((none,v),b)) : v = w := by
  cases kp with
  | none =>
    simp [keypairGet,branch,AmbientM.branch] at run
    exact run.1.symm
  | some id =>
    cases device : w.dev with
    | none =>
      simp [keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases found : d.keypairs[id]? with
      | none =>
        simp [keypairGet,branch,AmbientM.branch,getKeypair,getDev,device,found,invariant,AmbientM.invariant] at run
        cases run
      | some k =>
        by_cases zero : k.refcount = 0
        · simp [keypairGet,refcountIncNotZero,branch,branchCmp,AmbientM.branch,AmbientM.branchCmp,
            getKeypair,getDev,device,found,zero] at run
          exact run.1.symm
        · have impossible := get_positive_result (by simpa [keyAt,device] using found)
            (by omega) a b run
          cases impossible

theorem receive_key_none_world (entry : Option (IndexOwner × PeerId)) (a b : Ambient)
    (run : ((Affiliation.receiveKeyAcquire entry).run w).run a = .ok (((none,pid),v),b)) :
    v = w := by
  cases entry with
  | none =>
    simp [Affiliation.receiveKeyAcquire,keypairGetNull,branch,AmbientM.branch] at run
    exact run.1.2.symm
  | some entry =>
    obtain ⟨owner,peer⟩ := entry
    cases owner with
    | handshake id =>
      simp [Affiliation.receiveKeyAcquire,invariant,AmbientM.invariant] at run
      cases run
    | keypair id =>
      simp only [Affiliation.receiveKeyAcquire,pure_bind,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨out,u,c,keyRun,tail⟩ := run
      cases tail
      exact get_none_world (some id) a b keyRun

theorem HolderAccount.repay_lookup (account : HolderAccount temporary w)
    (loan : Queues.RxCredits.Loan initial pid w) (a b : Ambient)
    (run : ((peerPut pid).run w).run a = .ok (((),v),b)) : HolderAccount temporary v := by
  cases pid with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    exact run.1.symm ▸ account
  | some pid => exact account.peer_put (lookup_loan_ready loan) a b run

theorem HolderAccount.admit_none (account : HolderAccount temporary w)
    (msg : List UInt8) (src : SkbSource) (ds : Nat) (a b : Ambient)
    (run : ((RxOrigin.admitSource msg src ds).run w).run a = .ok ((none,v),b)) :
    HolderAccount temporary v := by
  rw [RxOrigin.admitSource_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨entry,u,c,lookupRun,acquired,t,e,keyRun,noKey,s,f,noKeyRun,tail⟩ := run
  obtain ⟨kp,pid⟩ := acquired
  have hu := (hoare_iff_run_ambient _ _ _).mp
    (indexLookup_holders [.keypair] (u32le msg 4) temporary) w a entry u c account lookupRun
  have front := Queues.RxCredits.lookup_front a c e lookupRun keyRun
  cases kp with
  | none =>
    have same := receive_key_none_world entry c e keyRun
    subst t
    change Except.ok ((true,u),CounterWindow.record e .dataNoKeypair true) =
      .ok ((noKey,s),f) at noKeyRun
    cases noKeyRun
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,z,g,putRun,done⟩ := tail
    cases done
    exact hu.repay_lookup front.loan _ b putRun
  | some kid =>
    change Except.ok ((false,t),CounterWindow.record e .dataNoKeypair false) =
      .ok ((noKey,s),f) at noKeyRun
    cases noKeyRun
    simp only [Bool.false_eq_true,ite_false] at tail
    cases pid with
    | none =>
      simp [invariant,AmbientM.invariant] at tail
      cases tail
    | some pid =>
      obtain ⟨allocation,key,ht⟩ := hu.receive_key entry c e keyRun
      simp only [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨p,z,g,peerRun,dead,y,h,deadRun,tail⟩ := tail
      have sameZ := (Queues.getPeer_normal pid t z p _ g peerRun).1
      subst z
      have sameY : y = t := (hoare_iff_run_ambient _ _ _).mp
        (hoare_liftAmbient (AmbientM.branch .dataPeerDead p.isDead) (fun s => s = t))
        t g dead y h rfl deadRun
      subst y
      cases dead with
      | false =>
        simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨_,_,_,_,impossible⟩ := tail
        simp at impossible
      | true =>
        simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨_,z,g,keyPutRun,_,s,f,peerPutRun,done⟩ := tail
        cases done
        have after := front.keyPut h g keyPutRun
        rw [← key] at keyPutRun
        exact (ht.put false h g keyPutRun).repay_lookup after.loan g b peerPutRun

end Leanux.Proofs.WG.RetirementSecurity
