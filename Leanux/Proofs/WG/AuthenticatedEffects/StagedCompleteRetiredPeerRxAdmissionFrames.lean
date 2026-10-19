import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxFinishFrames

/-! Admission joins its actual lookup loan to the newly allocated carrier.
Rejected admission pays that same loan. The complete source, rather than a
chosen successful lookup or assumed publication, determines these cases. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem credit_owner (view : peerView v = peerView (creditWorld w d pid p))
    (found : RxCredits.resident v owner = some q) (slot : owner.slot = pid) :
    owner = ⟨d.ifindex,pid,p.internalId⟩ := by
  obtain ⟨dv,device,epoch,stored,stamp⟩ := resident_fields found
  have epochs : dv.ifindex = d.ifindex := by
    simpa [peerView,creditWorld,device] using congrArg Prod.fst view
  have fields : (q.internalId,q.refcount,q.rxQueue) = (p.internalId,p.refcount+1,p.rxQueue) := by
    have installed : dv.peers[pid]? = some q := by simpa only [slot] using stored
    simpa [peerView,creditWorld,device,slot,installed] using congrFun (congrArg Prod.snd view) owner.slot
  have stamps := congrArg Prod.fst fields
  cases owner
  simp_all

theorem Upper.loan_repay (upper : Upper holders carriers loans w)
    (loan : Loan w pid u) (a b : Ambient)
    (run : ((peerPut pid).run u).run a = .ok (((),v),b)) :
    Upper holders carriers loans v := by
  cases pid with
  | none =>
    have same : v = u := by
      simp [peerPut,branch,CounterWindow.branch_run,StateT.run_bind,StateT.run_pure,
        StateT.run_monadLift,CounterWindow.except_ok_bind,CounterWindow.except_pure] at run
      exact run.1.symm
    subst v
    exact upper.peer_view loan.1
  | some pid =>
    obtain ⟨d,p,device,found,positive,view,_⟩ := loan
    intro owner
    rw [credit_repayment device found positive view a b run owner]
    exact upper owner

theorem Upper.admit_none (upper : Upper holders carriers loans w) (ambient ambient' : Ambient)
    (run : ((RxOrigin.admitSource msg src ds).run w).run ambient = .ok ((none,v),ambient')) :
    Upper holders carriers loans v := by
  rw [RxOrigin.admitSource_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨entry,a,aa,lookup,acquired,b,ab,acquire,noKey,c,ac,test,tail⟩ := run
  rcases acquired with ⟨kp,pid⟩
  have front := lookup_front ambient aa ab lookup acquire
  have same : c = b := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .dataNoKeypair kp.isNone) (fun g => g = b))
    b ab noKey c ac rfl test
  have atCut : AdmissionFront w pid c := by simpa only [same] using front
  cases noKey with
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨u,z,az,pay,finish⟩ := tail
    cases u
    obtain ⟨⟨_,rfl⟩,rfl⟩ := finish
    exact upper.loan_repay atCut.loan ac _ pay
  | false =>
    simp only [Bool.false_eq_true,ite_false] at tail
    cases kp with
    | none => simp [invariant,AmbientM.invariant] at tail; cases tail
    | some kid =>
      cases pid with
      | none => simp [invariant,AmbientM.invariant] at tail; cases tail
      | some pid =>
        simp only [MaterialOrigin.bind_ok_ambient] at tail
        obtain ⟨peer,d,ad,read,dead,e,ae,check,tail⟩ := tail
        have sameD : d = c := (getPeer_normal pid c d peer ac ad read).1
        have sameE : e = d := (hoare_iff_run_ambient _ _ _).mp
          (hoare_liftAmbient (AmbientM.branch .dataPeerDead peer.isDead) (fun g => g = d))
          d ad dead e ae rfl check
        have before : AdmissionFront w (some pid) e := by simpa only [sameE,sameD] using atCut
        cases dead with
        | true =>
          simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
          obtain ⟨u,f,af,key,u',g,ag,pay,finish⟩ := tail
          cases u
          cases u'
          obtain ⟨⟨_,rfl⟩,rfl⟩ := finish
          exact upper.loan_repay (before.keyPut ae af key).loan af _ pay
        | false =>
          simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
          obtain ⟨slot,z,az,allocation,bad⟩ := tail
          simp at bad

theorem Account.admit_none (account : Account holders carriers loans w) (a b : Ambient)
    (run : ((RxOrigin.admitSource msg src ds).run w).run a = .ok ((none,v),b)) :
    Account holders carriers loans v := by
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderAdmission.admit_frame msg src ds w)
    w a none v b (Frame.refl w) run
  exact ⟨⟨account.funded.aligned.frame frame,admitted_none account.funded.carriers a b run⟩,
    account.upper.admit_none a b run,admitted_none_stable account.stable a b run⟩

theorem Account.admit_some (account : Account holders carriers loans w) (fresh : Packets.Inv w)
    (a b : Ambient)
    (run : ((RxOrigin.admitSource msg src ds).run w).run a = .ok ((some ctx,v),b)) :
    ∃ owner,
      Phased holders (⟨⟨owner.epoch,ctx.slot⟩,owner,.unpublished⟩ :: carriers) loans v ∧
      StableRx carriers v ∧ owner.slot = ctx.packet.peer ∧
      KeyWord ctx.packet.keypair ctx.packet.peer v ∧ RxOrigin.Admitted msg src ds ctx w v a b := by
  obtain ⟨owner,funded,slot,word,admitted⟩ := admitted_state account.funded.carriers fresh a b run
  obtain ⟨before,aa,loan,allocation⟩ := admitted_loan a b run
  obtain ⟨d,p,device,found,positive,upper⟩ := account.upper.loan loan
  obtain ⟨other,q,otherDevice,otherFound,_,view,_⟩ := loan
  have eq := Option.some.inj (device.symm.trans otherDevice)
  subst other
  have eq := Option.some.inj (found.symm.trans otherFound)
  subst q
  have output := (ProjectedAction.iff_run_ambient _ _ _).mp (allocate_rx_peers ctx.packet)
    before aa ctx.slot v b allocation
  have charged : 0 < demand (⟨⟨owner.epoch,ctx.slot⟩,owner,.unpublished⟩ :: carriers)
      (holders.owners ++ loans) owner := by simp [demand,Phase.charged]; omega
  obtain ⟨q,resident,_⟩ := protected_resident funded.funded charged
  have identity := credit_owner (output.trans view) resident slot
  have bound : Upper holders carriers (owner :: loans) v := by
    simpa only [identity] using upper.peer_view output
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderAdmission.admit_frame msg src ds w)
    w a (some ctx) v b (Frame.refl w) run
  exact ⟨owner,⟨⟨account.funded.aligned.frame frame,funded⟩,bound.loan_to_carrier rfl⟩,
    admitted_stable_front account.stable account.funded.carriers.inventory fresh a b run,
    slot,word,admitted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
