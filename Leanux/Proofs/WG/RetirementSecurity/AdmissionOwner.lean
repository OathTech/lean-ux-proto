import Leanux.Proofs.WG.RetirementSecurity.TxStagedHolders
import Leanux.Proofs.WG.Queues.CurrentSlots

/-! The native peer acquisition immediately before TX allocation identifies
the batch's actual owner. Nullable slot compatibility is enough: successful
acquisition supplies the non-NULL word. This is an admission snapshot, not a
claim that later owner bookkeeping remains non-NULL. CurrentSlots.Inv stays
an explicit local premise; these contracts do not manufacture an initialized
internal-cut invariant from endpoint erasure. -/
namespace Leanux.Proofs.WG.RetirementSecurity.AdmissionOwner
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

/-- Full native entry records and the exact peer-reference increment. The key
record, including allocation stamp and sending material, is retained. -/
def Certificate (pid : PeerId) (kid : KeypairId) (w v : WGWorld) : Prop :=
  ∃ d k p, w.dev=some d ∧ d.keypairs[kid]?=some k ∧ k.peer=some pid ∧
    d.peers[pid]?=some p ∧ 0<p.refcount ∧
    v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}}

theorem acquire (compatible : Queues.RxCredits.KeyCompatible pid kid w)
    (a b : Ambient)
    (run : ((Affiliation.sendAcquire kid).run w).run a=.ok (((),v),b)) :
    Certificate pid kid w v := by
  obtain ⟨d,k,actual,p,device,resident,word,stored,positive,borrow⟩ :=
    Affiliation.sendAcquire_certificate kid w v a b run
  have owner : actual=pid := by
    simpa [Affiliation.Compatible,word] using compatible d k device resident
  subst actual
  obtain ⟨d',p',device',stored',_,current⟩ := borrow
  have sameDevice : d'=d := Option.some.inj (device'.symm.trans device)
  subst d'
  have samePeer : p'=p := Option.some.inj (stored'.symm.trans stored)
  subst p'
  exact ⟨d,k,p,device,resident,word,stored,positive,congrArg WGStoreView.dev current⟩

theorem Certificate.key (certificate : Certificate pid kid w v) :
    ∃k, keyAt w kid=some k ∧ k.peer=some pid ∧ keyAt v kid=some k := by
  obtain ⟨d,k,p,device,resident,word,_,_,after⟩ := certificate
  exact ⟨k,by simp [keyAt,device,resident],word,by simp [keyAt,after,resident]⟩

theorem current (slots : CurrentSlots.Inv w) (device : w.dev=some d)
    (selected : d.peers[pid]?=some p) (slot : p.keypairCurrent=some kid)
    (a b : Ambient)
    (run : ((Affiliation.sendAcquire kid).run w).run a=.ok (((),v),b)) :
    Certificate pid kid w v :=
  acquire ((CurrentSlots.current slots).compatible pid d p kid device selected slot) a b run

/-- Exact decomposition of the original post-reservation submission suffix.
The historical owner fact holds both before acquisition and at the allocator
output, before createData can unpublish or release any references. -/
theorem submit (compatible : Queues.RxCredits.KeyCompatible pid kid w)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((do
      Affiliation.sendAcquire kid
      let items ← packets.mapM newTxSkb
      createData pid items).run w).run a=.ok (((),v),b)) :
    ∃u c items t e k,
      ((Affiliation.sendAcquire kid).run w).run a=.ok (((),u),c) ∧
      Certificate pid kid w u ∧
      ((packets.mapM newTxSkb).run u).run c=.ok ((items,t),e) ∧
      ((createData pid items).run t).run e=.ok (((),v),b) ∧
      keyAt w kid=some k ∧ k.peer=some pid ∧ keyAt t kid=some k := by
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,acquireRun,items,t,e,allocateRun,createRun⟩ := run
  have certificate := acquire compatible a c acquireRun
  obtain ⟨k,before,owner,after⟩ := certificate.key
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (allocate_perimeter packets) u c items t e allocateRun
  have keys : Origins.view t=Origins.view u := congrArg (fun shape=>shape.1) perimeter
  have retained : keyAt t kid=keyAt u kid := by
    simpa [Origins.view,keyAt,Option.bind_map,Function.comp_def] using
      congrArg (fun shape=>shape.bind fun fields=>fields.2 kid) keys
  exact ⟨u,c,items,t,e,k,acquireRun,certificate,allocateRun,createRun,before,owner,
    retained.trans after⟩

end Leanux.Proofs.WG.RetirementSecurity.AdmissionOwner
