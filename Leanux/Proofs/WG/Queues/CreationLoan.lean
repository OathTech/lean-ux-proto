import Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration
import Leanux.Proofs.WG.Queues.HolderDecrypt

/-! Actual strict acquisition adds a caller reservation to the complete holder
account. Creation has already funded its distinct base occurrence; the source
peerGet then funds the additional loan, with the same stamped owner. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.CreationLoan
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders
variable {h : DurableHolders} {cs : Ledger} {loans : Reservations}
  {w u v : WGWorld} {pid : PeerId} {o : Owner}

theorem peerGet_configured_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (peerGet pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  obtain ⟨d,p,hd,hp,_,out⟩ := peerGet_loan pid w v a b run
  change (wgStoreView v).dev.map ConfiguredIdentity.state =
    (wgStoreView w).dev.map ConfiguredIdentity.state
  simp only [out,hd,Option.map_some]
  exact congrArg some (ConfiguredIdentity.state_peer_same d pid p
    {p with refcount:=p.refcount+1} hp rfl)

/-- This is the actual peerGet loan, charged alongside every durable holder
and caller loan. Its epoch and stamp come from that execution's resident. -/
theorem acquire_funded (funded : h.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient) (run : ((peerGet pid).run w).run a=.ok (((),v),b)) :
    ∃ d p, w.dev=some d ∧ d.peers[pid]?=some p ∧ 0<p.refcount ∧
      h.Funded cs (⟨d.ifindex,pid,p.internalId⟩::loans) v ∧ StableRx cs v ∧
      BaseCoherence.Inv v ∧ ConfiguredIdentity.Inv v := by
  obtain ⟨d,p,hd,hp,pos,carrier,stableOut⟩ :=
    ClearWork.acquire ⟨funded.carriers,stable⟩ a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderDecrypt.peerGet_frame pid w)
    w a () v b (Frame.refl w) run
  have base := (ProjectedAction.iff_run_ambient _ _ _).mp
    (BaseCoherence.peerGet_view pid) w a () v b run
  have identity := (ProjectedAction.iff_run_ambient _ _ _).mp
    (peerGet_configured_view pid) w a () v b run
  refine ⟨d,p,hd,hp,pos,⟨funded.aligned.frame frame,
    WorkReservations.carrier_loans_perm carrier List.perm_middle.symm⟩,
    stableOut,BaseCoherence.transport coherent base,?_⟩
  intro s hs
  exact configured s (identity ▸ hs)

/-- If the base occurrence is already source-funded, actual peerGet acquires
another charge to precisely that owner. Membership alone supplies no credit. -/
theorem acquire_selected (funded : h.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (selected : o ∈ h.base) (a b : Ambient)
    (run : ((peerGet o.slot).run w).run a=.ok (((),v),b)) :
    h.Funded cs (o::loans) v ∧ StableRx cs v ∧
      BaseCoherence.Inv v ∧ ConfiguredIdentity.Inv v := by
  have member : o ∈ h.owners := by
    simp only [owners,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl selected))))
  obtain ⟨p,res⟩ := funded.resident member
  obtain ⟨d,hd,epoch,hp,stamp⟩ := resident_fields res
  obtain ⟨actual,q,actualDev,actualPeer,_,after,stableOut,coherentOut,configuredOut⟩ :=
    acquire_funded funded stable coherent configured a b run
  have sameDev : actual=d := Option.some.inj (actualDev.symm.trans hd)
  subst actual
  have samePeer : q=p := Option.some.inj (actualPeer.symm.trans hp)
  subst q
  have sameOwner : (⟨d.ifindex,o.slot,p.internalId⟩ : Owner)=o := by
    cases o
    simp_all only
  exact ⟨sameOwner ▸ after,stableOut,coherentOut,configuredOut⟩

/-- Both ordinary errno and success outcomes preserve structural coherence and
configured identity while retaining the exact creation funding alternatives. -/
theorem creation (key : Key) (psk : Option Key)
    (funded : h.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a=.ok ((result,v),b)) :
    BaseCoherence.Inv v ∧ ConfiguredIdentity.Inv v ∧
      match result with
      | .error _ => h.Funded cs loans v ∧ StableRx cs v
      | .ok pid => ∃ d, w.dev=some d ∧ pid=d.nextPeer ∧
          (HolderCreation.addBase h (BaseCreation.owner w d)).Funded cs loans v ∧
          StableRx cs v := by
  exact ⟨BaseCoherence.creation_preserves key psk coherent funded configured a b run,
    ((hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.peerCreate_spec key psk)
      w a result v b configured run).1,
    HolderCreation.peerCreate_funded key psk funded stable configured a b run⟩

/-- The actual successful creation and following recorded strict acquisition
fund two occurrences of the same owner: the published base and caller loan.
All other holders and loans remain in the single combined account. -/
theorem creation_acquire (key : Key) (psk : Option Key)
    (funded : h.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a middle b : Ambient)
    (create : ((peerCreate key psk).run w).run a=.ok ((.ok pid,u),middle))
    (acquire : ((peerGet pid).run u).run
      (CounterWindow.record middle .peerCreateErr false)=.ok (((),v),b)) :
    ∃ d, w.dev=some d ∧ pid=d.nextPeer ∧
      (HolderCreation.addBase h (BaseCreation.owner w d)).Funded
        cs (BaseCreation.owner w d::loans) v ∧ StableRx cs v ∧
      BaseCoherence.Inv v ∧ ConfiguredIdentity.Inv v ∧
      pid ∈ BaseCoherence.slots v := by
  obtain ⟨coherentOut,configuredOut,d,hd,slot,fundedOut,stableOut⟩ :=
    creation key psk funded stable coherent configured a middle create
  have selected : BaseCreation.owner w d ∈ (HolderCreation.addBase h (BaseCreation.owner w d)).base := by
    simp only [HolderCreation.addBase,List.mem_append,List.mem_singleton]
    exact Or.inr True.intro
  have paySlot : (BaseCreation.owner w d).slot=pid := slot.symm
  have got := acquire_selected fundedOut stableOut coherentOut configuredOut selected
    (CounterWindow.record middle .peerCreateErr false) b (by simpa only [paySlot] using acquire)
  refine ⟨d,hd,slot,got.1,got.2.1,got.2.2.1,got.2.2.2,?_⟩
  unfold BaseCoherence.slots
  rw [←got.1.aligned.base]
  exact List.mem_map.mpr ⟨BaseCreation.owner w d,selected,paySlot⟩

end Leanux.Proofs.WG.Queues.RxCredits.CreationLoan
