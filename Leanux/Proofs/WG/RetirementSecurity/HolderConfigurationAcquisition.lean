import Leanux.Proofs.WG.RetirementSecurity.HolderConfigurationUpdate
import Leanux.Proofs.WG.RetirementSecurity.SlotAnchorConsumers
import Leanux.Proofs.WG.Queues.CreationLoan

/-! Actual lookup and creation supply the two distinct peer occurrences used
by configuration. Every component is obtained from the original native cuts;
the key account is retained independently of the peer-reference ledger. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

def Entry (temporary : Credits.Ledger) (carriers : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  HolderKeepalive.Ready temporary w ∧
  (∃holders,holders.Funded carriers loans w ∧ StableRx carriers w ∧ SlotPeerReferences holders loans w) ∧
  BaseCoherence.Inv w ∧ ConfiguredIdentity.Inv w

def Acquired (temporary : Credits.Ledger) (carriers : Ledger) (loans : Reservations)
    (peer : Option PeerId) (w : WGWorld) : Prop :=
  match peer with
  | none => Entry temporary carriers loans w
  | some pid => HolderKeepalive.Selected temporary pid w ∧
      ∃holders o,o.slot=pid ∧ holders.Funded carriers (o::loans) w ∧ StableRx carriers w ∧
        SlotPeerReferences holders (o::loans) w ∧ (holders.base.map Owner.slot).Nodup ∧
        pid ∈ holders.base.map Owner.slot

theorem anchors_extend (before : SlotPeerReferences holders loans w) (o : Owner) :
    SlotPeerReferences holders (o::loans) w := by
  intro d pid p device stored slots
  have member := before d pid p device stored slots
  simp only [List.mem_append,List.mem_cons] at member ⊢
  exact member.imp_right Or.inr

theorem lookup (key : Key) : Hoare (pubkeyLookup key)
    (Entry temporary carriers loans) (Acquired temporary carriers loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨ready,⟨holders,funded,stable,anchors⟩,coherent,configured⟩ := before
  have own := (hoare_iff_run_ambient _ _ _).mp (HolderConsume.pubkey key) w a result v b ready.1 run
  have allocation := Allocated.native (pubkeyLookupPrefix_erases key)
    (pubkeyLookupPrefix_preserves_ambient allocationAmbient key) ready.2.1 a b run
  have slots := (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.Configuration.pubkey_preserves key)
    w a result v b ready.2.2 run
  have anchors := (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.pubkey_lookup key) w a result v b anchors run
  cases result with
  | none =>
    obtain ⟨⟨funded,stable⟩,coherent⟩ := BaseLookupRemoval.lookup_funded key funded stable coherent a b run
    have identity := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ConfiguredReceive.pubkeyLookup_view key) w a none v b run
    exact ⟨⟨own.1,allocation,slots⟩,⟨holders,funded,stable,anchors⟩,coherent,
      fun s hs=>configured s (identity ▸ hs)⟩
  | some pid =>
    obtain ⟨o,slot,funded,stable,_,unique,selected⟩ :=
      BaseLookupRemoval.lookup_selected key funded stable coherent configured a b run
    exact ⟨⟨⟨own.1,allocation,slots⟩,own.2 pid rfl⟩,
      holders,o,slot,funded,stable,anchors_extend anchors o,unique,selected⟩

theorem update_acquired (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Hoare (Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid)
      (Acquired temporary carriers loans (some pid)) (fun _=>HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨ready,holders,o,slot,funded,stable,anchors,unique,selected⟩ := before
  subst pid
  cases remove : (flags &&& WGPEER_F_REMOVE_ME != 0) with
  | false =>
    exact (hoare_iff_run_ambient _ _ _).mp (ordinary attrs o flags psk remove) w a result v b ready run
  | true =>
    exact (HolderRemoval.update_remove attrs flags psk o ready.1.1 funded stable anchors
      unique selected remove a b run).2.2.1

theorem strict_ready (pid : PeerId) : Hoare (peerGet pid) (HolderKeepalive.Ready temporary)
    (fun _=>HolderKeepalive.Selected temporary pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  obtain ⟨d,p,device,stored,positive,after⟩ := peerGet_loan pid w v a b run
  have output : v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} :=
    congrArg WGStoreView.dev after
  refine ⟨⟨before.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_ownership pid) w a () v b run),
    Allocated.native (peerGetMixed_erases pid) (allocationAmbient.peerGet pid) before.2.1 a b run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.fields_preserves (project:=id) (CurrentSlots.peerGet_fields pid))
      w a () v b before.2.2 run⟩,?_⟩
  simpa [HolderConsume.Strong,peerView,output] using (show 1<p.refcount+1 by omega)

theorem strict_anchors (pid : PeerId) : Preserves (SlotPeerReferences holders loans) (peerGet pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  obtain ⟨d,p,device,stored,_,after⟩ := peerGet_loan pid w v a b run
  apply (before.replace device stored (q:={p with refcount:=p.refcount+1}) rfl (fun h=>h)).device
  exact congrArg WGStoreView.dev after

theorem creation_ready (key : Key) (psk : Option Key) (before : HolderKeepalive.Ready temporary w)
    (configured : ConfiguredIdentity.Inv w) (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a=.ok ((result,v),b)) : HolderKeepalive.Ready temporary v :=
  ⟨HolderPeerCreation.keys key psk before.1 configured a b run,
    Allocated.native (peerCreateMixed_erases key psk) (peerCreateMixed_preserves key psk) before.2.1 a b run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.peerCreate_preserves key psk) w a result v b before.2.2 run⟩

theorem creation_acquired (key : Key) (psk : Option Key) (before : Entry temporary carriers loans w)
    (a middle b : Ambient)
    (create : ((peerCreate key psk).run w).run a=.ok ((.ok pid,u),middle))
    (acquire : ((peerGet pid).run u).run (CounterWindow.record middle .peerCreateErr false)=.ok (((),v),b)) :
    Acquired temporary carriers loans (some pid) v := by
  obtain ⟨ready,⟨holders,funded,stable,anchors⟩,coherent,configured⟩ := before
  have ready := creation_ready key psk ready configured a middle create
  have selectedReady := (hoare_iff_run_ambient _ _ _).mp (strict_ready pid) u _ () v b ready acquire
  obtain ⟨d,_,slot,funded,stable,coherent,_,member⟩ :=
    CreationLoan.creation_acquire key psk funded stable coherent configured a middle b create acquire
  have anchors := HolderPeerCreation.slots key psk anchors a middle create
  have anchors := (hoare_iff_run_ambient _ _ _).mp (strict_anchors pid) u _ () v b anchors acquire
  let after := HolderCreation.addBase holders (BaseCreation.owner w d)
  refine ⟨selectedReady,after,BaseCreation.owner w d,slot.symm,funded,stable,?_,
    BaseCoherence.holder_unique coherent funded.aligned,?_⟩
  · intro e other p device stored slots
    have old := anchors e other p device stored slots
    rcases List.mem_append.mp old with base | loan
    · exact List.mem_append_left _ (List.mem_append_left _ base)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ loan)
  · simpa only [BaseCoherence.slots,←funded.aligned.base] using member

end Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
