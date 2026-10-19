import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerCreationFrames
import Leanux.Proofs.WG.Queues.CreationLoan

/-! Configuration's lookup and strict acquisition retain the actual stamped
owner. Creation publishes one base occurrence before acquiring the separate
caller occurrence; the same holders carry both reference bounds. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders
namespace ConfigurationAcquire

theorem lookup (key : Key) (account : Account holders cs loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w) (a b : Ambient)
    (run : ((pubkeyLookup key).run w).run a=.ok ((some pid,v),b)) :
    ∃ owner : Owner, owner.slot=pid ∧ Account holders cs (owner::loans) v ∧
      BaseCoherence.Inv v ∧ (holders.base.map Owner.slot).Nodup ∧ pid ∈ holders.base.map Owner.slot := by
  obtain ⟨d,p,_,_,_,after⟩ := account.pubkey key a b run
  have selected := BaseCoherence.lookup_selected key coherent configured account.funded.aligned a b run
  exact ⟨⟨d.ifindex,pid,p.internalId⟩,rfl,after,
    BaseCoherence.transport coherent ((ProjectedAction.iff_run_ambient _ _ _).mp
      (BaseCoherence.pubkeyLookup_view key) w a _ v b run),selected.2⟩

theorem acquire_selected (account : Account holders cs loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (selected : owner ∈ holders.base) (a b : Ambient)
    (run : ((peerGet owner.slot).run w).run a=.ok (((),v),b)) :
    Account holders cs (owner::loans) v ∧ BaseCoherence.Inv v ∧ ConfiguredIdentity.Inv v := by
  have member : owner ∈ holders.owners := by
    simp only [owners,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl selected))))
  obtain ⟨p,res⟩ := account.funded.resident member
  obtain ⟨d,hd,epoch,hp,stamp⟩ := resident_fields res
  obtain ⟨actual,q,actualDev,actualPeer,_,after⟩ := account.acquire owner.slot a b run
  have sameDev : actual=d := Option.some.inj (actualDev.symm.trans hd)
  subst actual
  have samePeer : q=p := Option.some.inj (actualPeer.symm.trans hp)
  subst q
  have sameOwner : (⟨d.ifindex,owner.slot,p.internalId⟩ : Owner)=owner := by
    cases owner
    simp_all only
  have structural := CreationLoan.acquire_selected account.funded account.stable
    coherent configured selected a b run
  exact ⟨sameOwner ▸ after,structural.2.2⟩

theorem creation_acquire (key : Key) (psk : Option Key) (account : Account holders cs loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a middle b : Ambient)
    (create : ((peerCreate key psk).run w).run a=.ok ((.ok pid,u),middle))
    (acquire : ((peerGet pid).run u).run
      (CounterWindow.record middle .peerCreateErr false)=.ok (((),v),b)) :
    ∃ d, w.dev=some d ∧ pid=d.nextPeer ∧
      Account (HolderCreation.addBase holders (BaseCreation.owner w d)) cs
        (BaseCreation.owner w d::loans) v ∧ BaseCoherence.Inv v ∧ ConfiguredIdentity.Inv v ∧
      pid ∈ BaseCoherence.slots v := by
  obtain ⟨d,hd,slot,after⟩ := account.peer_create configured key psk create
  have coherentOut := BaseCoherence.creation_preserves key psk coherent account.funded configured a middle create
  have configuredOut := ((hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.peerCreate_spec key psk)
    w a (.ok pid) u middle configured create).1
  have selected : BaseCreation.owner w d ∈ (HolderCreation.addBase holders (BaseCreation.owner w d)).base := by
    simp only [HolderCreation.addBase,List.mem_append,List.mem_singleton]
    exact Or.inr True.intro
  have paySlot : (BaseCreation.owner w d).slot=pid := slot.symm
  have got := acquire_selected after coherentOut configuredOut selected
    (CounterWindow.record middle .peerCreateErr false) b (by simpa only [paySlot] using acquire)
  refine ⟨d,hd,slot,got.1,got.2.1,got.2.2,?_⟩
  unfold BaseCoherence.slots
  rw [←got.1.funded.aligned.base]
  exact List.mem_map.mpr ⟨BaseCreation.owner w d,selected,paySlot⟩

end ConfigurationAcquire
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
