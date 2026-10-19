import Leanux.Proofs.WG.RetirementSecurity.HolderRemoval

/-! Native single-peer and acquired configuration removal consume different
peer occurrences. The successful source lookup supplies the caller loan and
selects the base occurrence; neither payment discards remaining key credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem SlotPeerReferences.device (before : SlotPeerReferences holders loans w)
    (same : v.dev = w.dev) : SlotPeerReferences holders loans v := by
  intro d pid p device stored slots
  exact before d pid p (same.symm.trans device) stored slots

theorem SlotAnchors.pubkey (key : Key) :
    Preserves (SlotPeerReferences holders loans) (pubkeyLookup key) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.pubkeyLookup_borrowed_spec key (wgStoreView w)) w a result v b rfl run
  cases result with
  | none => exact before.device (congrArg WGStoreView.dev borrowed)
  | some pid =>
    obtain ⟨d,p,device,stored,_,output⟩ := borrowed
    have ready := before.replace device stored (q := {p with refcount := p.refcount + 1}) rfl (fun h => h)
    exact ready.device (congrArg WGStoreView.dev output)

namespace HolderRemoval

theorem some_peer (keys : HolderAccount temporary w)
    (peers : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (pid : PeerId)
    (unique : (holders.base.map Owner.slot).Nodup)
    (selected : pid ∈ holders.base.map Owner.slot) (a b : Ambient)
    (run : ((peerRemove (some pid)).run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready (holders.withoutBase (BaseRemoval.live holders.base pid))
      carriers loans temporary v ∧ SlotsCleared pid v := by
  obtain ⟨o,slot,one⟩ := unique_detached holders.base pid unique selected
  change ((peerMakeDead pid >>= fun _ => peerRemoveAfterDead pid).run w).run
    (CounterWindow.record a .peerRemoveNull false) = .ok (((),v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,marked,c,mark,payment⟩ := run
  cases ignored
  obtain ⟨keys,peers,stable,anchors⟩ := make_dead_accounts keys peers stable anchors pid _ c mark
  rw [one,List.singleton_append] at peers anchors
  have done := after_dead (HolderDrain.initial keys peers stable anchors) c b
    (by simpa only [slot] using payment)
  simpa only [slot] using done

theorem update_remove (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key) (o : Owner)
    (keys : HolderAccount temporary w) (peers : holders.Funded carriers (o :: loans) w)
    (stable : StableRx carriers w) (anchors : SlotPeerReferences holders (o :: loans) w)
    (unique : (holders.base.map Owner.slot).Nodup)
    (selected : o.slot ∈ holders.base.map Owner.slot)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0) = true) (a b : Ambient)
    (run : ((Configuration.peerConfigUpdateSource attrs (some o.slot) flags psk o.slot).run w).run a =
      .ok ((result,v),b)) :
    result = 0 ∧ HolderDrain.Ready (holders.withoutBase (BaseRemoval.live holders.base o.slot))
      carriers loans temporary v := by
  simp only [Configuration.peerConfigUpdateSource,remove] at run
  change ((do peerRemove (some o.slot)
              peerPut (some o.slot)
              _ ← branch .peerZeroPsk attrs.presharedKey.isSome
              pure (0 : Int) : WG.M Int).run w).run
    (CounterWindow.record a .peerRemoveMe true) = .ok ((result,v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,u,c,removed,tail⟩ := run
  cases ignored
  obtain ⟨ready,cleared⟩ := some_peer keys peers stable anchors o.slot unique selected _ c removed
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨ignored,z,d,paid,done⟩ := tail
  cases ignored
  have keyAccount := ready.2.1.peer_put (fun p found _ => cleared p found) c d paid
  have peerAccount := work_payment_normal ready.1 c d paid
  have clearedAfter := (hoare_iff_run_ambient _ _ _).mp (peerPut_slots o.slot (some o.slot))
    u c () z d cleared paid
  have anchorAccount := (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.peer_put (some o.slot))
    u c () z d ready.2.2 paid
  change Except.ok ((0,z),CounterWindow.record d .peerZeroPsk attrs.presharedKey.isSome) =
    .ok ((result,v),b) at done
  cases done
  exact ⟨rfl,peerAccount,keyAccount,anchorAccount.drop_cleared clearedAfter⟩

/-- The actual successful public-key lookup selects the unique base occurrence
and acquires its separate caller reference. The native removal branch pays
both while preserving exact credit for all surviving key holders. -/
theorem lookup_update_remove (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (keys : HolderAccount temporary w) (peers : holders.Funded carriers loans w)
    (stable : StableRx carriers w) (anchors : SlotPeerReferences holders loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0) = true) (a middle b : Ambient)
    (lookup : ((pubkeyLookup key).run w).run a = .ok ((some pid,u),middle))
    (update : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle =
      .ok ((result,v),b)) :
    result = 0 ∧ HolderDrain.Ready (holders.withoutBase (BaseRemoval.live holders.base pid))
      carriers loans temporary v := by
  obtain ⟨o,slot,peersAfter,stableAfter,_,unique,selected⟩ :=
    BaseLookupRemoval.lookup_selected key peers stable coherent configured a middle lookup
  have keysAfter := keys.points ((ProjectedAction.iff_run_ambient _ _ _).mp
    (HolderConsume.pubkey_points key) w a (some pid) u middle lookup)
  have anchorsAfter := (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.pubkey key)
    w a (some pid) u middle anchors lookup
  have additional : SlotPeerReferences holders (o :: loans) u := by
    intro d q p device stored slots
    have member := anchorsAfter d q p device stored slots
    simp only [List.mem_append,List.mem_cons] at member ⊢
    exact member.imp_right Or.inr
  subst pid
  exact update_remove attrs flags psk o keysAfter peersAfter stableAfter additional unique selected remove middle b update

end HolderRemoval
end Leanux.Proofs.WG.RetirementSecurity
