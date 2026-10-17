import Leanux.Proofs.WG.Queues.BaseCoherence
import Leanux.Proofs.WG.Queues.HandshakeLoans
import Leanux.Proofs.WG.Configuration.PeerSource

/-! Public-key acquisition supplies a transient loan separately from the
selected base occurrence paid by removal. Both are actual source payments. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseLookupRemoval
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

theorem lookup_funded (key : Key) {h : DurableHolders}
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (coherent : BaseCoherence.Inv w)
    (a b : Ambient) (run : ((pubkeyLookup key).run w).run a=.ok ((result,v),b)) :
    HandshakeLoans.FundedResult h cs loans result v ∧ BaseCoherence.Inv v := by
  have frame := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeLoans.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans.pubkey_frame) key w)
    w a result v b (Frame.refl w) run
  have result := HandshakeLoans.pubkeyLookup_result key ⟨hi.carriers,stable⟩ a b run
  exact ⟨(pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeLoans.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans.funded_result)
    hi.aligned frame result,
    BaseCoherence.transport coherent ((ProjectedAction.iff_run_ambient _ _ _).mp
      (BaseCoherence.pubkeyLookup_view key) w a _ v b run)⟩

/-- The actual lookup derives both its paid-for loan and the selected base
occurrence. Identity assumptions do not replace the acquisition. -/
theorem lookup_selected (key : Key) {h : DurableHolders}
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (coherent : BaseCoherence.Inv w)
    (configured : ConfiguredIdentity.Inv w) (a b : Ambient)
    (run : ((pubkeyLookup key).run w).run a=.ok ((some pid,v),b)) :
    ∃ o : Owner, o.slot=pid ∧ h.Funded cs (o::loans) v ∧ StableRx cs v ∧
      BaseCoherence.Inv v ∧ (h.base.map Owner.slot).Nodup ∧ pid ∈ h.base.map Owner.slot := by
  obtain ⟨funded,coherentOut⟩ := lookup_funded key hi stable coherent a b run
  obtain ⟨o,slot,funded,stable⟩ := funded
  have selected := BaseCoherence.lookup_selected key coherent configured hi.aligned a b run
  exact ⟨o,slot,funded,stable,coherentOut,selected.2⟩

/-- The original removal branch pays the base reference in peerRemove and
its separate acquired caller loan in the final out path. -/
theorem update_remove (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key) (o : Owner)
    {h : DurableHolders} (hi : h.Funded cs (o::loans) w) (stable : StableRx cs w)
    (unique : (h.base.map Owner.slot).Nodup) (selected : o.slot ∈ h.base.map Owner.slot)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=true) (a b : Ambient)
    (run : ((Configuration.peerConfigUpdateSource attrs (some o.slot) flags psk o.slot).run w).run a=.ok ((result,v),b)) :
    result=0 ∧ DuringWork (h.withoutBase (BaseRemoval.live h.base o.slot)) cs loans v := by
  simp only [Configuration.peerConfigUpdateSource,remove] at run
  change ((do peerRemove (some o.slot)
              peerPut (some o.slot)
              _ ← branch .peerZeroPsk attrs.presharedKey.isSome
              pure (0 : Int) : WG.M Int).run w).run
    (CounterWindow.record a .peerRemoveMe true)=.ok ((result,v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨x,u,c,removed,tail⟩ := run
  cases x
  have kept := peerRemove_some_funded o.slot hi stable unique selected _ c removed
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨x,z,d,paid,done⟩ := tail
  cases x
  have funded := work_payment_normal kept c d paid
  change Except.ok ((0,z),CounterWindow.record d .peerZeroPsk attrs.presharedKey.isSome)=.ok ((result,v),b) at done
  cases done
  exact ⟨rfl,funded⟩

/-- Join actual lookup and actual acquired-peer removal at the returned
World/Ambient cut. No intermediate funding or successful-cleanup premise is
substituted for either normal execution. -/
theorem lookup_update_remove (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    {h : DurableHolders} (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=true) (a middle b : Ambient)
    (lookup : ((pubkeyLookup key).run w).run a=.ok ((some pid,u),middle))
    (update : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle=.ok ((result,v),b)) :
    result=0 ∧ DuringWork (h.withoutBase (BaseRemoval.live h.base pid)) cs loans v := by
  obtain ⟨o,slot,funded,stable,_,unique,selected⟩ := lookup_selected key hi stable coherent configured a middle lookup
  subst pid
  exact update_remove attrs flags psk o funded stable unique selected remove middle b update

end Leanux.Proofs.WG.Queues.RxCredits.BaseLookupRemoval
