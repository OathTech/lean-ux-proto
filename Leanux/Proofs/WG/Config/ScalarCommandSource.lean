import Leanux.Proofs.WG.Config.ScalarCommandEffects
import Leanux.Proofs.WG.Config.ScalarTailSource
import Leanux.Proofs.WG.Config.QueuedRemoveSource

/-! Same-run existing-target selection and scalar completion of the original public command. The actual lookup supplies the paid caller; arbitrary later attributes and original Stops remain in the source. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarCommand
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open PeerScalarRetention
theorem existing_command_index (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Ensures (setPeerCmd attrs)
      (fun g=>Index.ConfigurationIndex.Entry cs loans g ∧ g.dev=some before)
      (fun ret g=>Index.ConfigurationIndex.Entry cs loans g ∧
        ∃ p,before.peers[pid]?=some p ∧
          view g pid=some (ScalarTail.tailCell attrs ret
            (ScalarTail.prefixCell p attrs.presharedKey attrs.endpoint))) := by
  intro g a result v b pre run
  obtain ⟨p,resident,positive⟩ := QueuedRemove.lookup_target_index cs loans key pid before g pre.1 pre.2 found
  obtain ⟨first,cut⟩ := QueuedRemove.command_lookup_default_cut attrs key pubkey valid protocol
    g v a b result run
  rw [MaterialOrigin.bind_ok_ambient] at cut
  obtain ⟨peer,u,c,looked,tail⟩ := cut
  have selected := ((ensures_iff _ _ _).mpr
    (pubkeyLookup_present key pid before p found resident positive)) g first peer u c pre.2 looked
  obtain ⟨rfl,device⟩ := selected
  have acquired := Index.ConfigurationIndex.lookup cs loans key g first (some pid) u c pre.1 looked
  obtain ⟨paid,slot,entry,member⟩ := acquired
  subst pid
  change ((Configuration.peerConfigUpdateSource attrs (some paid.slot) (attrs.flags.getD 0)
    attrs.presharedKey paid.slot).run u).run
    (CounterWindow.record c .peerNotFound false)=.ok ((result,v),b) at tail
  have stored : (withPeer before paid.slot {p with refcount:=p.refcount+1}).peers[paid.slot]?=
      some {p with refcount:=p.refcount+1} := by simp [withPeer]
  have listed : paid.slot∈(withPeer before paid.slot {p with refcount:=p.refcount+1}).peerList := by
    simpa only [BaseCoherence.slots,device,Option.map_some,Option.getD_some] using member
  have done := ScalarTail.update_exact cs loans paid attrs (attrs.flags.getD 0) attrs.presharedKey
    keep (withPeer before paid.slot {p with refcount:=p.refcount+1})
    {p with refcount:=p.refcount+1} stored listed
    u _ result v b ⟨entry,device⟩ tail
  exact ⟨done.1,p,resident,by simpa only [prefixCell_acquire] using done.2⟩

theorem existing_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Ensures (setPeerCmd attrs)
      (fun g=>OwnerConfiguration.Entry cs loans g ∧ g.dev=some before)
      (fun ret g=>Index.ConfigurationIndex.Entry cs loans g ∧
        ∃ p,before.peers[pid]?=some p ∧
          view g pid=some (ScalarTail.tailCell attrs ret
            (ScalarTail.prefixCell p attrs.presharedKey attrs.endpoint))) := by
  intro g a result v b pre run
  exact existing_command_index cs loans attrs key pid before pubkey valid protocol keep found
    g a result v b ⟨pre.1.1,pre.2⟩ run
end Leanux.Proofs.WG.Config.ScalarCommand
