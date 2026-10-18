import Leanux.Proofs.WG.Index.ConfigurationIndexModel
import Leanux.Proofs.WG.Index.LookupCoreSource
import Leanux.Proofs.WG.Index.RetirementSinglePeerSource
import Leanux.Proofs.WG.Index.PeerRemovalClaims
import Leanux.Proofs.WG.Queues.SlotDevice
import Leanux.Proofs.WG.Queues.BaseLookupRemoval

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem lookup (cs : Ledger) (loans : Reservations) (key : Key) :
    Ensures (pubkeyLookup key) (Entry cs loans) (Acquired cs loans) := by
  intro w a result v b pre run
  have core := (pubkeyLookup_indexCore_held key w a result v b pre.2.2 run).1
  have slots := (hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.Configuration.pubkey_preserves key) w a result v b pre.2.1 run
  have identity := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ConfiguredReceive.pubkeyLookup_view key) w a result v b run
  have configured : ConfiguredIdentity.Inv v := fun s hs => pre.1.2.2 s (identity ▸ hs)
  obtain ⟨holders,funded,stable⟩ := pre.1.1
  cases result with
  | none =>
    obtain ⟨⟨fundedOut,stableOut⟩,base⟩ :=
      BaseLookupRemoval.lookup_funded key funded stable pre.1.2.1 a b run
    exact ⟨⟨⟨holders,fundedOut,stableOut⟩,base,configured⟩,slots,core⟩
  | some pid =>
    obtain ⟨paid,selected,fundedOut,stableOut,base,_,member⟩ :=
      BaseLookupRemoval.lookup_selected key funded stable pre.1.2.1 pre.1.2.2 a b run
    refine ⟨paid,selected,⟨⟨⟨holders,fundedOut,stableOut⟩,base,configured⟩,slots,core⟩,?_⟩
    unfold BaseCoherence.slots
    rw [←fundedOut.aligned.base]
    exact member

theorem remove_selected (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Ensures (peerRemove (some pid))
      (fun w => Entry cs loans w ∧ pid ∈ BaseCoherence.slots w)
      (fun _ => Entry cs loans) := by
  intro w a result v b pre run
  obtain ⟨holders,funded,stable⟩ := pre.1.1.1
  have selected : pid ∈ holders.base.map Owner.slot := by
    rw [funded.aligned.base]
    exact pre.2
  have removed := peerRemove_some_retirement holders cs [] loans pid selected
    w a result v b
      ⟨pre.1.1.2.2,pre.1.1.2.1,funded,stable,
        fun d hd => (pre.1.2.2 d hd).2.1,
        fun d hd => (pre.1.2.2 d hd).2.2.1,
        fun d hd => (pre.1.2.2 d hd).2.2.2⟩ run
  have tables := peerRemove_tables (some pid) w a result v b
    (fun d hd => (pre.1.2.2 d hd).1) run
  have slots := (hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.Removal.remove (some pid)) w a result v b pre.1.2.1 run
  obtain ⟨remaining,_,fundedOut,stableOut⟩ := removed.account
  exact ⟨⟨⟨remaining,fundedOut,stableOut⟩,removed.base,removed.configured⟩,slots,
    fun d hd => ⟨tables d hd,removed.covered d hd,removed.coherent d hd,removed.reserved d hd⟩⟩

theorem pay (cs : Ledger) (loans : Reservations) (paid : Owner) :
    Ensures (peerPut (some paid.slot)) (Entry cs (paid::loans))
      (fun _ => Entry cs loans) := by
  intro w a result v b pre run
  have paidEntry := Reached.peerPut_boundary_core cs paid loans
    w a result v b ⟨pre.1,pre.2.2⟩ run
  have slots := (hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.peerPut_preserves (some paid.slot)) w a result v b pre.2.1 run
  exact ⟨paidEntry.1,slots,paidEntry.2⟩

theorem keyConflict (cs : Ledger) (loans : Reservations) (key : Key) :
    Ensures (do
      let peer ← pubkeyLookup key
      if ← branch .setDevOldPeer peer.isSome then
        peerPut peer
        peerRemove peer : WG.M Unit)
      (Entry cs loans) (fun _ => Entry cs loans) := by
  intro w a result v b pre run
  cases result
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,looked,tail⟩ := run
  have acquired := lookup cs loans key w a peer u c pre looked
  cases peer with
  | none =>
    change Except.ok (((),u),CounterWindow.record c .setDevOldPeer false)=
      .ok (((),v),b) at tail
    cases tail
    exact acquired
  | some pid =>
    obtain ⟨paid,selected,entry,member⟩ := acquired
    subst pid
    change ((peerPut (some paid.slot) >>= fun _ => peerRemove (some paid.slot)).run u).run
      (CounterWindow.record c .setDevOldPeer true)=.ok (((),v),b) at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,z,d,payment,removed⟩ := tail
    cases ignored
    have afterPay := pay cs loans paid u _ () z d entry payment
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (BaseCoherence.peerPut_view (some paid.slot)) u _ () z d payment
    have memberAfter : paid.slot ∈ BaseCoherence.slots z := by
      rw [show BaseCoherence.slots z = BaseCoherence.slots u from congrArg Prod.fst same]
      exact member
    exact remove_selected cs loans paid.slot z d () v b ⟨afterPay,memberAfter⟩ removed

theorem removeMe (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=true) :
    Ensures (peerConfigUpdateSource attrs (some paid.slot) flags psk paid.slot)
      (fun w => Entry cs (paid::loans) w ∧ paid.slot ∈ BaseCoherence.slots w)
      (fun result w => result=0 ∧ Entry cs loans w) := by
  intro w a result v b pre run
  simp only [peerConfigUpdateSource,remove] at run
  change ((do peerRemove (some paid.slot)
              peerPut (some paid.slot)
              _ ← branch .peerZeroPsk attrs.presharedKey.isSome
              pure (0 : Int) : WG.M Int).run w).run
    (CounterWindow.record a .peerRemoveMe true)=.ok ((result,v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,u,c,removed,tail⟩ := run
  cases ignored
  have removedEntry := remove_selected cs (paid::loans) paid.slot
    w _ () u c pre removed
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨ignored,z,d,payment,done⟩ := tail
  cases ignored
  have paidEntry := pay cs loans paid u c () z d removedEntry payment
  change Except.ok ((0,z),CounterWindow.record d .peerZeroPsk attrs.presharedKey.isSome)=
    .ok ((result,v),b) at done
  cases done
  exact ⟨rfl,paidEntry⟩

end Leanux.Proofs.WG.Index.ConfigurationIndex
