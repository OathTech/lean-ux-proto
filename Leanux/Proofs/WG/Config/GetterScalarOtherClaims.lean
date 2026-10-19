import Leanux.Proofs.WG.Config.GetterScalarOtherSource

/-! Projected normal original-command contracts. Arbitrary mixed attributes are classified from actual validation and table selection. No totality or stopped-state scalar claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar.Other
open Leanux Leanux.WG Noise Queues Queues.RxCredits

theorem original_update (selected : PeerId) (entry : Campaign2.Snapshot)
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) :
    Campaign2.Ensures
      (Configuration.peerConfigUpdateSource attrs peer flags psk selected)
      (Keeps selected entry) (fun _=>Keeps selected entry) :=
  (ensures_iff _ _ _).mpr
    (update selected (GetterScalar.observation entry) attrs peer flags psk)

theorem original_existing_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>Index.View.ConfigurationInput cs loans s ∧ s.wg.device=some before)
      (fun _ s=>ExceptAt pid (GetterScalar.values (some before)) (GetterScalar.observation s)) := by
  intro g a result final b pre run
  exact existing_command cs loans attrs key pid before pubkey valid protocol found
    g a result final b ⟨(Index.configurationInput_snapshot cs loans g a).mp pre.1,pre.2⟩ run

theorem original_missing_command (attrs : PeerAttrs) (key : Key) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (missing : before.peerHashtable.find? (·.1 == key)=none) :
    Campaign2.Ensures (setPeerCmd attrs) (fun s=>s.wg.device=some before)
      (fun _ s=>ExceptAt before.nextPeer (GetterScalar.values (some before))
        (GetterScalar.observation s)) :=
  missing_command attrs key before pubkey valid protocol missing

theorem original_existing_remove (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid))
    (remove : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME ≠ 0) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>Index.View.ConfigurationInput cs loans s ∧ s.wg.device=some before)
      (fun _ s=>∀pid value,GetterScalar.observation s pid=some value →
        GetterScalar.values (some before) pid=some value) := by
  intro g a result final b pre run
  exact existing_remove_command cs loans attrs key pid before pubkey valid protocol found remove
    g a result final b ⟨(Index.configurationInput_snapshot cs loans g a).mp pre.1,pre.2⟩ run

theorem original_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (before : Device) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>Index.View.ConfigurationInput cs loans s ∧ s.wg.device=some before)
      (fun _ s=>CommandEffect attrs before (GetterScalar.observation s)) := by
  intro g a ret final b pre run
  exact command cs loans attrs before g a ret final b
    ⟨(Index.configurationInput_snapshot cs loans g a).mp pre.1,pre.2⟩ run

end Leanux.Proofs.WG.Config.GetterScalar.Other
