import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastStagingFrames

/-! All native sending admissions retain historical packet-identity exclusion.
The proof uses the original validity, age, nonce-limit and queue-refusal arms. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TxDisposition RxCredits
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem submit_ready (pid kid : Nat) (packets : List DataPacket) :
    Preserves (Ready past active) (RxCredits.stagedSubmit pid kid packets) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact staged_submit pid kid packets before.1 before.2 a b run

theorem key_source (pid kid : Nat) (packets : List WG.Packet) :
    Preserves (Ready past active) (stagedKeySource pid kid packets) := by
  let P := Ready past active
  have getter := ready_read_key (past := past) (active := active) kid
  have setter := ready_set_key (past := past) (active := active)
  have expired (date : Int64) : Preserves P (branchExpired .stagedBirthdateExpired date REJECT_AFTER_TIME) :=
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn (pkt : WG.Packet) : Preserves P (ipTunnelEcnEncap pkt) :=
    (ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out := ready_no_key (past := past) (active := active) pid packets (some kid)
  have submit := submit_ready (past := past) (active := active) pid kid
  have loop {α β : Type} (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs init f) :=
    list_view_spec id P xs init f hf
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  rxstack_preserves_source [stagedKeySource,branch,branchCmp]
    using [getter,setter,expired,ecn,out,submit,loop,ambient]

/-- Native staged send preserves exclusion of every historical encryption
identity from pending work, including no-key and refusal paths. -/
theorem send (pid : PeerId) : Preserves (Ready past active) (sendStagedPackets pid) := by
  let P := Ready past active
  have read (id : PeerId) : Preserves P (getPeer id) := getPeer_preserves _ _
  have write := ready_set_peer (past := past) (active := active)
  have key := ready_get_key (past := past) (active := active)
  have out := ready_no_key (past := past) (active := active)
  have source := key_source (past := past) (active := active)
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  rw [← stagedFullSource_eq]
  rxstack_preserves_source [stagedFullSource,branch,invariant] using [read,write,key,out,source,ambient]

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
