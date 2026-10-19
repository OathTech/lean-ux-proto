import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastDecrypt
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastMaintenance
import Leanux.Proofs.WG.Queues.TxLiveWorkers

/-! TX completion leaf frames preserve the historical encryption projection;
freeing packet storage does not restore an alias to pending encryption work. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Tx
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition

theorem get_tx (id : SkbId) : Preserves (Ready past active) (getTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Packets.getTxSkb_current id w v result a b run).1 ▸ before

theorem free_tx (id : SkbId) : Preserves (Ready past active) (freeTxSkb id) :=
  ready_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveWorkers.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveWorkers.free_tx) id)
    (free_packet id)

macro "encryption_past_tx_step" : tactic => `(tactic| first
  | (allocation_release_head getTxSkb; exact get_tx _)
  | (allocation_release_head freeTxSkb; exact free_tx _)
  | encryption_past_handshake_step)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Tx
