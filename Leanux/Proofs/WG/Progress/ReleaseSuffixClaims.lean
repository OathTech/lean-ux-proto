import Leanux.Proofs.WG.Progress.RxPrimitiveSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-return suffix guarantees for release, confirmation and replay validation. No residency, non-null or bitmap-validity input premise is supplied. Conclusions concern normal returns; malformed inputs retain their original Stops. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem peerPut_record_suffix (records : List HiddenRecord) (peer : Option PeerId) :
    Campaign2.Ensures (peerPut peer)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (peerPut_retains records peer g) a (value,after) b
    (pre ▸ tail_self records) run

theorem keypairPut_record_suffix (records : List HiddenRecord) (key : Option KeypairId) (now : Bool) :
    Campaign2.Ensures (keypairPut key now)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (keypairPut_retains records key now g) a (value,after) b
    (pre ▸ tail_self records) run

theorem confirmation_record_suffix (records : List HiddenRecord) (pid : PeerId) (kid : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid kid)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (confirmation_retains records pid kid g) a (value,after) b
    (pre ▸ tail_self records) run

theorem counterValidate_record_suffix (records : List HiddenRecord) (kid : KeypairId) (nonce : Nat) :
    Campaign2.Ensures (counterValidate kid nonce)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (counterValidate_retains records kid nonce g) a (value,after) b
    (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
