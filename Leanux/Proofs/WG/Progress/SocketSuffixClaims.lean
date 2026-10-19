import Leanux.Proofs.WG.Progress.SocketSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-result suffix claims for original socket sends. These do not
assert normal return or strict record consumption. Routing and loopback contracts
are concrete, with no successful-call or callback hypothesis. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Noise

/-- Normal IPv6 sends leave a suffix of the supplied hidden records. This neither
asserts a normal return nor requires positive record consumption. -/
theorem send6_record_suffix (records : List HiddenRecord)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Campaign2.Ensures (send6 e cache bytes ds exactRx)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (send6_retains records e cache bytes ds exactRx g)
    a (value,after) b (pre ▸ tail_self records) run

theorem send6_product_record_suffix (records : List HiddenRecord)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Campaign2.Product.Ensures (liftWG (send6 e cache bytes ds exactRx))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp
    (native_product records _ (send6_retains records e cache bytes ds exactRx))
    w value after (pre ▸ tail_self records) run


theorem send4_record_suffix (records : List HiddenRecord)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Campaign2.Ensures (send4 e cache bytes ds exactRx)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (send4_retains records e cache bytes ds exactRx g)
    a (value,after) b (pre ▸ tail_self records) run

theorem sendSkbToPeer_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Campaign2.Ensures (sendSkbToPeer pid bytes ds)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (sendSkbToPeer_retains records pid bytes ds g)
    a (value,after) b (pre ▸ tail_self records) run

theorem sendBufferToPeer_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (bytes : List UInt8) :
    Campaign2.Ensures (sendBufferToPeer pid bytes)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (sendBufferToPeer_retains records pid bytes g)
    a (value,after) b (pre ▸ tail_self records) run

theorem sendBufferAsReplyToSkb_record_suffix (records : List HiddenRecord)
    (src : SkbSource) (bytes : List UInt8) :
    Campaign2.Ensures (sendBufferAsReplyToSkb src bytes)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (sendBufferAsReplyToSkb_retains records src bytes g)
    a (value,after) b (pre ▸ tail_self records) run
end Leanux.Proofs.WG.Progress.RecordSuffix
