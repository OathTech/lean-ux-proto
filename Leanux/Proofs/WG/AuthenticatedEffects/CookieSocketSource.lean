import Leanux.Proofs.WG.AuthenticatedEffects.CookieEmissionObservation
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerParametric
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase

/-! Embed the existing actual cookie-emission observer in the final journal.
The MAC/load witness is metadata until the native caller proves qualification;
it is distinct from an authenticated handshake or transport root. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CookieSocket
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Receipt where
  mac : HandshakeMac
  input : List UInt8
  source : SkbSource
  datagram : DatagramReceipt

def Receipt.Valid (receipt : Receipt) : Prop :=
  receipt.datagram.Valid ∧ receipt.datagram.endpoint.addr = receipt.source.saddr ∧
    receipt.datagram.endpoint.port = receipt.source.sport ∧
    receipt.datagram.bytes.length = 64 ∧ receipt.datagram.ds = 0

def Receipt.Qualifying (receipt : Receipt) : Prop :=
  receipt.mac.input = receipt.input ∧ receipt.mac.source = receipt.source ∧
    receipt.mac.loaded = true ∧ receipt.mac.checked.value = .noCookie ∧
    receipt.mac.checked.Valid (cookieValidatePacket receipt.input receipt.source true)

def observed (record : Receipt → E) (mac : HandshakeMac)
    (msg : List UInt8) (src : SkbSource) : WGPrefix E Unit :=
  focusStatePrefix (fun datagram => record ⟨mac,msg,src,datagram⟩)
    (fun _ => none) (cookieEmitted msg src)

theorem observed_erases (record : Receipt → E) (mac : HandshakeMac)
    (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (observed record mac msg src) (sendHandshakeCookie msg src) :=
  focusStatePrefix_erases _ _ (cookieEmitted_erases msg src)

theorem observed_receipts (record : Receipt → E) (mac : HandshakeMac)
    (msg : List UInt8) (src : SkbSource) (w : WGWorld) (a : Ambient) (history : List E) :
    ∃ suffix, (runWGPrefix (observed record mac msg src) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ event ∈ suffix, ∃ receipt,
        event = record receipt ∧ receipt.Valid ∧ receipt.mac = mac ∧
          receipt.input = msg ∧ receipt.source = src := by
  obtain ⟨suffix,grown,bound,valid⟩ := cookieEmitted_receipts msg src w a []
  simp only [List.nil_append] at grown
  refine ⟨suffix.map (fun datagram => record ⟨mac,msg,src,datagram⟩),?_,by simpa using bound,?_⟩
  · change history ++ ((runWGPrefix (cookieEmitted msg src) w a
        (history.filterMap (fun _ => none))).2.drop
        (history.filterMap (fun _ => (none : Option DatagramReceipt))).length).map
        (fun datagram => record ⟨mac,msg,src,datagram⟩) = _
    have empty : history.filterMap (fun _ => (none : Option DatagramReceipt)) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro _ _
      rfl
    rw [empty,List.length_nil,List.drop_zero,grown]
  · intro event member
    obtain ⟨datagram,inside,equal⟩ := List.mem_map.mp member
    subst event
    exact ⟨⟨mac,msg,src,datagram⟩,rfl,valid datagram inside,rfl,rfl,rfl⟩

theorem observed_frame (ρ : E → Option F) (record : Receipt → E)
    (quiet : ∀ receipt, ρ (record receipt) = none) (mac : HandshakeMac)
    (msg : List UInt8) (src : SkbSource) : StateHistoryFrame ρ (observed record mac msg src) := by
  intro w a h
  obtain ⟨suffix,grown,_,members⟩ := observed_receipts record mac msg src w a h
  change (runWGPrefix (observed record mac msg src) w a h).2.filterMap ρ = h.filterMap ρ
  rw [grown,List.filterMap_append]
  have silent : suffix.filterMap ρ = [] := List.filterMap_eq_nil_iff.mpr (by
    intro event member
    obtain ⟨receipt,rfl,_⟩ := members event member
    exact quiet receipt)
  rw [silent,List.append_nil]

theorem observed_ignored (ρ : E → Option F) (record : Receipt → E)
    (quiet : ∀ receipt, ρ (record receipt) = none) (mac : HandshakeMac)
    (msg : List UInt8) (src : SkbSource) :
    StateProjectsPrefix ρ id (observed record mac msg src) (liftWGPrefix (sendHandshakeCookie msg src)) := by
  intro w a h
  change (((sendHandshakeCookie msg src).run w).run a,h.filterMap ρ) =
    ((runWGPrefix (observed record mac msg src) w a h).1.map
      (fun ((x,v),b) => ((x,v),b)),(runWGPrefix (observed record mac msg src) w a h).2.filterMap ρ)
  have erase := observed_erases record mac msg src w a h
  change (runWGPrefix (observed record mac msg src) w a h).1 = _ at erase
  have frame := observed_frame ρ record quiet mac msg src w a h
  change (runWGPrefix (observed record mac msg src) w a h).2.filterMap ρ = _ at frame
  rw [erase,frame]
  cases ((sendHandshakeCookie msg src).run w).run a <;> rfl

theorem observed_appends (record : Receipt → E) (mac : HandshakeMac)
    (msg : List UInt8) (src : SkbSource) : StateAppends (observed record mac msg src) :=
  StateAppends.focus _ _ _

theorem observed_history (Safe : List E → Prop) (record : Receipt → E) (mac : HandshakeMac)
    (msg : List UInt8) (src : SkbSource)
    (append : ∀ h receipt, Safe h → receipt.Valid → Safe (h ++ [record receipt])) :
    TransmitSecurity.Driver.StateHistorySafe Safe (observed record mac msg src) := by
  intro w a h hi
  obtain ⟨suffix,grown,bound,members⟩ := observed_receipts record mac msg src w a h
  have good : Safe (h ++ suffix) := by
    cases suffix with
    | nil => simpa only [List.append_nil] using hi
    | cons event rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at bound; omega)
      subst rest
      obtain ⟨receipt,rfl,valid,_⟩ := members event (by simp)
      exact append h receipt hi valid
  change (runPrefix (StateT.run (observed record mac msg src) w) a h).2 = h ++ suffix at grown
  refine ⟨suffix,grown,grown ▸ good,?_⟩
  cases result : (runPrefix (StateT.run (observed record mac msg src) w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨value,b⟩
    exact grown ▸ good

end Leanux.Proofs.WG.AuthenticatedEffects.CookieSocket
