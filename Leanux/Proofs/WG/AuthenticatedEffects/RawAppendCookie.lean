import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendProtocol
import Leanux.Proofs.WG.AuthenticatedEffects.CookieSocketSource

/-! The cookie source already observes the primitive tunnel append directly.
Discard its extra construction metadata without consulting any completed final
journal receipt; the original append occurrence and ordered position remain. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged

def datagramEvent (receipt : DatagramReceipt) : Event :=
  ⟨receipt.front.after.sent,receipt.datagram⟩

def cookie (msg : List UInt8) (source : SkbSource) : WGPrefix Event Unit :=
  focusStatePrefix datagramEvent (fun _ => none) (cookieEmitted msg source)

private theorem filter_none (history : List E) :
    history.filterMap (fun _ => (none : Option F)) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro _ _
  rfl

theorem cookie_projects (decode : E → Option Event) (record : CookieSocket.Receipt → E)
    (selected : ∀ receipt, decode (record receipt) = some (datagramEvent receipt.datagram))
    (mac : HandshakeMac) (msg : List UInt8) (source : SkbSource) :
    StateProjectsPrefix decode id (CookieSocket.observed record mac msg source) (cookie msg source) := by
  intro w a history
  change
    ((runWGPrefix (cookieEmitted msg source) w a
        ((history.filterMap decode).filterMap (fun _ => none))).1,
      history.filterMap decode ++
        ((runWGPrefix (cookieEmitted msg source) w a
          ((history.filterMap decode).filterMap (fun _ => none))).2.drop
          ((history.filterMap decode).filterMap (fun _ => (none : Option DatagramReceipt))).length).map datagramEvent) =
    ((runWGPrefix (cookieEmitted msg source) w a (history.filterMap (fun _ => none))).1.map
      (fun ((value,v),b) => ((value,v),b)),
      (history ++ ((runWGPrefix (cookieEmitted msg source) w a (history.filterMap (fun _ => none))).2.drop
        (history.filterMap (fun _ => (none : Option DatagramReceipt))).length).map
          (fun datagram => record ⟨mac,msg,source,datagram⟩)).filterMap decode)
  simp only [filter_none,List.length_nil,List.drop_zero,List.filterMap_append,List.filterMap_map]
  simp only [Function.comp_def,selected,List.filterMap_eq_map']
  cases (runWGPrefix (cookieEmitted msg source) w a []).1 <;> rfl

theorem cookie_erases (msg : List UInt8) (source : SkbSource) :
    ErasesStatePrefix (cookie msg source) (sendHandshakeCookie msg source) :=
  focusStatePrefix_erases datagramEvent (fun _ => none) (cookieEmitted_erases msg source)

theorem cookie_count (msg : List UInt8) (source : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List Event) :
    ∃ suffix, (runWGPrefix (cookie msg source) w a history).2 = history ++ suffix ∧ suffix.length ≤ 1 := by
  obtain ⟨suffix,grown,bound,_⟩ := cookieEmitted_receipts msg source w a []
  simp only [List.nil_append] at grown
  refine ⟨suffix.map datagramEvent,?_,by simpa only [List.length_map] using bound⟩
  change history ++ ((runWGPrefix (cookieEmitted msg source) w a (history.filterMap (fun _ => none))).2.drop
    (history.filterMap (fun _ => (none : Option DatagramReceipt))).length).map datagramEvent = _
  rw [filter_none,List.length_nil,List.drop_zero,grown]

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
