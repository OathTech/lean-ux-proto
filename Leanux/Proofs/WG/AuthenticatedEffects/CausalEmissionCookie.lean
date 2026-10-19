import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionState
import Leanux.Proofs.WG.AuthenticatedEffects.CookieEmissionAccounting

/-! The actual cookie observer appends precisely the native emitted datagrams
to the final journal's ordered accounting, preserving their multiplicity. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem cookie (mac : HandshakeMac) (msg : List UInt8) (src : SkbSource) :
    StateSafe (CookieSocket.observed Event.cookieSocket mac msg src) := by
  intro w a h hi
  let encode := fun datagram => Event.cookieSocket ⟨mac,msg,src,datagram⟩
  obtain ⟨suffix,grown,_,counted⟩ := CookieAccounting.cookie msg src w.sent w a []
    (by simp only [List.map_nil,List.append_nil])
  change (runWGPrefix (cookieEmitted msg src) w a []).2 = [] ++ suffix at grown
  simp only [List.nil_append] at grown
  have empty : h.filterMap (fun _ => (none : Option DatagramReceipt)) = [] :=
    List.filterMap_eq_nil_iff.mpr (fun _ _ => rfl)
  have nativeRun : runPrefix ((cookieEmitted msg src).run w) a
      (h.filterMap (fun _ => none)) =
      ((runWGPrefix (cookieEmitted msg src) w a []).1,
        h.filterMap (fun _ => none) ++ suffix) := by
    rw [empty,List.nil_append]
    exact Prod.ext rfl grown
  have focused := focusPrefix_suffix encode (fun _ => none) ((cookieEmitted msg src).run w)
    a h _ suffix nativeRun
  change runPrefix ((CookieSocket.observed Event.cookieSocket mac msg src).run w) a h = _ at focused
  rw [focused]
  refine ⟨suffix.map encode,rfl,True.intro,?_⟩
  cases result : (runWGPrefix (cookieEmitted msg src) w a []).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    simp only [runWGPrefix,runStatePrefix] at result grown
    rw [result,grown] at counted
    obtain ⟨earlier,historyEq⟩ := hi
    refine ⟨earlier,?_⟩
    rw [emitted_append,historyEq,counted,List.append_assoc]
    apply congrArg (fun tail => earlier ++ (w.sent ++ tail))
    clear grown nativeRun focused counted
    induction suffix with
    | nil => rfl
    | cons receipt rest ih =>
      change receipt.datagram :: emitted (rest.map encode) = receipt.datagram :: rest.map DatagramReceipt.datagram
      rw [ih]

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
