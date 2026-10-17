import Leanux.Proofs.WG.Config.TwoPageDrainSource
import Leanux.Proofs.WG.Config.PageTransitionSource
import Leanux.Proofs.WG.Config.PaginationChainSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- An actual finite drain contract, with a sufficient receive budget.
The final Device is the accumulated native state, not a reconstruction.
The budget alone does not assert a minimal number of receive calls. -/
def PageDrainContract (d : Device) (sock : NlSock)
    (finalDevice : Device) (finalSock : NlSock) (messages : List NlMessage)
    (count : Nat) : Prop :=
  ∀ step budget acc, count ≤ budget →
    Returns (forIn (List.range' step budget) (acc,false) receiveDumpStep)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = (acc ++ messages.toArray,true) ∧
        g.dev = some finalDevice ∧ g.nlSock7 = finalSock)

/-- A completed callback's queued DATA finishes the drain using one receive,
or two when DONE spills into its own envelope. -/
theorem pageDrain_completed (d : Device) (sock : NlSock) (call : DumpCall)
    (attrs : List (String × Json)) (parts : Option (List PeerDumpAttrs))
    (running : sock.cbRunning = true) (cursor : call.ctx = {hasWg := true})
    (sequence : call.prevSeq = d.deviceUpdateGen)
    (data : call.skb.messages = [.data 2 attrs parts]) :
    PageDrainContract d (paginationCompletedSocket sock call) d (socketReadbackFinal sock d)
      [.data 2 attrs parts,.done 2 0]
      (if call.skb.room < nlmsgTotal 4 then 2 else 1) := by
  intro step budget acc enough
  exact getterReceive_completed_page d sock call attrs parts step budget acc
    running cursor sequence data enough

/-- Prefix one actual DATA receive and its possibly changed Device. The
remaining contract begins after that receive has run the next callback. -/
theorem pageDrain_prepend (d middle finalDevice : Device)
    (sock nextSock finalSock : NlSock)
    (attrs : List (String × Json)) (parts : Option (List PeerDumpAttrs))
    (messages : List NlMessage) (count : Nat)
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some [.data 2 attrs parts] ∧
        g.dev = some middle ∧ g.nlSock7 = nextSock))
    (tail : PageDrainContract middle nextSock finalDevice finalSock messages count) :
    PageDrainContract d sock finalDevice finalSock
      (.data 2 attrs parts :: messages) (count+1) := by
  intro step budget acc enough
  cases budget with
  | zero => omega
  | succ budget =>
    have first := receiveDumpStep_data_device_transition d middle sock nextSock
      step acc 2 attrs parts receive
    have rest := tail (step+1) budget (acc.push (.data 2 attrs parts)) (by omega)
    intro g ambient pre
    obtain ⟨value,current,inputs,run,valueEq,device,socket⟩ := first g ambient pre
    subst value
    obtain ⟨result,final,after,restRun,resultEq,finalDeviceEq,finalSocket⟩ :=
      rest current inputs ⟨device,socket⟩
    refine ⟨result,final,after,?_,?_,finalDeviceEq,finalSocket⟩
    · rw [List.range'_succ,List.forIn_cons]
      change (((receiveDumpStep step (acc,false)).run g).run ambient >>= _) = _
      rw [run]
      exact restRun
    · rw [List.toArray_cons, ← Array.append_assoc, ← Array.push_eq_append]
      exact resultEq

/-- The original bounded getter drain, after its start has queued a page.
Both the drain contract and coalescer equation are source premises to be
derived by the native page producer before a whole-getter claim. -/
theorem getterDrain_pages_source (d finalDevice : Device) (sock finalSock : NlSock)
    (messages : List NlMessage) (count : Nat) (json : Json)
    (drain : PageDrainContract d sock finalDevice finalSock messages count)
    (enough : count ≤ 4096)
    (coalesced : coalesce messages = pure (.ok json)) :
    Returns getterDrainSource (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .ok json ∧ g.dev = some finalDevice ∧ g.nlSock7 = finalSock) := by
  have actual := drain 0 4096 #[] enough
  intro g ambient pre
  obtain ⟨value,final,after,run,valueEq,device,socket⟩ := actual g ambient pre
  simp only [Array.empty_append] at valueEq
  subst value
  refine ⟨.ok json,final,after,?_,rfl,device,socket⟩
  rw [getterDrain_range_source]
  change (((forIn (List.range' 0 4096) (#[],false) receiveDumpStep).run g).run ambient >>= _) = _
  rw [run]
  change ((coalesce messages.toArray.toList).run final).run after = _
  rw [coalesced]
  rfl

end Leanux.Proofs.WG.Config
