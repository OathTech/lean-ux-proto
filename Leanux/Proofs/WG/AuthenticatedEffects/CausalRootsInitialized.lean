import Leanux.Proofs.WG.AuthenticatedEffects.CausalRoots

/-! Initialized native effects cannot obtain authority from an unsupported
scope label or from a cyclic chain of delayed callbacks. The induction follows
strictly earlier arm, enqueue and selected-head allocation occurrences in the
same final execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Roots
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxHeartbeats 800000

private theorem not_handshake (relevant : Coverage.Protected effect) (kind : HandshakeCausal.Kind) (pid : PeerId) :
    effect ≠ .old (.handshake (.callback kind pid)) := by
  intro equal
  rw [equal] at relevant
  exact relevant.elim

private theorem not_completion (relevant : Coverage.Protected effect) (pid : PeerId) (items : List SkbId) :
    effect ≠ .old (.disposition (.completion pid items)) := by
  intro equal
  rw [equal] at relevant
  exact relevant.elim

/-- Every initialized arm, work append and TX allocation has a finite causal
explanation ending at an actual fixture operation or its own authenticated
receive. Inherited causes descend through native occurrences, not equal IDs. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool)
    (history suffix : List Event) (effect : Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = history ++ effect :: suffix)
    (relevant : Coverage.Protected effect) : Rooted history := by
  generalize lengthEq : history.length = length
  induction length using Nat.strongRecOn generalizing history suffix effect with
  | ind length ih =>
    obtain ⟨⟨index,cause⟩,current⟩ := Coverage.initialized_present trace placeholders history suffix effect position relevant
    cases cause with
    | fixture trigger =>
      obtain ⟨before,after,entered⟩ := ContextOrigins.current_entry history _ current
      exact Rooted.fixture history index trigger current before after entered
    | handshake kind pid =>
      obtain ⟨before,after,paired,admission⟩ := HandshakePairs.current_authenticated trace placeholders history suffix
        effect index kind pid position (not_handshake relevant kind pid) current
      exact Rooted.handshake history index kind pid current before after paired admission
    | candidate skb packet =>
      exact Rooted.candidate history index skb packet current
        (Coverage.candidate_authenticated trace placeholders history suffix effect position relevant index skb packet current)
    | stackInput entry =>
      obtain ⟨before,after,entered⟩ := ContextOrigins.current_entry history _ current
      have whole : (runPrefixOuter (execute trace placeholders) []).2 =
          before ++ .scope (.entered ⟨index,.stackInput entry⟩) :: (after ++ effect :: suffix) := by
        simp only [position,entered,List.append_assoc,List.cons_append]
      have authenticated := StackOrigins.initialized_authenticated trace placeholders before
        (after ++ effect :: suffix) index entry whole
      exact Rooted.stackInput history index entry current before after entered authenticated
    | timer bound pid timer entry =>
      obtain ⟨before,after,arm,stamp,expires,earlier,less,native,changed,peer,kind,pending,cause⟩ :=
        ContextOrigins.timer_parent trace placeholders history (effect :: suffix) index bound pid timer entry position current
      have whole : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .armed arm :: (after ++ effect :: suffix) := by
        simp only [position,earlier,List.append_assoc,List.cons_append]
      have rooted := ih before.length (by omega) before (after ++ effect :: suffix) (.armed arm) whole True.intro rfl
      exact Rooted.timer history index bound pid timer entry current before after arm stamp expires earlier
        native changed peer kind pending cause rooted
    | sendWork pid entry =>
      obtain ⟨before,after,queued,earlier,less,native,peer,cause⟩ :=
        ContextOrigins.work_parent trace placeholders history (effect :: suffix) index pid entry position current
      have whole : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .queued queued :: (after ++ effect :: suffix) := by
        simp only [position,earlier,List.append_assoc,List.cons_append]
      have rooted := ih before.length (by omega) before (after ++ effect :: suffix) (.queued queued) whole True.intro rfl
      exact Rooted.work history index pid entry current before after queued earlier native peer cause rooted
    | completion pid items =>
      obtain ⟨scopeBefore,rest,paired,parent⟩ := CompletionParents.current_entry trace placeholders history suffix effect
        index pid items position (not_completion relevant pid items) current
      obtain ⟨before,after,packets,run,id,tail,generation,packet,earlier,less,shape,native,epoch,
        ordinal,original,atPacket,atId,material⟩ := parent
      have whole : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .old (.allocated packets run) ::
          (after ++ [.scope (.entered ⟨index,.completion pid items⟩),.old (.disposition (.completion pid items))] ++ rest ++ effect :: suffix) := by
        simp only [position,paired,earlier,List.append_assoc,List.cons_append]
      have shorter : before.length < length := by
        have sizes := congrArg List.length paired
        simp only [List.length_append,List.length_cons,List.length_nil] at sizes
        omega
      have rooted := ih before.length shorter before _ (.old (.allocated packets run)) whole True.intro rfl
      exact Rooted.completion history index pid items current scopeBefore rest paired before after packets run id tail
        generation packet earlier shape native epoch ordinal original atPacket atId material rooted

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Roots
