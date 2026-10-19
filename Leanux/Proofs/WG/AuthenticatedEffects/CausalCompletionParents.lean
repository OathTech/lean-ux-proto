import Leanux.Proofs.WG.AuthenticatedEffects.CausalHandshakePairInitialized
import Leanux.Proofs.WG.TransmitSecurity.CompletionOriginFinal

/-! A completion context inherits the allocation of its actual selected head.
The occurrence is strictly earlier in the same final journal. Authorization of
the allocation's context is deliberately a separate root-induction premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CompletionParents
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def Parent (history : List Event) (items : List SkbId) : Prop :=
  ∃ before after packets, ∃ (run : WGRunWitness (List SkbId)), ∃ id rest generation packet,
    history = before ++ Event.old (.allocated packets run) :: after ∧
    before.length < history.length ∧ items = id :: rest ∧
    run.Valid (packets.mapM newTxSkb) ∧ PacketOrigins.epoch run.after = some generation ∧
    ∃ (n : Nat), ∃ original, packets[n]? = some original ∧ run.value[n]? = some id ∧
      PacketMaterial.material original = packet

theorem certificate_parent (history : List Event) (items : List SkbId)
    (certificate : CompletionOrigin.Certificate (history.filterMap old?) items) : Parent history items := by
  obtain ⟨id,rest,generation,packet,shape,packets,run,member,valid,epoch,n,original,atPacket,atId,material⟩ := certificate
  obtain ⟨event,inHistory,decoded⟩ := List.mem_filterMap.mp member
  have same : event = .old (.allocated packets run) := by
    cases event with
    | old value => exact congrArg Event.old (Option.some.inj decoded)
    | scope value => cases decoded
    | armed value => cases decoded
    | queued value => cases decoded
    | exchange value => cases decoded
    | keepalivePrepared pid run => cases decoded
    | protocolSocket receipt => cases decoded
    | cookieSocket receipt | cookieConsumed receipt => cases decoded
    | delivery sent => cases decoded
    | transmitInput _ | stagedDisposal _ | sendResult _ | stagingTaken _ | stagedRestored _ | terminalDrop _ => cases decoded
  rw [same] at inHistory
  obtain ⟨before,after,position⟩ := List.mem_iff_append.mp inHistory
  refine ⟨before,after,packets,run,id,rest,generation,packet,position,?_,shape,valid,epoch,
    n,original,atPacket,atId,material⟩
  simp only [position,List.length_append,List.length_cons]
  omega

theorem current_entry (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (effect : Event) (index : Nat) (pid : PeerId) (items : List SkbId)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ effect :: post)
    (different : effect ≠ .old (.disposition (.completion pid items)))
    (current : CausalScope.current scope? pre = .ok (some ⟨index,.completion pid items⟩)) :
    ∃ before rest, pre = before ++
      [.scope (.entered ⟨index,.completion pid items⟩),.old (.disposition (.completion pid items))] ++ rest ∧
      Parent before items := by
  obtain ⟨before,after,entered⟩ := ContextOrigins.current_entry pre _ current
  have whole : (runPrefixOuter (execute trace placeholders) []).2 =
      before ++ .scope (.entered ⟨index,.completion pid items⟩) :: (after ++ effect :: post) := by
    simp only [position,entered,List.append_assoc,List.cons_append]
  obtain ⟨tail,paired⟩ := (HandshakePairs.initialized trace placeholders).next_completion
    before (after ++ effect :: post) index pid items whole
  cases after with
  | nil =>
    exact False.elim (different (List.cons.inj paired).1)
  | cons first rest =>
    have same : first = .old (.disposition (.completion pid items)) := (List.cons.inj paired).1
    have pair : pre = before ++
        [.scope (.entered ⟨index,.completion pid items⟩),.old (.disposition (.completion pid items))] ++ rest := by
      simpa only [same,List.append_assoc,List.cons_append,List.nil_append] using entered
    refine ⟨before,rest,pair,?_⟩
    apply certificate_parent
    have cert := PacketOrigins.final_completion trace placeholders
      (before ++ [.scope (.entered ⟨index,.completion pid items⟩)]) (rest ++ effect :: post) pid items
      (by simp only [position,pair,List.append_assoc,List.cons_append,List.nil_append])
    simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,old?,
      Option.toList_none,List.nil_append,List.append_nil] using cert

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CompletionParents
