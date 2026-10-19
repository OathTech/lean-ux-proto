import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionProduct
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsEmbedding

/-! Ordered emission accounting at the original transport socket receipt.
Lifetime events are retained independently and contribute no sent occurrences;
the native socket return contributes its exact append difference. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity Queues
set_option maxHeartbeats 600000

theorem focused_receipt (encode : E → Event) (decode : Event → Option E)
    (body : PrefixM E α) (record : RunWitness α → E) (appends : Appends body)
    (quiet : ProductQuiet (focusPrefix encode decode body))
    (grows : ∀ w h value v, (runPrefix body w h).1 = .ok (value,v) →
      ∃ suffix, v.wg.sent = w.wg.sent ++ suffix)
    (covers : ∀ r, added (encode (record r)) = r.after.wg.sent.drop r.before.wg.sent.length) :
    ProductSafe (focusPrefix encode decode (receiptObserved body record)) := by
  intro w h hi
  obtain ⟨suffix,grown⟩ := appends w (h.filterMap decode)
  have quietHistory := quiet w h
  change emitted (h ++ ((runPrefix body w (h.filterMap decode)).2.drop
    (h.filterMap decode).length).map encode) = emitted h at quietHistory
  have focused : runPrefix (focusPrefix encode decode (receiptObserved body record)) w h =
      ((runPrefix (receiptObserved body record) w (h.filterMap decode)).1,
       h ++ ((runPrefix (receiptObserved body record) w (h.filterMap decode)).2.drop
         (h.filterMap decode).length).map encode) := rfl
  rw [focused,runPrefix_receiptObserved]
  cases run : runPrefix body w (h.filterMap decode) with
  | mk result history =>
    rw [run] at grown quietHistory
    change history = h.filterMap decode ++ suffix at grown
    cases result with
    | error stop =>
      exact ⟨(history.drop (h.filterMap decode).length).map encode,rfl,True.intro,True.intro⟩
    | ok out =>
      obtain ⟨value,v⟩ := out
      let receipt : RunWitness α := ⟨value,w,v⟩
      have nativeGrows := grows w (h.filterMap decode) value v (congrArg Prod.fst run)
      have kept : Inv (h ++ suffix.map encode) w.wg := by
        obtain ⟨earlier,historyEq⟩ := hi
        refine ⟨earlier,?_⟩
        rw [grown,List.drop_append_length] at quietHistory
        rw [quietHistory]
        exact historyEq
      refine ⟨suffix.map encode ++ [encode (record receipt)],?_,True.intro,?_⟩
      · simp only [grown,List.append_assoc,List.drop_append_length,List.map_append,
          List.map_cons,List.map_nil]
        rfl
      · have preserved := kept.receipt (encode (record receipt)) nativeGrows (covers receipt)
        simpa only [grown,← List.append_assoc,List.drop_append_length,List.map_append,
          List.map_cons,List.map_nil,List.append_assoc] using preserved

theorem completion_access_quiet (body : MixedM α) : ProductQuiet
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access body)) := by
  unfold Completion.access
  rw [CompletionEffects.focus_composed]
  exact focus_quiet _ _ (fun _ => rfl) _

theorem completion_socket (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion?
      (Completion.socket pid id packet peer ipv4)) := by
  unfold Completion.socket
  apply focused_receipt
  · cases ipv4 <;> exact Appends.focus _ _ _
  · cases ipv4 <;> exact completion_access_quiet _
  · intro w h value v run
    have erased : ErasesPrefix
        (if ipv4 then Completion.access (send4Prefix
          (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
          (some pid) packet.value.bytes packet.value.ds true)
         else Completion.access (send6Prefix
          (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
          (some pid) packet.value.bytes packet.value.ds true))
        (liftWG (if ipv4 then send4
          (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
          (some pid) packet.value.bytes packet.value.ds true
         else send6 (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
          (some pid) packet.value.bytes packet.value.ds true)) := by
      cases ipv4
      · exact Completion.access_erases (send6Prefix_erases _ _ _ _ _)
      · exact Completion.access_erases (send4Prefix_erases _ _ _ _ _)
    have native := (erased w h).symm.trans run
    rw [liftWG_run] at native
    cases original : ((if ipv4 then send4
        (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
        (some pid) packet.value.bytes packet.value.ds true
      else send6 (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
        (some pid) packet.value.bytes packet.value.ds true).run w.wg).run w.ambient with
    | error stop => simp [original,Except.map] at native
    | ok out =>
      obtain ⟨⟨result,u⟩,a⟩ := out
      simp only [original,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
      have worldEq : v.wg = u := congrArg World.wg native.2.symm
      rw [worldEq]
      have emitted : SocketEmission (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
          packet.value.bytes packet.value.ds w.wg.sent u.sent := by
        cases ipv4
        · exact Completion.send6_emission _ _ _ _ _ _ _ _ _ _ original
        · exact Completion.send4_emission _ _ _ _ _ _ _ _ _ _ original
      exact ⟨emitted.choose,emitted.choose_spec.1⟩
  · intro r
    rfl

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
