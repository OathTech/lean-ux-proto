import Leanux.Proofs.WG.TransmitSecurity.JournalPacketOrigins
import Leanux.Proofs.WG.TransmitSecurity.CompletionOriginSource

/-! Completion and encryption share the existing initialized allocation
carrier. Their certificates refer to strict preceding journal prefixes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
set_option maxHeartbeats 600000

theorem Safe.completion_good (old : Safe h) :
    CompletionOrigin.Good h (h.filterMap Journal.completion?) := by
  intro items member
  obtain ⟨event,inside,encoded⟩ := List.mem_filterMap.mp member
  obtain ⟨original,present,decoded⟩ := List.mem_filterMap.mp inside
  cases original <;> simp only [Journal.completion?,Option.some.injEq,reduceCtorEq] at decoded
  case disposition value =>
    subst event
    cases value <;> simp only [CompletionOrigin.entry?,Option.some.injEq,reduceCtorEq] at encoded
    rename_i pid batch
    subst batch
    obtain ⟨pre,post,position⟩ := List.mem_iff_append.mp present
    exact (old pre (.disposition (.completion pid items)) post position).mono
      (fun _ member => by rw [position]; exact List.mem_append_left _ member)
  case socket value => subst event; cases encoded

theorem Safe.completion_suffix (old : Safe h) (fresh : CompletionOrigin.Good h suffix) :
    Safe (h ++ suffix.map Journal.completionEvent) := by
  apply old.append
  intro pre event post position
  have member : event ∈ suffix.map Journal.completionEvent := by rw [position]; simp
  obtain ⟨e,inside,rfl⟩ := List.mem_map.mp member
  cases e with
  | socket value => trivial
  | disposition value =>
    cases value <;> simp only [Journal.completionEvent,Checked]
    rename_i pid items
    exact (fresh items (List.mem_filterMap.mpr ⟨.disposition (.completion pid items),inside,rfl⟩)).mono
      (fun _ member => List.mem_append_left _ member)

theorem transmit_completion (pid : PeerId) :
    PrefixPreserves (fun h w => JournalInv h w.wg) Safe (Journal.transmit pid) := by
  intro w h before
  obtain ⟨suffix,extension,good,after⟩ := CompletionOrigin.step (bank := h) pid w
    (h.filterMap Journal.completion?) ⟨before.1,before.2.completion_good⟩
  have out := focusPrefix_suffix Journal.completionEvent Journal.completion?
    (Completion.step pid) w h _ suffix (Prod.ext rfl extension)
  change runPrefix (Journal.transmit pid) w h = _ at out
  have fresh : CompletionOrigin.Good h suffix := by
    intro items member
    apply good items
    rw [extension,List.filterMap_append]
    exact List.mem_append_right _ member
  have safe := before.2.completion_suffix fresh
  rw [out]
  refine ⟨suffix.map Journal.completionEvent,rfl,safe,?_⟩
  cases result : (runPrefix (Completion.step pid) w (h.filterMap Journal.completion?)).1 with
  | error stop => trivial
  | ok value =>
    simp only [result] at after
    exact ⟨after.1.mono (fun _ member => List.mem_append_left _ member),safe⟩

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
