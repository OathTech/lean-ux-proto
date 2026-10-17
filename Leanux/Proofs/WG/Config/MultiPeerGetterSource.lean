import Leanux.Proofs.WG.Config.PaginationCompletionSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original getter drain consumes an actual queued DATA/DONE envelope.
The DATA peer nest may be absent or contain any finite peer list. -/
theorem getterDrain_completed_page (d : Device) (sock : NlSock) (skb : NlSkb)
    (parts : Option (List PeerDumpAttrs)) (json : Json)
    (queued : sock.queue = [skb]) (quiet : sock.cbRunning = false)
    (messages : skb.messages = [.data 2 (deviceFixedAttrs d) parts,.done 2 0])
    (coalesced : coalesce skb.messages = pure (.ok json)) :
    Returns getterDrainSource (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .ok json ∧ g.dev = some d ∧
        g.nlSock7 = {sock with queue := []}) := by
  have first : Returns (receiveDumpStep 0 (#[],false))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .yield (skb.messages.toArray,true) ∧
        g.dev = some d ∧ g.nlSock7 = {sock with queue := []}) := by
    simp only [receiveDumpStep,Bool.false_eq_true,ite_false]
    apply returns_bind _ _ (netlinkRecvmsg_quiescent (some d) sock skb queued quiet)
    intro value g ambient pre
    obtain ⟨rfl,device,socket⟩ := pre
    refine ⟨_,g,ambient,?_,rfl,device,socket⟩
    simp [messages,List.forIn_cons,List.forIn_nil]
    rfl
  rw [getterDrain_first]
  apply returns_bind _ _ first
  intro value g ambient pre
  obtain ⟨rfl,device,socket⟩ := pre
  refine ⟨.ok json,g,ambient,?_,rfl,device,socket⟩
  simp [receiveDump_finished,coalesced]
  rfl


end Leanux.Proofs.WG.Config
