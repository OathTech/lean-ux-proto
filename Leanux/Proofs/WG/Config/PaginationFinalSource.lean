import Leanux.Proofs.WG.Config.PaginationPlanModel
import Leanux.Proofs.WG.Config.PaginationCallbackSource
import Leanux.Proofs.WG.Config.PaginationDoneSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Unlike the existing last-call contract, the final DATA callback does not
assume that DONE fits in the same envelope. The socket decides that later. -/
theorem socketFinalCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (beforeIds : List NodeId) (start : NodeId) (tail : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = beforeIds ++ start :: tail) (absent : start ∉ beforeIds)
    (readable : Ipv4Residents d nodes (start :: tail))
    (headerFits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fits : devicePrefixSpace d + 44 + 28 * (start :: tail).length ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump
      {hasWg := true,nextAllowedip := some start,allowedipsSeq := d.peerAllowedips.seq}
      d.deviceUpdateGen {}) (fun g => g.dev = some d)
      (fun result g => result = socketLastCall d p nodes (start :: tail) ∧ g.dev = some d) := by
  have tailRun := dumpTail_after_front d nodes p beforeIds start tail listed absent readable
    {hasWg := true,nextAllowedip := some start,allowedipsSeq := d.peerAllowedips.seq}
    {room := NLMSG_GOODSIZE - devicePrefixSpace d} rfl rfl (by simp only [List.length_cons] at fits ⊢; omega)
  have getter := multipart_getter_returns pid d p _ _ _ resident
    ((returns_iff _ _ _).mpr tailRun)
  have callback := deviceDump_single_contract pid d _ _ d.deviceUpdateGen
    (NLMSG_GOODSIZE - devicePrefixSpace d - (44 + 28 * (start :: tail).length))
    (suffixLast p nodes (start :: tail)) false peers rfl rfl (.inr rfl) headerFits getter
  simpa [socketCallbackResult,socketLastCall,Nat.sub_sub,Nat.add_assoc] using callback

/-- The fitting completed DATA path appends the original DONE and runs the
NULL-cursor finalizer. Together with completed_spill, this covers both outcomes
of the actual socket's room comparison. -/
theorem netlinkDump_completed_fits (d : Device) (sock : NlSock) (call : DumpCall)
    (active : 0 < sock.dumpDoneErrno) (completed : call.ret = 0)
    (fits : nlmsgTotal 4 ≤ call.skb.room) (cursor : call.ctx.nextPeer = none)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d)) :
    Returns (netlinkDump 7) (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun _ g => g.dev = some d ∧ g.nlSock7 =
        {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := 0,cbRunning := false, queue := sock.queue ++ [{call.skb with room := call.skb.room - nlmsgTotal 4, messages := call.skb.messages ++ [.done 2 0]}]}) := by
  intro g ambient pre
  obtain ⟨device,socket⟩ := pre
  obtain ⟨result,current,after,run,value,finalDevice⟩ := callback g ambient device
  subst result
  let final : WGWorld := {current with nlSock7 :=
    {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := 0,cbRunning := false, queue := sock.queue ++ [{call.skb with room := call.skb.room - nlmsgTotal 4, messages := call.skb.messages ++ [.done 2 0]}]}}
  let marked := {after with steps := after.steps.push {
    decision := .getDoneHasWg,outcome := call.ctx.hasWg,netRx := after.netRxSection}}
  let inputs := {marked with steps := marked.steps.push {
    decision := .peerPutNull,outcome := true,netRx := marked.netRxSection}}
  have enough : ¬ call.skb.room < nlmsgTotal 4 := by omega
  refine ⟨(),final,inputs,?_,finalDevice,rfl⟩
  simp [netlinkDump,getNlSock,socket,active]
  rw [run]
  dsimp only [bind,Except.bind]
  simp [completed,enough,setNlSock,wgGetDeviceDone,cursor,
    peerPut,branch,AmbientM.branch,final,marked,inputs]
  rfl


end Leanux.Proofs.WG.Config
