import Leanux.Proofs.WG.Config.EmptyMetadataGetterEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG TimerDiscipline

/-- Once cleanup has produced an empty configured list and retained the
header, the original getter completes from static entry socket and capacity
conditions. The arbitrary physical peer store is never traversed. -/
theorem empty_metadata_getter_returns (d out : Device) (sock : NlSock)
    (empty : out.peerList = [])
    (same : sendConfiguration out = sendConfiguration d)
    (room : devicePrefixSpace d + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (queue : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some out ∧ s.wg.nlSock7 = sock ∧
        ClaimView.selectsDevice s d)
      (fun result s => result = .ok (emptyPeersJson d) ∧
        s.wg.device = some out ∧ s.wg.nlSock7 = socketReadbackFinal sock d) := by
  let peers : PeerId → Peer := fun _ =>
    {remoteStatic:=[],presharedKey:=[],precomputedStaticStatic:=[],internalId:=0}
  obtain ⟨attrs,space,selector,socket⟩ := sendConfiguration_dump_congr d out same
  have enough : devicePrefixSpace out + 168 * out.peerList.length + 20 ≤ NLMSG_GOODSIZE := by
    simpa only [empty,List.length_nil,Nat.mul_zero,Nat.add_zero,space] using room
  have getter := fitting_peers_getter_returns out peers sock
    (by simp only [empty,List.not_mem_nil,false_implies,implies_true])
    (by simp only [empty,List.not_mem_nil,false_implies,implies_true])
    enough idle queue
  rw [selector] at getter
  intro g a pre
  obtain ⟨result,final,after,run,json,device,readSocket⟩ := getter g a
    ⟨pre.1,pre.2.1,(sendConfiguration_selector_congr d out same _).mpr pre.2.2⟩
  refine ⟨result,final,after,run,?_,device,?_⟩
  · simpa [multiPeerJson,multiPeerParts,empty,emptyPeersJson,attrs] using json
  · exact readSocket.trans (socket sock)


end Leanux.Proofs.WG.Config

