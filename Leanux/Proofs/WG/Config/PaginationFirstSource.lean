import Leanux.Proofs.WG.Config.PaginationCompletionSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- A fitting nonempty first peer page serializes the complete original list.
The recorded branches and full peer attributes follow the actual source. -/
theorem dumpTail_first_complete (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (a : NodeId) (ids : List NodeId)
    (listed : p.allowedipsList = a :: ids)
    (resident : Ipv4Residents d nodes (a :: ids)) (endpoint : p.endpoint = none)
    (ctx : DumpCtx) (skb : NlSkb) (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0)
    (fits : 140 + 28 * (a :: ids).length ≤ skb.room) :
    Returns (getPeerDumpTailSource p ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result =
        ({skb with room := skb.room - (140 + 28 * (a :: ids).length)},
         {ctx with nextAllowedip := none,allowedipsSeq := 0},
         .complete {socketFirstPeer p nodes (a :: ids) with split := false})) := by
  have r4 : ¬ skb.room < 4 := by omega
  have r40 : ¬ skb.room - 4 < 36 := by omega
  have r76 : ¬ skb.room - 40 < 36 := by omega
  have r96 : ¬ skb.room - 76 < 20 := by omega
  have r104 : ¬ skb.room - 96 < 8 := by omega
  have r116 : ¬ skb.room - 104 < 12 := by omega
  have r128 : ¬ skb.room - 116 < 12 := by omega
  have r136 : ¬ skb.room - 128 < 8 := by omega
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark (mark (mark (mark (mark (mark (mark
    (mark (mark ambient .getPeerNoNest false) .getPeerPubkeyFail false) .getPeerFirst true)
    .getPeerPskFail false) .getPeerPutHandshake false) .getPeerPutKeepalive false)
    .getPeerPutTx false) .getPeerPutRx false) .getPeerPutProto false)
    .getPeerEp4 false) .getPeerEp6 false) .getPeerEpFail false
  obtain ⟨result, final, after, run, finalDevice, value⟩ :=
    (returns_iff _ _ _).mpr (dumpAllowed_suffix_all d nodes p
      ctx skb {skb with room := skb.room - 136} (hexKey p.remoteStatic) (peerFixedAttrs p)
      a (a :: ids) resident (by simp [listed]) (by simp) (.inl sequence)
      (by dsimp; simp only [List.length_cons] at fits ⊢; omega)) g before device
  refine ⟨result, final, after, ?_, finalDevice, ?_⟩
  · have source : ((getPeerDumpTailSource p ctx skb).run g).run ambient =
        ((getPeerDumpAllowedSource p ctx skb {skb with room := skb.room - 136} (hexKey p.remoteStatic)
          (peerFixedAttrs p) p.allowedipsList.head?).run g).run before := by
      simp [getPeerDumpTailSource, fresh, branch, AmbientM.branch, NlSkb.put, nlaTotal,
        r4, r40, r76, r96, r104, r116, r128, r136, Nat.sub_sub,
        endpoint, AF_INET, AF_INET6, peerFixedAttrs, before, mark]
    rw [listed] at source
    simpa using source.trans run
  · have arithmetic : skb.room - 136 - (4 + 28 * (a :: ids).length) =
        skb.room - (140 + 28 * (a :: ids).length) := by omega
    simpa only [arithmetic, socketFirstPeer] using value

/-- A fitting nonempty first page completes with the full peer attributes.
DONE capacity is deliberately left to the socket transport. -/
theorem socketFirstCompleteCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (a : NodeId) (ids : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = a :: ids) (readable : Ipv4Residents d nodes (a :: ids))
    (endpoint : p.endpoint = none)
    (headerFits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fits : devicePrefixSpace d + 140 + 28 * (a :: ids).length ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = socketCallbackResult d {hasWg := true}
        (NLMSG_GOODSIZE - devicePrefixSpace d - (140 + 28 * (a :: ids).length))
        {socketFirstPeer p nodes (a :: ids) with split := false} false ∧ g.dev = some d) := by
  have tail := dumpTail_first_complete d nodes p a ids listed readable endpoint
    {hasWg := true} {room := NLMSG_GOODSIZE - devicePrefixSpace d} rfl rfl
    (by dsimp; simp only [List.length_cons] at fits ⊢; omega)
  have getter := multipart_getter_returns pid d p _ _ _ resident tail
  exact deviceDump_single_contract pid d _ _ 0 _ _ false peers rfl rfl (.inl rfl) headerFits getter

/-- An empty allowed-IP list still emits one actual full-attributes peer DATA.
There is no allowed-IP nest in that DATA; coalescing supplies the empty array. -/
theorem socketEmptyFirstCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = [])
    (headerFits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = socketCallbackResult d {hasWg := true}
        (NLMSG_GOODSIZE - devicePrefixSpace d - peerFixedSpace p)
        {publicKey := hexKey p.remoteStatic,attrs := peerFixedAttrs p} false ∧ g.dev = some d) := by
  have tail := (returns_iff _ _ _).mpr
    (dumpTail_no_allowedips_returns p {hasWg := true}
      {room := NLMSG_GOODSIZE - devicePrefixSpace d} rfl empty
      (by dsimp; omega) (fun g => g.dev = some d))
  have getter := multipart_getter_returns pid d p _ _ _ resident tail
  exact deviceDump_single_contract pid d _ _ 0 _ _ false peers rfl rfl (.inl rfl) headerFits getter

end Leanux.Proofs.WG.Config
