import Leanux.Proofs.WG.Config.ReplacementConverseRequestSource
import Leanux.Proofs.WG.Config.ReplacementReadbackEffects
import Leanux.Proofs.WG.Config.ReplacementRequestReadbackFrames
import Leanux.Proofs.WG.Config.ReplacementSurvivorFrames
import Leanux.Proofs.WG.Config.MixedNodeViewFrames
import Leanux.Proofs.WG.Config.MixedGetterInputFrames
import Leanux.Proofs.WG.Config.MixedGetterClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean

/-- Actual empty allowed-IP replacement followed by complete mixed readback.
All original peer occurrences remain, with every removed ID filtered from
their lists. Only readable nonremoved dump nodes need a non-null owner.
The normal-return setter derives its structural removal effect; the getter
runs on that same successor, with its exact ordered cursor effects. -/
theorem replacement_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (key : Key) (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid)) (pairs : NodePairs d)
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount+1 < 2^31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList, d.nodes[id]? = some (nodes id))
    (owned : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList,
      id ∉ (peers pid).allowedipsList → (nodes id).peer.isSome = true)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let ids := (peers pid).allowedipsList
    let baseline := replacementReadbackInputs d ids
    let configured := fun q => erasePeerList ids (peers q)
    ∀ ready : MixedPageReady baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true},
    devicePrefixSpace baseline ≤ NLMSG_GOODSIZE →
    MixedPlanFresh baseline configured
      (mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready) →
    MixedPlanCursorData baseline
      (mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready) →
    mixedPageReceiveCount
      (mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready) ≤ 4096 →
    Campaign2.Ensures (do
      let ret ← wgSetDevice (replaceAllowedipsDeviceAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧ s.wg.nlSock7 = sock)
      (fun result s =>
        let pages := mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready
        result = (0,.ok (mixedGetterJson baseline configured nodes)) ∧
        ∃ removed,
          RemovalEffect (withPeer (requestGeneration d) pid
            {peers pid with refcount := (peers pid).refcount+1}) ids removed ∧
          let current := generalReplacementDevice removed pid (peers pid)
          s.wg.device = some (mixedPagesDevice current pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock current ∧
          CursorHeld current (mixedPagesDevice current pages) none) := by
  dsimp only
  intro ready headerFits fresh cursorData within entry ambient result final after pre run
  change (((wgSetDevice (replaceAllowedipsDeviceAttrs d key)).run entry).run ambient >>= fun ((ret,middle),next) =>
    ((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
  cases setRun : ((wgSetDevice (replaceAllowedipsDeviceAttrs d key)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok out =>
    obtain ⟨⟨ret,middle⟩,next⟩ := out
    have framed := setDevice_replace_readbackFrame key pid d (peers pid) sock entry.fixtureNetDevices
      found resident pairs live bounded down entry ambient ret middle next
        ⟨pre.1,pre.2.1,pre.2.2,rfl⟩ setRun
    obtain ⟨code,removed,steps,device⟩ := setDevice_replace_effect_pairs key pid d (peers pid)
      found resident pairs live bounded down entry ambient ret middle next ⟨pre.1,pre.2.1⟩ setRun
    let ids := (peers pid).allowedipsList
    let baseline := replacementReadbackInputs d ids
    let configured : PeerId → Peer := fun q => erasePeerList ids (peers q)
    let current := generalReplacementDevice removed pid (peers pid)
    obtain ⟨outer,sequence,lookup⟩ := replacementReadback_effect d removed pid (peers pid) resident steps
    have members : current.peerList = baseline.peerList := by
      have h := congrArg Device.peerList outer
      exact h
    have attrs : deviceFixedAttrs current = deviceFixedAttrs baseline := by
      have h := congrArg deviceFixedAttrs outer
      exact h
    have space : devicePrefixSpace current = devicePrefixSpace baseline := by
      have h := congrArg devicePrefixSpace outer
      exact h
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex outer
      exact h
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname outer
      exact h
    obtain ⟨rows,json,freshEq,cursorEq⟩ := mixedGetter_data_congr baseline current configured configured
      members attrs (fun _ => rfl) (fun q => congrArg (Option.map keyGetterPeerView) (lookup q)) nodes
    have currentResidents : ∀ q ∈ current.peerList, current.peers[q]? = some (configured q) := by
      intro q member
      rw [lookup q]
      have listed : q ∈ d.peerList := members ▸ member
      simp only [replacementReadbackInputs,requestGeneration,Std.TreeMap.getElem?_map,
        residents q listed,Option.map_some,configured,ids]
    let footprint := d.peerList.flatMap (fun q => (configured q).allowedipsList)
    let values : NodeId → AipNode := fun id =>
      if id ∈ footprint then (current.nodes[id]?).getD (nodes id) else nodes id
    have surviving : ∀ id ∈ footprint, ∃ n, current.nodes[id]? = some n ∧
        dumpNodeView n = dumpNodeView (nodes id) := by
      intro id member
      obtain ⟨q,listed,belongs⟩ := List.mem_flatMap.mp member
      obtain ⟨n,read,view⟩ := removalEffect_readable_survivors steps (peers q) nodes
        (readable q listed) (owned q listed) id belongs
      exact ⟨n,read,congrArg Prod.snd view⟩
    have nodeView : ∀ id, dumpNodeView (values id) = dumpNodeView (nodes id) := by
      intro id
      by_cases member : id ∈ footprint
      · obtain ⟨n,read,view⟩ := surviving id member
        simpa only [values,ite_eq_left member,read,Option.getD_some] using view
      · simp only [values,ite_eq_right member]
    have currentReadable : ∀ q ∈ current.peerList, ∀ id ∈ (configured q).allowedipsList,
        current.nodes[id]? = some (values id) := by
      intro q member id belongs
      have listed : q ∈ d.peerList := members ▸ member
      have present : id ∈ footprint := List.mem_flatMap.mpr ⟨q,listed,belongs⟩
      obtain ⟨n,read,_⟩ := surviving id present
      simp only [values,ite_eq_left present,read,Option.getD_some]
    have originalReady : MixedPageReady current configured nodes
        (mixedInitialRows baseline configured) {hasWg := true} :=
      (mixedPageReady_getter_congr baseline current configured configured space (fun _ => rfl) nodes _ _).mpr ready
    have translatedReady : MixedPageReady current configured values
        (mixedInitialRows baseline configured) {hasWg := true} :=
      (mixedPageReady_node_congr current configured nodes values nodeView _ _).mpr originalReady
    have currentReady : MixedPageReady current configured values (mixedInitialRows current configured) {hasWg := true} := by
      simpa only [rows] using translatedReady
    have plan : mixedPages current configured values (mixedInitialRows current configured) {hasWg := true} currentReady =
        mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready := by
      have first := mixedPages_node_congr current configured nodes values nodeView
        (mixedInitialRows baseline configured) {hasWg := true} originalReady translatedReady
      have second := mixedPages_getter_congr baseline current configured configured space sequence
        (fun _ => rfl) nodes (mixedInitialRows baseline configured) {hasWg := true} ready originalReady
      simpa only [rows] using first.trans second
    have selection : selectsDevice middle current := by
      have initial : selectsDevice entry d := pre.2.1
      simpa only [selectsDevice,framed.2,index,name] using initial
    obtain ⟨dump,out,rest,getRun,dumped,finalDevice,finalSocket,held⟩ :=
      mixed_getter_returns current configured values sock currentReady currentResidents currentReadable
        (by simpa only [space] using headerFits)
        (by rw [plan]; exact (freshEq _).mpr fresh)
        (by rw [plan]; exact (cursorEq _).mpr cursorData)
        idle emptyQueue (by simpa only [plan] using within)
        middle next ⟨device,framed.1,selection⟩
    have selector : byIndex d = byIndex current := by simp only [byIndex,index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    have jsonNodes := mixedGetterJson_node_congr current configured nodes values nodeView
    refine ⟨?_,removed,steps,?_,finalSocket,?_⟩
    · rw [code,dumped,jsonNodes,json]
    · simpa only [plan] using finalDevice
    · simpa only [plan] using held

end Leanux.Proofs.WG.Config
