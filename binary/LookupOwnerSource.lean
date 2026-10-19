import SourceAdapter
import OwnerStore
import LookupPeerSource

namespace Binary.LookupRelation
open Leanux Leanux.WG

/-- Store-back changes the selected word only. In particular a handshake
    owner equal to the referenced peer retains the helper's committed count. -/
theorem owner_set_project (c : Config) (world : World) (v : View)
    (owner : IndexOwner) (old word : Option PeerId)
    (projected : project c world = some v) (focused : c.focus.owner = some owner)
    (oldWord : v.ownerWord = some old) :
    ∃ final, (Source.setPeerWord owner word).run world = .ok ((), final) ∧
      project c final = some {v with ownerWord := some word} ∧
      final.steps = world.steps ∧ final.netRxSection = world.netRxSection := by
  cases hasDevice : world.wg.dev with
  | none => simp [project, hasDevice] at projected
  | some device =>
    have selectedWord : OwnerWord.value device owner = some old := by
      have h := congrArg (fun view : Option View => view.bind (·.ownerWord)) projected
      simpa [project, hasDevice, focused, oldWord] using h
    cases owner with
    | handshake id =>
      cases hasPeer : device.peers[id]? with
      | none => simp [OwnerWord.value, hasPeer] at selectedWord
      | some peer =>
        refine ⟨_, OwnerWord.set_handshake_run world device id peer word hasDevice hasPeer, ?_, rfl, rfl⟩
        have counts : (fun pid => ((device.peers.insert id {peer with handshakeEntryPeer := word}).get? pid).map (·.refcount)) =
            (fun pid => (device.peers.get? pid).map (·.refcount)) := by
          funext pid
          by_cases eq : id = pid
          · subst pid
            have h : device.peers[id]? = some peer := hasPeer
            simp [h]
          · simp [Std.TreeMap.getElem?_insert, eq]
        have view : v = {
            bucket := device.indexTable.filter (fun e => e.index % 8192 == c.query % 8192)
            ownerWord := some old
            count := c.focus.peer.bind (fun pid => (device.peers.get? pid).map (·.refcount)) } := by
          simpa [project, hasDevice, focused, selectedWord] using projected.symm
        subst v
        simpa [project, focused, OwnerWord.value] using congrArg (fun count => some ({
          bucket := device.indexTable.filter (fun e => e.index % 8192 == c.query % 8192)
          ownerWord := some word
          count := count } : View)) (congrArg (Option.bind c.focus.peer) counts)
    | keypair id =>
      cases hasKeypair : device.keypairs[id]? with
      | none => simp [OwnerWord.value, hasKeypair] at selectedWord
      | some kp =>
        refine ⟨_, OwnerWord.set_keypair_run world device id kp word hasDevice hasKeypair, ?_, rfl, rfl⟩
        have view : v = {
            bucket := device.indexTable.filter (fun e => e.index % 8192 == c.query % 8192)
            ownerWord := some old
            count := c.focus.peer.bind (fun pid => (device.peers.get? pid).map (·.refcount)) } := by
          simpa [project, hasDevice, focused, selectedWord] using projected.symm
        subst v
        simp [project, focused, OwnerWord.value]

#print axioms owner_set_project
end Binary.LookupRelation
