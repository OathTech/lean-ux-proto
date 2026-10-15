import LookupResultHistory

namespace Binary.OwnerWord
open Leanux Leanux.WG

/-- Physical cuts after the owner store but before its source decision. -/
def PendingPC (pc : Int64) : Prop :=
  pc = Image.Lookup.entry+0xbd ∨ pc = Image.Lookup.entry+0xc0 ∨ pc = Image.Lookup.entry+0xc3

/-- The old source word comes from the actual helper-return snapshot, not
    an independently chosen ghost value. The current physical word already
    contains that snapshot's RAX. The enclosing relation must derive `events`
    from the executed history and use this component only in PendingPC. All
    other fields still need their own current-memory/phase relations. -/
def PendingAt (peers : PeerId → BitVec 64) (keypairs : KeypairId → BitVec 64)
    (events : List LookupObservation.Point) (current : MachineState)
    (device : Device) (owner : IndexOwner) : Prop :=
  PendingPC current.pc ∧ ∃ snapshot,
    events.getLast? = some snapshot ∧
    snapshot.tag = .returned "wg_peer_get_maybe_zero" ∧
    snapshot.machine.pc = Image.Lookup.entry+0xba ∧
    snapshot.machine.data.regs.rbx.toBitVec = address peers keypairs owner ∧
    At peers keypairs snapshot.machine.data.dmem device owner ∧
    current.data.dmem.loadInt (address peers keypairs owner) 8 =
      some (snapshot.machine.data.regs.rax.toNat : Int)

/-- Every pre-decision successor of the actual result-store region carries
    the pending word. The source owner can be NULL or refer to a dead peer. -/
theorem pending_after_store (peers : PeerId → BitVec 64) (keypairs : KeypairId → BitVec 64)
    (s : MachineData) (device : Device) (owner : IndexOwner)
    (location : s.regs.rbx.toBitVec = address peers keypairs owner)
    (source : At peers keypairs s.dmem device owner)
    (prior : List LookupObservation.Point) (af : Bool) (q : MachineState)
    (member : q ∈ LookupHistory.resultStates s af) (phase : PendingPC q.pc) :
    PendingAt peers keypairs
      (prior ++ [LookupObservation.returned "wg_peer_get_maybe_zero" ⟨s, Image.Lookup.entry+0xba⟩])
      q device owner := by
  refine ⟨phase, LookupObservation.returned "wg_peer_get_maybe_zero" ⟨s, Image.Lookup.entry+0xba⟩,
    by simp, rfl, rfl, location, source, ?_⟩
  rw [← location, LookupHistory.resultStates_memory s af q member]
  exact load64_store _ _ _

/-- Under fixed allocation names the snapshot determines a unique old
    source word, even though current memory contains the new one. -/
theorem pending_functional {present} (names : PeerNames present)
    (keypairs : KeypairId → BitVec 64) (events : List LookupObservation.Point)
    (current : MachineState) (first second : Device) (owner : IndexOwner)
    (a b : Option PeerId)
    (firstAt : PendingAt names.address keypairs events current first owner)
    (secondAt : PendingAt names.address keypairs events current second owner)
    (firstValue : value first owner = some a) (secondValue : value second owner = some b)
    (firstNamed : Named present a) (secondNamed : Named present b) : a = b := by
  obtain ⟨_, snapshot, last, _, _, _, old, _⟩ := firstAt
  obtain ⟨_, snapshot', last', _, _, _, old', _⟩ := secondAt
  have same : snapshot' = snapshot := Option.some.inj (last'.symm.trans last)
  subst snapshot'
  obtain ⟨word, selected, represented⟩ := old
  obtain ⟨word', selected', represented'⟩ := old'
  have ha : word = a := Option.some.inj (selected.symm.trans firstValue)
  have hb : word' = b := Option.some.inj (selected'.symm.trans secondValue)
  subst word
  subst word'
  exact Field.functional names represented represented' firstNamed secondNamed

/-- The three pending successors emit no event, so the last observed point
    stays the real helper return until the final conditional edge. -/
theorem pending_observed (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      (⟨s, Image.Lookup.entry+0xba⟩ :: (LookupHistory.resultStates s af).take 3) = .ok [] := by
  simp [observeHistory, LookupHistory.resultStates, LookupObservation.edge,
    Image.Lookup.entry, Image.PeerGet.entry]

/-- Commit the ordinary word relation using the landed source setter. The
    supplied World/Peer are from helper return, so an aliased helper increment
    is retained. This post-setter word equation already holds physically in
    pending states; the matched source World advances only at idxPeerAlive.
    This says nothing about the other whole-World components. -/
theorem handshake_result_at (peers : PeerId → BitVec 64) (keypairs : KeypairId → BitVec 64)
    (w : World) (device : Device) (id : PeerId) (peer : Peer) (word : Option PeerId)
    (hasDevice : w.k.wg = some device) (hasPeer : device.peers.get? id = some peer)
    (s : MachineData) (location : s.regs.rbx.toBitVec = address peers keypairs (.handshake id))
    (result : s.regs.rax.toBitVec = pointer peers word)
    (af : Bool) (q : MachineState) (member : q ∈ LookupHistory.resultStates s af) :
    ∃ w' device', ((IndexOwner.handshake id).setPeerWord word).run w = .ok ((), w') ∧
      w'.k.wg = some device' ∧ At peers keypairs q.data.dmem device' (.handshake id) := by
  refine ⟨_, _, set_handshake_run w device id peer word hasDevice hasPeer, rfl, ?_⟩
  rw [LookupHistory.resultStates_memory s af q member]
  change At peers keypairs (s.dmem.storeInt s.regs.rbx.toBitVec 8 s.regs.rax.toBitVec.toInt) _ _
  rw [location, result]
  exact handshake_store_at peers keypairs s.dmem device id peer word

theorem keypair_result_at (peers : PeerId → BitVec 64) (keypairs : KeypairId → BitVec 64)
    (w : World) (device : Device) (id : KeypairId) (kp : Keypair) (word : Option PeerId)
    (hasDevice : w.k.wg = some device) (hasKeypair : device.keypairs.get? id = some kp)
    (s : MachineData) (location : s.regs.rbx.toBitVec = address peers keypairs (.keypair id))
    (result : s.regs.rax.toBitVec = pointer peers word)
    (af : Bool) (q : MachineState) (member : q ∈ LookupHistory.resultStates s af) :
    ∃ w' device', ((IndexOwner.keypair id).setPeerWord word).run w = .ok ((), w') ∧
      w'.k.wg = some device' ∧ At peers keypairs q.data.dmem device' (.keypair id) := by
  refine ⟨_, _, set_keypair_run w device id kp word hasDevice hasKeypair, rfl, ?_⟩
  rw [LookupHistory.resultStates_memory s af q member]
  change At peers keypairs (s.dmem.storeInt s.regs.rbx.toBitVec 8 s.regs.rax.toBitVec.toInt) _ _
  rw [location, result]
  exact keypair_store_at peers keypairs s.dmem device id kp word

#print axioms pending_after_store
#print axioms pending_functional
#print axioms pending_observed
#print axioms handshake_result_at
#print axioms keypair_result_at
end Binary.OwnerWord
