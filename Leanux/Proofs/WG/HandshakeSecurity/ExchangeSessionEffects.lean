import Leanux.Proofs.WG.HandshakeSecurity.ExchangeInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeSessionSource

/-! The initialized session receipt is tied to its native clearing and actual
allocation cuts. A counter delta alone is not used as an allocation witness.
Final role-slot residency remains distinct from the creation cut. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues MaterialOrigin

theorem initialized_session_effects (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.session pid r :: post) :
    r.Valid (beginSession pid) ∧
    (r.value = true → handshakeTagAt r.before pid = some HANDSHAKE_CREATED_RESPONSE ∨
      handshakeTagAt r.before pid = some HANDSHAKE_CONSUMED_RESPONSE) ∧
    (∀ target, handshakeTagAt r.after target = if r.value = true ∧ target = pid then
      some HANDSHAKE_ZEROED else handshakeTagAt r.before target) ∧
    r.after.keypairCounter = r.before.keypairCounter + (if r.value then 1 else 0) := by
  have valid := ((initialized facts config traffic trace placeholders).checked
    pre post (.session pid r) position).1
  exact ⟨valid,facts.edges.session pid r.before r.after r.ambientBefore r.ambientAfter r.value valid⟩

theorem initialized_session_clears (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.session pid r :: post) (success : r.value = true) :
    handshakeTagAt r.after pid = some HANDSHAKE_ZEROED ∧
    (∀ target, target ≠ pid → handshakeTagAt r.after target = handshakeTagAt r.before target) ∧
    r.after.keypairCounter = r.before.keypairCounter + 1 := by
  obtain ⟨_,_,tags,count⟩ := initialized_session_effects facts config traffic trace placeholders pre post pid r position
  exact ⟨by simpa [success] using tags pid,
    fun target other => by simpa only [success,and_true,and_false,other,↓reduceIte] using tags target,
    by simpa only [success,↓reduceIte] using count⟩

theorem initialized_session_refusal (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.session pid r :: post) (refused : r.value = false) :
    (∀ target, handshakeTagAt r.after target = handshakeTagAt r.before target) ∧
    r.after.keypairCounter = r.before.keypairCounter := by
  obtain ⟨_,_,tags,count⟩ := initialized_session_effects facts config traffic trace placeholders pre post pid r position
  exact ⟨fun target => by simpa only [refused,Bool.false_eq_true,false_and,↓reduceIte] using tags target,
    by simpa [refused] using count⟩

theorem initialized_session_allocation (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.session pid r :: post) (success : r.value = true) :
    ∃ slot allocation device,
      (runWGPrefix (Installation.observed pid) r.before r.ambientBefore []).2 = [allocation] ∧
      allocation.Valid ∧ allocation.execution.value = some slot ∧
      allocation.execution.before.dev = some device ∧ slot = device.nextKeypairId ∧
      allocation.execution.after = keyAllocationWorld allocation.execution.before device allocation.word := by
  have valid := (initialized_session_effects facts config traffic trace placeholders pre post pid r position).1
  obtain ⟨_,_,_,postcondition⟩ := Installation.evidence [] pid r.before r.ambientBefore [] rfl
  have run : (runPrefix ((Installation.observed pid).run r.before) r.ambientBefore []).1 =
      .ok ((true,r.after),r.ambientAfter) :=
    (Installation.erases pid r.before r.ambientBefore []).trans (by simpa only [WGRunWitness.Valid,success] using valid)
  rw [run] at postcondition
  obtain ⟨slot,allocation,only,source,created⟩ := postcondition.2 rfl
  obtain ⟨device,resident,keyslot,endpoint⟩ := Origins.create_some allocation.word
    allocation.execution.before allocation.execution.after slot
    allocation.execution.ambientBefore allocation.execution.ambientAfter
    (by simpa only [Installation.AllocationReceipt.Valid,WGRunWitness.Valid,created] using source)
  exact ⟨slot,allocation,device,only,source,created,resident,keyslot,endpoint⟩

/-- The actual derived key at the session front and the exact suffix that
receives its numeric slot. The allocation identity is the source entry counter
plus one; final role-slot residency is deliberately a separate property. -/
def SessionMaterialCut (pid : PeerId) (r : WGRunWitness Bool) : Prop :=
  ∃ context middle clock device key,
    ((SessionOrigin.front pid).run r.before).run r.ambientBefore = .ok ((some context,middle),clock) ∧
    ((SessionOrigin.tail pid context.slot).run middle).run clock = .ok ((true,r.after),r.ambientAfter) ∧
    r.before.dev = some device ∧ device.peers[pid]? = some context.peer ∧
    context.slot = device.nextKeypairId ∧
    Origins.view middle = some (device.ifindex, fun id =>
      if context.slot = id then some key else device.keypairs[id]?) ∧
    key.internalId = r.before.keypairCounter + 1 ∧ key.peer = context.word ∧
    context.word = context.peer.handshakeEntryPeer ∧ key.receiving.isValid = true

theorem initialized_session_material (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.session pid r :: post) (success : r.value = true) : SessionMaterialCut pid r := by
  have valid := (initialized_session_effects facts config traffic trace placeholders pre post pid r position).1
  obtain ⟨context,middle,clock,front,tail⟩ := session_true_front pid r.before r.after r.ambientBefore r.ambientAfter
    (by simpa only [WGRunWitness.Valid,success] using valid)
  obtain ⟨device,key,resident,peer,_,word,slot,view,stamp,owner,receiving⟩ :=
    Origins.front_effect pid context r.before middle r.ambientBefore clock front
  exact ⟨context,middle,clock,device,key,front,tail,resident,peer,slot,view,stamp,owner,word,receiving⟩

theorem initialized_session_refusal_world (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.session pid r :: post) (refused : r.value = false) : r.after = r.before := by
  have valid := (initialized_session_effects facts config traffic trace placeholders pre post pid r position).1
  exact session_false_world pid r.before r.after r.ambientBefore r.ambientAfter
    (by simpa only [WGRunWitness.Valid,refused] using valid)

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
