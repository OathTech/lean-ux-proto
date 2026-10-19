import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsProjection

/-! Capture the actual outer send result, including the unsupported-endpoint
false arm which has no inner socket receipt. A successful result is not another
terminal event: the earlier socket handoff already supplies that terminal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.SendResult
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects

structure Receipt where
  pid : PeerId
  skb : SkbId
  packet : RunWitness DataPacket
  run : RunWitness Bool

def Receipt.Valid (r : Receipt) : Prop :=
  r.packet.Valid (liftWG (getTxSkb r.skb)) ∧
  r.run.Valid (liftWG (sendSkbToPeer r.pid r.packet.value.bytes r.packet.value.ds))

/-- The native `.sendSkbOk false` result is a counterless refusal. Its
underlying action is visible in Valid, including the unsupported-family arm. -/
def Receipt.failed (r : Receipt) : Prop := r.run.value = false

def observed (record : Receipt → E) (send : PrefixM E Bool)
    (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) : PrefixM E Bool :=
  receiptObserved send (fun run => record ⟨pid,skb,packet,run⟩)

def decorate (record : Receipt → E) (base : CompletionEffects.Ops E) : CompletionEffects.Ops E :=
  {base with send := fun pid skb packet => observed record (base.send pid skb packet) pid skb packet}

theorem observed_erases (record : Receipt → E) (send : PrefixM E Bool)
    (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (erases : ErasesPrefix send (liftWG (sendSkbToPeer pid packet.value.bytes packet.value.ds))) :
    ErasesPrefix (observed record send pid skb packet)
      (liftWG (sendSkbToPeer pid packet.value.bytes packet.value.ds)) := by
  intro w h
  rw [observed,runPrefix_receiptObserved]
  have same := erases w h
  cases run : runPrefix send w h with
  | mk result events =>
    rw [run] at same
    cases result with
    | error stop => exact same
    | ok out => rcases out with ⟨value,state⟩; exact same

theorem observed_completed (record : Receipt → E) (send : PrefixM E Bool)
    (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (w v : World) (h tail : List E) (sent : Bool)
    (run : runPrefix send w h = (.ok (sent,v),tail)) :
    runPrefix (observed record send pid skb packet) w h =
      (.ok (sent,v),tail ++ [record ⟨pid,skb,packet,⟨sent,w,v⟩⟩]) := by
  rw [observed,runPrefix_receiptObserved,run]

theorem completed_valid (send : PrefixM E Bool) (pid : PeerId) (skb : SkbId)
    (packet : RunWitness DataPacket)
    (packetRead : packet.Valid (liftWG (getTxSkb skb)))
    (erases : ErasesPrefix send (liftWG (sendSkbToPeer pid packet.value.bytes packet.value.ds)))
    (w v : World) (h tail : List E) (sent : Bool)
    (run : runPrefix send w h = (.ok (sent,v),tail)) :
    (⟨pid,skb,packet,⟨sent,w,v⟩⟩ : Receipt).Valid := by
  refine ⟨packetRead,?_⟩
  exact (erases w h).symm.trans (congrArg Prod.fst run)

/-- An internal stop preserves all prior socket and access observations. It
does not invent a completed refusal or conflate an unfinished send with a drop. -/
theorem observed_stopped (record : Receipt → E) (send : PrefixM E Bool)
    (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (w : World) (h tail : List E) (stop : Stop)
    (run : runPrefix send w h = (.error stop,tail)) :
    runPrefix (observed record send pid skb packet) w h = (.error stop,tail) := by
  rw [observed,runPrefix_receiptObserved,run]

theorem decorate_projects (record : Receipt → E) (ρ : E → Option F)
    (quiet : ∀ r, ρ (record r) = none)
    {base : CompletionEffects.Ops E} {target : CompletionEffects.Ops F}
    (projects : CompletionEffects.Ops.Projects ρ base target) :
    CompletionEffects.Ops.Projects ρ (decorate record base) target where
  step := projects.step
  peer := projects.peer
  modifyPeer := projects.modifyPeer
  packet := projects.packet
  completion := projects.completion
  send := fun pid skb packet => receiptObserved_projects (fun _ => quiet _)
    (projects.send pid skb packet)
  drop := projects.drop
  dispose := projects.dispose
  traversal := projects.traversal
  sent := projects.sent
  dataSent := projects.dataSent
  fresh := projects.fresh

theorem step_projects (record : Receipt → E) (ρ : E → Option F)
    (quiet : ∀ r, ρ (record r) = none)
    {base : CompletionEffects.Ops E} {target : CompletionEffects.Ops F}
    (projects : CompletionEffects.Ops.Projects ρ base target) (pid : PeerId) :
    ProjectsPrefix ρ id (CompletionEffects.stepWith (decorate record base) pid)
      (CompletionEffects.stepWith target pid) :=
  CompletionEffects.step_projects ρ (decorate_projects record ρ quiet projects) pid

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.SendResult
