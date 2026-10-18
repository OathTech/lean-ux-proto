import Leanux.Proofs.WG.Packets.PublicationPrepareFrames
import Leanux.Proofs.Logged.Capture

/-! Native shared-driver cuts for publication and indexed replay checking.
Prepare retains the existing exact decrypt receipts; replay captures its native
input before any endpoint, confirmation or staged-send effect. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportDriver
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

abbrev OriginEvent := MaterialOrigin.Event RxOrigin.Receipt

structure Replay where
  skb : SkbId
  packet : RxPacket
  run : RunWitness Bool

def Replay.Valid (r : Replay) : Prop :=
  r.run.Valid (liftWG (counterValidate r.packet.keypair r.packet.nonce))

def Replay.Selected (r : Replay) : Prop :=
  (Queues.RxDisposition.nativeRxStore r.run.before.wg).2 r.skb = some r.packet ∧
    r.packet.state = .crypted

def prepare (record : OriginEvent → E) (decode : E → Option OriginEvent) : PrefixM E (Option PeerId) :=
  focusPrefix record decode (liftWGObserver RxOrigin.prepare)

def counter (record : Replay → E) (skb : SkbId) (packet : RxPacket) : PrefixM E Bool :=
  receiptObserved (liftPrefix (liftWG (counterValidate packet.keypair packet.nonce)))
    (fun run => record ⟨skb,packet,run⟩)

private theorem decrypt_appends (skb : SkbId) : StateAppends (RxOrigin.decrypt skb) := by
  unfold RxOrigin.decrypt
  exact StateAppends.receiptWGObserved (StateAppends.focus _ _ _) _

private theorem native_lift_appends (action : WG.M α) :
    StateAppends (liftWGPrefix action : WGPrefix OriginEvent α) :=
  fun _ _ _ => ⟨[],by simp only [List.append_nil]; rfl⟩

theorem native_prepare_appends : StateAppends RxOrigin.prepare := by
  unfold RxOrigin.prepare RxOrigin.prepareWith
  index_unfold _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.accessState
  simp only [monadLift_self]
  repeat' first
    | with_reducible exact decrypt_appends _
    | with_reducible exact StateAppends.focus _ _ _
    | with_reducible exact native_lift_appends _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.bind
    | split
    | (session_origin_intro_forall; try dsimp only)

theorem prepare_erases (record : OriginEvent → E) (decode : E → Option OriginEvent) :
    ErasesPrefix (prepare record decode) (liftWG Queues.RxWorkers.prepareSource) :=
  focusPrefix_erases record decode (liftWGObserver_erases RxOrigin.prepare_erases)

theorem prepare_projects_other (record : OriginEvent → E) (decode : E → Option OriginEvent)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none) :
    ProjectsPrefix ρ id (prepare record decode) (liftPrefix (liftWG Queues.RxWorkers.prepareSource)) :=
  projectsPrefix_focus_other record decode ρ quiet (liftWGObserver_erases RxOrigin.prepare_erases)

theorem prepare_projects (record : OriginEvent → E) (decode : E → Option OriginEvent)
    (inverse : ∀ event, decode (record event) = some event) :
    ProjectsPrefix decode id (prepare record decode) (liftWGObserver RxOrigin.prepare) := by
  intro w h
  have projected := projectsUnder_focus (I := fun _ (_ : World) => True) record decode inverse
    (fun w h _ => native_prepare_appends.liftWGObserver w h) w h True.intro
  rw [projected]
  change ((runPrefix (prepare record decode) w h).1,(runPrefix (prepare record decode) w h).2.filterMap decode) = _
  cases result : (runPrefix (prepare record decode) w h).1 with
  | error err => rfl
  | ok out => rcases out with ⟨x,v⟩; rfl

theorem counter_erases (record : Replay → E) (skb : SkbId) (packet : RxPacket) :
    ErasesPrefix (counter record skb packet) (liftWG (counterValidate packet.keypair packet.nonce)) := by
  intro w h
  simp only [counter,runPrefix_receiptObserved,runPrefix_lift]
  cases (liftWG (counterValidate packet.keypair packet.nonce)).run w <;> rfl

theorem counter_projects_other (record : Replay → E) (ρ : E → Option F)
    (quiet : ∀ replay, ρ (record replay) = none) (skb : SkbId) (packet : RxPacket) :
    ProjectsPrefix ρ id (counter record skb packet)
      (liftPrefix (liftWG (counterValidate packet.keypair packet.nonce))) := by
  apply HistoryFrame.project
  · exact HistoryFrame.receiptObserved (HistoryFrame.lift ρ _) (fun _ => quiet _)
  · exact counter_erases record skb packet

theorem counter_run (record : Replay → E) (skb : SkbId) (packet : RxPacket) (w : World) (h : List E) :
    runPrefix (counter record skb packet) w h =
      match (liftWG (counterValidate packet.keypair packet.nonce)).run w with
      | .error err => (.error err,h)
      | .ok (value,v) => (.ok (value,v),h ++ [record ⟨skb,packet,⟨value,w,v⟩⟩]) := by
  rw [counter,runPrefix_receiptObserved]
  simp only [runPrefix_lift]
  cases (liftWG (counterValidate packet.keypair packet.nonce)).run w <;> rfl

theorem counter_receipt_valid (record : Replay → E) (skb : SkbId) (packet : RxPacket)
    (w : World) (h : List E) (value : Bool) (v : World)
    (run : (liftWG (counterValidate packet.keypair packet.nonce)).run w = .ok (value,v)) :
    runPrefix (counter record skb packet) w h =
      (.ok (value,v),h ++ [record ⟨skb,packet,⟨value,w,v⟩⟩]) ∧
    Replay.Valid ⟨skb,packet,⟨value,w,v⟩⟩ := by
  exact ⟨by rw [counter_run,run],run⟩

theorem counter_projects (record : Replay → E) (decode : E → Option Replay)
    (inverse : ∀ replay, decode (record replay) = some replay) (skb : SkbId) (packet : RxPacket) :
    ProjectsPrefix decode id (counter record skb packet) (counter id skb packet) := by
  intro w h
  rw [counter_run,counter_run]
  cases result : (liftWG (counterValidate packet.keypair packet.nonce)).run w with
  | error err => rfl
  | ok out =>
    rcases out with ⟨value,v⟩
    simp only [id,Except.map,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,inverse]

end Leanux.Proofs.WG.AuthenticatedEffects.TransportDriver
