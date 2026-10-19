import Leanux.Proofs.WG.Noise.ConsumeConfirmationSource
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.WG.Origins.RetainingLeaves
import Leanux.Proofs.WG.KeyTimes.Receive
set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReceiveCompletion.Rules
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Origins.HandshakeSources

abbrev Keeps (P : WGWorld → Ambient → Prop) {α : Type} (action : WG.M α) : Prop :=
  StatePrefixPreserves (fun (_ : List Unit) g a=>P g a) (fun _=>True) (liftWGPrefix action)

theorem keeps_iff {P : WGWorld → Ambient → Prop} {α : Type} (action : WG.M α) :
    Keeps P action ↔ ∀ g a value after b, P g a →
      (action.run g).run a = .ok ((value,after),b) → P after b := by
  constructor
  · intro h g a value after b pre run
    obtain ⟨suffix,append,safe,post⟩ := h g a [] pre
    change action g a = .ok ((value,after),b) at run
    simpa only [liftWGPrefix,liftStatePrefix,StateT.run,runPrefix_lift,run] using post
  · intro h
    exact StatePrefixEnsures.lift action (fun _ _ _ _=>True.intro)
      (fun _ g a value after b pre run=>h g a value after b pre run)

theorem pure_rule (P : WGWorld → Ambient → Prop) {α : Type} (value : α) :
    Keeps P (pure value) := by
  apply (keeps_iff _).mpr
  intro g a result after b pre run
  cases run
  exact pre

theorem bind_rule (P : WGWorld → Ambient → Prop) {α β : Type}
    (action : WG.M α) (next : α → WG.M β)
    (first : Keeps P action) (rest : ∀ x, Keeps P (next x)) :
    Keeps P (action >>= next) := by
  apply (keeps_iff _).mpr
  intro g a value after b pre run
  rw [Leanux.Proofs.WG.MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨x,middle,c,head,tail⟩ := run
  exact (keeps_iff _).mp (rest x) middle c value after b
    ((keeps_iff _).mp first g a x middle c pre head) tail

theorem invariant_rule (P : WGWorld → Ambient → Prop) {α : Type} (message : String) :
    Keeps P (invariant message : WG.M α) := by
  apply (keeps_iff _).mpr
  intro g a value after b pre run
  cases run

theorem get_rule (P : WGWorld → Ambient → Prop) : Keeps P (get : WG.M WGWorld) := by
  apply (keeps_iff _).mpr
  intro g a value after b pre run
  cases run
  exact pre

theorem getDev_rule (P : WGWorld → Ambient → Prop) : Keeps P getDev := by
  unfold getDev
  apply bind_rule P _ _ (get_rule P)
  intro g
  split
  · exact pure_rule P _
  · exact invariant_rule P _

theorem getPeer_rule (P : WGWorld → Ambient → Prop) (pid : PeerId) : Keeps P (getPeer pid) := by
  unfold getPeer
  apply bind_rule P _ _ (getDev_rule P)
  intro d
  split
  · exact pure_rule P _
  · exact invariant_rule P _

theorem getKeypair_rule (P : WGWorld → Ambient → Prop) (kid : KeypairId) :
    Keeps P (getKeypair kid) := by
  unfold getKeypair
  apply bind_rule P _ _ (getDev_rule P)
  intro d
  split
  · exact pure_rule P _
  · exact invariant_rule P _

theorem of_native {P : WGWorld → Prop} {α : Type} {action : WG.M α}
    (keep : Preserves P action) : Keeps (fun g _=>P g) action :=
  (keeps_iff _).mpr ((hoare_iff_run_ambient _ _ _).mp keep)

theorem to_native {P : WGWorld → Prop} {α : Type} {action : WG.M α}
    (keep : Keeps (fun g _=>P g) action) : Preserves P action :=
  (hoare_iff_run_ambient _ _ _).mpr ((keeps_iff _).mp keep)

theorem prepareRest (P : WGWorld → Ambient → Prop) (pid : PeerId) (pkt : RxPacket)
    (branches : ∀ decision value, Keeps P (branch decision value : WG.M Bool))
    (fresh : Keeps P (keepKeyFreshRx pid))
    (received : Keeps P (timersAnyAuthenticatedPacketReceived pid))
    (traversal : Keeps P (timersTraversal pid))
    (data : Keeps P (timersDataReceived pid))
    (stats : ∀ len, Keeps P (updateRxStats pid len))
    (dishonest : ∀ why, Keeps P (WG.dishonest why))
    (ecn : ∀ protocol ds bytes, Keeps P (inetEcnDecapsulate protocol ds bytes)) :
    Keeps P (RxCredits.prepareRest pid pkt) := by
  unfold RxCredits.prepareRest WG.andM WG.orM
  repeat' first
    | with_reducible exact fresh
    | with_reducible exact received
    | with_reducible exact traversal
    | with_reducible exact data
    | with_reducible exact stats _
    | with_reducible exact dishonest _
    | with_reducible exact ecn _ _ _
    | with_reducible exact branches _ _
    | with_reducible exact pure_rule P _
    | with_reducible apply bind_rule P
    | split
    | (with_reducible intro x; try dsimp only)

theorem rxFinish (P : WGWorld → Ambient → Prop) (pid : PeerId) (ready : Packets.RxReady)
    (branches : ∀ decision value, Keeps P (branch decision value : WG.M Bool))
    (lookup : Keeps P (RxBorrow.source ready.protocol ready.bytes))
    (dishonest : Keeps P (WG.dishonest .peer))
    (stats : Keeps P (updateRxStats pid (ready.originalLen + MESSAGE_DATA_LEN_0))) :
    Keeps P (Packets.rxFinish pid ready) := by
  rw [← RxCredits.rxFinishSource_eq]
  unfold RxCredits.rxFinishSource
  repeat' first
    | with_reducible exact lookup
    | with_reducible exact dishonest
    | with_reducible exact stats
    | with_reducible exact branches _ _
    | with_reducible exact pure_rule P _
    | with_reducible apply bind_rule P
    | split
    | (with_reducible intro x; try dsimp only)

theorem afterConfirmation (P : WGWorld → Ambient → Prop)
    (pid : PeerId) (pkt : RxPacket) (confirmed : Bool)
    (branches : ∀ decision value, Keeps P (branch decision value : WG.M Bool))
    (complete : Keeps P (timersHandshakeComplete pid .walltimeLastHandshakeData))
    (staged : Keeps P (sendStagedPackets pid))
    (prepare : Keeps P (RxCredits.prepareRest pid pkt))
    (finish : ∀ ready, Keeps P (Packets.rxFinish pid ready)) :
    Keeps P (ConsumeConfirmation.afterConfirmation pid pkt confirmed) := by
  unfold ConsumeConfirmation.afterConfirmation
  repeat' first
    | with_reducible exact complete
    | with_reducible exact staged
    | with_reducible exact prepare
    | with_reducible exact finish _
    | with_reducible exact branches _ _
    | with_reducible exact pure_rule P _
    | with_reducible apply bind_rule P
    | split
    | (with_reducible intro x; try dsimp only)
theorem keepKeyFreshRx (P : WGWorld → Ambient → Prop) (pid : PeerId)
    (branches : ∀ decision value, Keeps P (branch decision value : WG.M Bool))
    (expired : ∀ birthday, Keeps P (branchExpired .rxFreshExpired birthday
      (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)))
    (modify : Keeps P (modifyPeer pid fun p => {p with sentLastminuteHandshake := true}))
    (queued : Keeps P (sendQueuedHandshakeInitiation pid false)) :
    Keeps P (WG.keepKeyFreshRx pid) := by
  have source : WG.keepKeyFreshRx pid = (do
      if ← branch .rxFreshSentLastminute (← getPeer pid).sentLastminuteHandshake then return
      let current := (← getPeer pid).keypairCurrent
      let send ← WG.andM (branch .rxFreshKeypair current.isSome) do
        let some id := current | invariant "unreachable"
        let k ← getKeypair id
        WG.andM (branch .rxFreshValid k.sending.isValid) do
          WG.andM (branch .rxFreshInitiator k.iAmTheInitiator) do
            branchExpired .rxFreshExpired k.sending.birthdate
              (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)
      if ← branch .rxFreshSend send then
        modifyPeer pid (fun p => {p with sentLastminuteHandshake := true})
        sendQueuedHandshakeInitiation pid false) := by
    simp only [WG.keepKeyFreshRx,RxCredits.modifyPeer_source,bind_assoc] <;> rfl
  rw [source]
  simp (config := {zeta := false}) only [WG.andM]
  repeat' first
    | with_reducible exact modify
    | with_reducible exact queued
    | with_reducible exact expired _
    | with_reducible exact getPeer_rule P _
    | with_reducible exact getKeypair_rule P _
    | with_reducible exact branches _ _
    | with_reducible exact invariant_rule P _
    | with_reducible exact pure_rule P _
    | with_reducible apply bind_rule P
    | split
    | (with_reducible intro x; try dsimp only)

theorem dataReceived (P : WGWorld → Ambient → Prop) (pid : PeerId)
    (branches : ∀ decision value, Keeps P (branch decision value : WG.M Bool))
    (arm : Keeps P (modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS))
    (update : Keeps P (modifyPeer pid fun p => {p with timerNeedAnotherKeepalive := true})) :
    Keeps P (timersDataReceived pid) := by
  have source : timersDataReceived pid = (do
      if ← branch .timersDataReceivedRunning (← getDev).running then
        if ← branch .timersDataReceivedNotPending !((← getPeer pid).timerPending .sendKeepalive) then
          discard <| modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
        else modifyPeer pid fun p=>{p with timerNeedAnotherKeepalive:=true}) := by
    simp only [timersDataReceived,RxCredits.modifyPeer_source]
  rw [source]
  simp (config:={zeta:=false}) only [discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' first
    | with_reducible exact arm
    | with_reducible exact update
    | with_reducible exact getDev_rule P
    | with_reducible exact getPeer_rule P _
    | with_reducible exact branches _ _
    | with_reducible exact pure_rule P _
    | with_reducible apply bind_rule P
    | split
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Index.ReceiveCompletion.Rules
