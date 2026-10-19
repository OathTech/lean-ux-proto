import Leanux.Proofs.WG.Index.ReceiveCompletionRulesSource
import Leanux.Proofs.WG.Progress.NativeSuffixSource

/-! Native record-suffix instances for actual receive completion. Remaining callback premises name the original operations; no totality or successful-activation conclusion is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Origins.HandshakeSources
namespace Completion
abbrev RulesKeeps (records : List HiddenRecord) {α : Type} (action : WG.M α) :=
  Index.ReceiveCompletion.Rules.Keeps (fun _ a=>Tail records a.hidden) action

theorem to_rules {α : Type} (records : List HiddenRecord) (action : WG.M α)
    (keep : NativeKeeps records action) : RulesKeeps records action :=
  native_statePrefix records action keep

theorem of_rules {α : Type} (records : List HiddenRecord) (action : WG.M α)
    (keep : RulesKeeps records action) : NativeKeeps records action := by
  intro g
  apply (hoare_iff_run _ _ _).mpr
  intro a out b pre run
  exact (Index.ReceiveCompletion.Rules.keeps_iff _).mp keep g a out.1 out.2 b pre run

theorem stats_retains (records : List HiddenRecord) (pid : PeerId) (len : Nat) :
    NativeKeeps records (updateRxStats pid len) := by
  unfold updateRxStats
  exact native_bind records _ _ (native_modifyDev records _) (fun _=>
    native_bind records _ _ (native_getPeer records pid) (fun _=>native_setPeer records pid _))

theorem dishonest_retains (records : List HiddenRecord) (why : Dishonest) :
    NativeKeeps records (WG.dishonest why) := native_modifyDev records _

theorem ecn_retains (records : List HiddenRecord) (protocol outer : Nat) (bytes : List UInt8) :
    NativeKeeps records (inetEcnDecapsulate protocol outer bytes) := by
  apply of_rules
  have branch_rule (decision : Decision) (value : Bool) :
      RulesKeeps records (branch decision value : WG.M Bool) :=
    to_rules records _ (native_branch records decision value)
  have ce4 (bytes : List UInt8) : RulesKeeps records (ipEcnSetCe bytes) := by
    unfold ipEcnSetCe
    apply Index.ReceiveCompletion.Rules.bind_rule _ _ _ (branch_rule _ _)
    intro b
    split <;> exact Index.ReceiveCompletion.Rules.pure_rule _ _
  have ect4 (bytes : List UInt8) : RulesKeeps records (ipEcnSetEct1 bytes) := by
    unfold ipEcnSetEct1
    apply Index.ReceiveCompletion.Rules.bind_rule _ _ _ (branch_rule _ _)
    intro b
    split <;> exact Index.ReceiveCompletion.Rules.pure_rule _ _
  have ce6 (bytes : List UInt8) : RulesKeeps records (ip6EcnSetCe bytes) := by
    unfold ip6EcnSetCe
    apply Index.ReceiveCompletion.Rules.bind_rule _ _ _ (branch_rule _ _)
    intro b
    split <;> exact Index.ReceiveCompletion.Rules.pure_rule _ _
  have ect6 (bytes : List UInt8) : RulesKeeps records (ip6EcnSetEct1 bytes) := by
    unfold ip6EcnSetEct1
    apply Index.ReceiveCompletion.Rules.bind_rule _ _ _ (branch_rule _ _)
    intro b
    split <;> exact Index.ReceiveCompletion.Rules.pure_rule _ _
  have setter (ce : Bool) (protocol : Nat) (bytes : List UInt8) :
      RulesKeeps records (inetEcnSet ce protocol bytes) := by
    unfold inetEcnSet
    repeat' first
      | with_reducible exact ce4 _
      | with_reducible exact ect4 _
      | with_reducible exact ce6 _
      | with_reducible exact ect6 _
      | with_reducible exact branch_rule _ _
      | with_reducible exact Index.ReceiveCompletion.Rules.invariant_rule _ _
      | with_reducible exact Index.ReceiveCompletion.Rules.pure_rule _ _
      | with_reducible apply Index.ReceiveCompletion.Rules.bind_rule
      | split
      | (with_reducible intro x; try dsimp only)
  unfold inetEcnDecapsulate
  repeat' first
    | with_reducible exact setter _ _ _
    | with_reducible exact branch_rule _ _
    | with_reducible exact Index.ReceiveCompletion.Rules.pure_rule _ _
    | with_reducible apply Index.ReceiveCompletion.Rules.bind_rule
    | split
    | (with_reducible intro x; try dsimp only)

theorem fresh_retains (records : List HiddenRecord) (pid : PeerId)
    (queued : NativeKeeps records (sendQueuedHandshakeInitiation pid false)) :
    NativeKeeps records (keepKeyFreshRx pid) := by
  apply of_rules
  apply Index.ReceiveCompletion.Rules.keepKeyFreshRx (fun _ a=>Tail records a.hidden) pid
  · exact fun decision value=>to_rules records _ (native_branch records decision value)
  · exact fun birthday=>to_rules records _ (native_expired records _ birthday _ _)
  · apply to_rules
    unfold modifyPeer
    exact native_bind records _ _ (native_getPeer records pid) (fun _=>native_setPeer records pid _)
  · exact to_rules records _ queued

theorem data_retains (records : List HiddenRecord) (pid : PeerId)
    (arm : NativeKeeps records
      (modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)) :
    NativeKeeps records (timersDataReceived pid) := by
  apply of_rules
  apply Index.ReceiveCompletion.Rules.dataReceived (fun _ a=>Tail records a.hidden) pid
  · exact fun decision value=>to_rules records _ (native_branch records decision value)
  · exact to_rules records _ arm
  · apply to_rules
    unfold modifyPeer
    exact native_bind records _ _ (native_getPeer records pid) (fun _=>native_setPeer records pid _)

theorem prepare_retains (records : List HiddenRecord) (pid : PeerId) (pkt : RxPacket)
    (fresh : NativeKeeps records (keepKeyFreshRx pid))
    (received : NativeKeeps records (timersAnyAuthenticatedPacketReceived pid))
    (traversal : NativeKeeps records (timersTraversal pid))
    (data : NativeKeeps records (timersDataReceived pid)) :
    NativeKeeps records (RxCredits.prepareRest pid pkt) := by
  apply of_rules
  exact Index.ReceiveCompletion.Rules.prepareRest (fun _ a=>Tail records a.hidden) pid pkt
    (fun decision value=>to_rules records _ (native_branch records decision value))
    (to_rules records _ fresh) (to_rules records _ received) (to_rules records _ traversal)
    (to_rules records _ data) (fun len=>to_rules records _ (stats_retains records pid len))
    (fun why=>to_rules records _ (dishonest_retains records why))
    (fun protocol ds bytes=>to_rules records _ (ecn_retains records protocol ds bytes))

theorem finish_retains (records : List HiddenRecord) (pid : PeerId) (ready : Packets.RxReady)
    (lookup : NativeKeeps records (RxBorrow.source ready.protocol ready.bytes)) :
    NativeKeeps records (Packets.rxFinish pid ready) := by
  apply of_rules
  exact Index.ReceiveCompletion.Rules.rxFinish (fun _ a=>Tail records a.hidden) pid ready
    (fun decision value=>to_rules records _ (native_branch records decision value))
    (to_rules records _ lookup) (to_rules records _ (dishonest_retains records .peer))
    (to_rules records _ (stats_retains records pid _))

theorem after_retains (records : List HiddenRecord)
    (pid : PeerId) (pkt : RxPacket) (confirmed : Bool)
    (complete : NativeKeeps records (timersHandshakeComplete pid .walltimeLastHandshakeData))
    (staged : NativeKeeps records (sendStagedPackets pid))
    (prepare : NativeKeeps records (RxCredits.prepareRest pid pkt))
    (finish : ∀ ready, NativeKeeps records (Packets.rxFinish pid ready)) :
    NativeKeeps records (ConsumeConfirmation.afterConfirmation pid pkt confirmed) := by
  apply of_rules
  exact Index.ReceiveCompletion.Rules.afterConfirmation (fun _ a=>Tail records a.hidden)
    pid pkt confirmed
    (fun decision value=>to_rules records _ (native_branch records decision value))
    (to_rules records _ complete) (to_rules records _ staged) (to_rules records _ prepare)
    (fun ready=>to_rules records _ (finish ready))
end Completion
end Leanux.Proofs.WG.Progress.RecordSuffix
