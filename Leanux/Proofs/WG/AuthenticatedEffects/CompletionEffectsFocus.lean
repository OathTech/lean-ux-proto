import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsNative
import Leanux.Proofs.WG.AuthenticatedEffects.CausalFocusSource

/-! Focusing the complete original TX observer distributes through its actual
source callbacks. This permits exact projection to an already combined journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Appends (o : Ops E) : Prop where
  step : ∀ {α} (a : WG.M α), Leanux.Proofs.Logged.Appends (o.step a)
  peer : ∀ pid, Leanux.Proofs.Logged.Appends (o.peer pid)
  modifyPeer : ∀ pid f, Leanux.Proofs.Logged.Appends (o.modifyPeer pid f)
  packet : ∀ id, Leanux.Proofs.Logged.Appends (o.packet id)
  completion : ∀ pid item, Leanux.Proofs.Logged.Appends (o.completion pid item)
  send : ∀ pid id packet, Leanux.Proofs.Logged.Appends (o.send pid id packet)
  drop : ∀ pid item, Leanux.Proofs.Logged.Appends (o.drop pid item)
  dispose : ∀ pid item key, Leanux.Proofs.Logged.Appends (o.dispose pid item key)
  traversal : ∀ pid, Leanux.Proofs.Logged.Appends (o.traversal pid)
  sent : ∀ pid, Leanux.Proofs.Logged.Appends (o.sent pid)
  dataSent : ∀ pid, Leanux.Proofs.Logged.Appends (o.dataSent pid)
  fresh : ∀ pid, Leanux.Proofs.Logged.Appends (o.fresh pid)

theorem native_appends : Ops.Appends native where
  step := fun _ => Appends.lift _
  peer := fun _ => Appends.focus _ _ _
  modifyPeer := fun _ _ => Appends.focus _ _ _
  packet := fun _ => Appends.focus _ _ _
  completion := fun _ _ => fun _ _ => ⟨[_],rfl⟩
  send := fun _ _ _ =>
    (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsNative.«0».Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects.send_appends) _ _ _
  drop := fun _ _ => Appends.focus _ _ _
  dispose := fun _ _ _ => Appends.focus _ _ _
  traversal := fun _ => Appends.focus _ _ _
  sent := fun _ => Appends.focus _ _ _
  dataSent := fun _ => Appends.focus _ _ _
  fresh := fun _ => Appends.focus _ _ _

macro "completion_align " enc:ident dec:ident inv:ident : tactic => `(tactic| first
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.step native_appends _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.peer native_appends _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.modifyPeer native_appends _ _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.packet native_appends _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.completion native_appends _ _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.send native_appends _ _ _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.drop native_appends _ _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.dispose native_appends _ _ _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.traversal native_appends _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.sent native_appends _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.dataSent native_appends _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.fresh native_appends _)
  | (maintenance_head captureObserved; apply CausalFocus.capture $enc $dec)
  | (maintenance_head Pure.pure; exact CausalFocus.pure $enc $dec _)
  | (maintenance_head Bind.bind; apply CausalFocus.bind $enc $dec $inv)
  | (maintenance_head ite; apply CausalFocus.choice $enc $dec)
  | (maintenance_head ForIn.forIn; apply CausalFocus.loop $enc $dec $inv)
  | (maintenance_intro; try dsimp only)
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable (encode : Completion.Event → E) (decode : E → Option Completion.Event)
  (inverse : ∀ event, decode (encode event) = some event)
include inverse

private theorem complete_aligned (pid : PeerId) (item : List SkbId) :
    CausalFocus.Aligned encode decode (completeWith (focused encode decode) pid item)
      (completeWith native pid item) := by
  unfold completeWith TxDisposition.andObs
  simp only [focused]
  repeat' completion_align encode decode inverse

private theorem body_aligned (pid : PeerId) (first : Option (List SkbId)) :
    CausalFocus.Aligned encode decode (bodyWith (focused encode decode) pid first)
      (bodyWith native pid first) := by
  unfold bodyWith TxDisposition.andObs
  simp only [focused]
  repeat' first
    | (maintenance_head completeWith; exact complete_aligned encode decode inverse _ _)
    | completion_align encode decode inverse

theorem step_focus (pid : PeerId) :
    stepWith (focused encode decode) pid = focusPrefix encode decode (Completion.step pid) := by
  have aligned : CausalFocus.Aligned encode decode (stepWith (focused encode decode) pid)
      (stepWith native pid) := by
    unfold stepWith
    simp only [focused]
    repeat' first
      | (maintenance_head bodyWith; exact body_aligned encode decode inverse _ _)
      | completion_align encode decode inverse
  exact aligned.2

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
