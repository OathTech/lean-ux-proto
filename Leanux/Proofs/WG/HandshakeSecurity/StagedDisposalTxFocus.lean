import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalTxRelease
import Leanux.Proofs.WG.AuthenticatedEffects.CausalFocusSource

/-! Exact embedding of TX source factors into a larger journal. Existing
disposition events and lifetime accesses keep their order and stopped prefix. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

structure Ops.Appends (o : Ops E) : Prop where
  step : ∀ {α} (action : WG.M α), Logged.Appends (o.step action)
  access : ∀ {α} (action : MixedM α), Logged.Appends (o.access action)
  event : ∀ event, Logged.Appends (o.event event)
  enqueue : ∀ pid item, Logged.Appends (o.enqueue pid item)
  release : ∀ peer, Logged.Appends (o.release peer)

def Ops.focus (encode : E → F) (decode : F → Option E) (o : Ops E) : Ops F where
  step := fun action => focusPrefix encode decode (o.step action)
  access := fun action => focusPrefix encode decode (o.access action)
  event := fun event => focusPrefix encode decode (o.event event)
  enqueue := fun pid item => focusPrefix encode decode (o.enqueue pid item)
  release := fun peer => focusPrefix encode decode (o.release peer)

private theorem appends_emit (event : E) : Appends (emitPrefix event : PrefixM E Unit) :=
  fun _ _ => ⟨[event],rfl⟩

private theorem access_appends (action : MixedM α) : Appends (TxDisposition.nativeAccess action) :=
  Appends.focus _ _ _

private theorem enqueue_appends (pid : PeerId) (item : List SkbId) : Appends (TxDisposition.enqueue pid item) := by
  unfold TxDisposition.enqueue TxDisposition.enqueueCore
  repeat' first
    | with_reducible exact access_appends _
    | with_reducible exact Appends.focus _ _ _
    | with_reducible exact Appends.lift _
    | with_reducible exact appends_emit _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.bind
    | (maintenance_intro; try dsimp only)
    | maintenance_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)

theorem native_appends : Ops.Appends native where
  step := fun _ => Appends.lift _
  access := fun _ => Appends.focus _ _ _
  event := appends_emit
  enqueue := enqueue_appends
  release := fun _ => Appends.focus _ _ _

macro "disposal_tx_align " enc:ident dec:ident inv:ident h:ident : tactic => `(tactic| first
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.step $h _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.access $h _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.event $h _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.enqueue $h _ _)
  | with_reducible exact CausalFocus.native $enc $dec _ (Ops.Appends.release $h _)
  | (maintenance_head Pure.pure; exact CausalFocus.pure $enc $dec _)
  | (maintenance_head Bind.bind; apply CausalFocus.bind $enc $dec $inv)
  | (maintenance_head ite; apply CausalFocus.choice $enc $dec)
  | (maintenance_head ForIn.forIn; apply CausalFocus.loop $enc $dec $inv)
  | (maintenance_intro; try dsimp only)
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable (encode : E → F) (decode : F → Option E) (inverse : ∀ event, decode (encode event) = some event)
  (o : Ops E) (h : Ops.Appends o)

include inverse h in
private theorem publish_aligned (item : List SkbId) (state : PacketState) :
    CausalFocus.Aligned encode decode (publish (Ops.focus encode decode o) item state) (publish o item state) := by
  unfold publish
  simp only [Ops.focus]
  repeat' disposal_tx_align encode decode inverse h

include inverse h in
theorem publish_focus (item : List SkbId) (state : PacketState) :
    publish (Ops.focus encode decode o) item state = focusPrefix encode decode (publish o item state) :=
  (publish_aligned encode decode inverse o h item state).2

include inverse h in
theorem create_focus (pid : PeerId) (item : List SkbId) :
    create (Ops.focus encode decode o) pid item = focusPrefix encode decode (create o pid item) := by
  have aligned : CausalFocus.Aligned encode decode
      (create (Ops.focus encode decode o) pid item) (create o pid item) := by
    unfold create
    simp only [Ops.focus]
    repeat' first
      | exact publish_aligned encode decode inverse o h _ _
      | disposal_tx_align encode decode inverse h
  exact aligned.2

include inverse h in
theorem dispose_focus (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    dispose (Ops.focus encode decode o) pid item key = focusPrefix encode decode (dispose o pid item key) := by
  have aligned : CausalFocus.Aligned encode decode
      (dispose (Ops.focus encode decode o) pid item key) (dispose o pid item key) := by
    unfold dispose
    simp only [Ops.focus]
    repeat' disposal_tx_align encode decode inverse h
  exact aligned.2

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
