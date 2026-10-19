import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentCanonical

/-! Wrapper phases are derived from exact successful original prefixes.
The deletion guard is never replaced by a whole-tree framing assumption. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver Points
set_option maxHeartbeats 600000

theorem normal_post {P : List Event→World→Prop} {Q : α→List Event→World→Prop}
    (checked : PrefixEnsures P Safe action Q) (before : P h w)
    (performed : runPrefix action w h=(.ok (value,v),last)) : Q value last v := by
  obtain ⟨_,_,_,post⟩ := checked w h before
  simpa only [performed] using post

theorem up_notifications_strong (enabled : Bool) : Strong (upNotificationsShape enabled) := by
  cases enabled with
  | false => trivial
  | true => exact ⟨CompleteProduct.routing _,fun _=>⟨CompleteProduct.routing _,fun _=>CompleteProduct.env_edit _⟩⟩

theorem up_finish_strong (ret : Int) : Strong (upFinishShape ret) :=
  ⟨CompleteProduct.ambient _,fun _=>⟨up_notifications_strong _,fun _=>True.intro⟩⟩

theorem up_active_strong (running : Bool) : Strong (upActiveShape running) := by
  cases running with
  | true => trivial
  | false => exact ⟨Points.up_strong,up_finish_strong⟩

theorem up_tail_strong (dev : Option Device) : Strong (upTailShape dev) := by
  cases dev with
  | none => trivial
  | some d => exact up_active_strong d.running

theorem up_strong : Strong upShape :=
  ⟨CompleteProduct.product_store _ (fun initial=>productGetWG_spec (·=initial)),
    fun saved=>up_tail_strong saved.dev⟩

theorem down_body_ordinary : Ordinary downBodyShape := by
  unfold downBodyShape
  repeat' first | (lifecycle_certificate_head Points.downShape; exact down_ordinary) | lifecycle_ordinary_steps

theorem down_active_ordinary (running : Bool) : Ordinary (downActiveShape running) := by
  cases running with
  | false => trivial
  | true => exact down_body_ordinary

theorem down_tail_ordinary (dev : Option Device) : Ordinary (downTailShape dev) := by
  cases dev with
  | none => trivial
  | some d => exact down_active_ordinary d.running

theorem down_ordinary : Ordinary downShape := ⟨True.intro,fun saved=>down_tail_ordinary saved.dev⟩

theorem delete_guards_ordinary : Ordinary deleteGuardsShape := by
  unfold deleteGuardsShape
  repeat' lifecycle_ordinary_steps

theorem delete_prefix_ordinary : Ordinary deletePrefixShape := by
  unfold deletePrefixShape
  repeat' first | (lifecycle_certificate_head Points.downShape; exact Points.down_ordinary) | lifecycle_ordinary_steps

theorem delete_tail_framed (absent : Bool) (before : RetiredPeer.Lifecycle.Packet.Environment.Ready h w) :
    Framed (deleteTailShape absent) w h := by
  cases absent with
  | true => exact before.1.1
  | false =>
    refine ⟨delete_prefix_ordinary.framed before.1.1,?_⟩
    intro ignored v last prefixRun
    have post := normal_post RetiredPeer.Lifecycle.Packet.Environment.prefix_checked before prefixRun
    have framed := destruct_framed ⟨post.1.1,post.2⟩
    exact ⟨framed,fun _ _ _ performed=>framed.normal performed⟩

theorem delete_framed (before : RetiredPeer.Lifecycle.Packet.Environment.Entry cs h w) :
    Framed deleteShape w h := by
  refine ⟨delete_guards_ordinary.framed before.1.1,?_⟩
  intro ignored u middle guards
  have ready := normal_post RetiredPeer.Lifecycle.Packet.Environment.guards_checked before guards
  refine ⟨ready.1.1,?_⟩
  intro saved v last read
  cases read
  exact delete_tail_framed _ ready

theorem original_up_framed (before : CompleteProduct.Carrier h w) : Framed originalUp w h :=
  Framed.source_mpr up_source (up_strong.framed before)

theorem original_down_framed (before : Account h w) : Framed originalDown w h :=
  Framed.source_mpr down_source (down_ordinary.framed before)

theorem original_delete_framed (before : RetiredPeer.Lifecycle.Packet.Environment.Entry cs h w) :
    Framed originalDelete w h := Framed.source_mpr delete_source (delete_framed before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
