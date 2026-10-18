import Leanux.Proofs.WG.RetirementSecurity.TransmitEntryFrames

/-! The destination lookup's positive peer borrow is carried through native
selection and staging. Its final payment cannot delete the peer while key
holders remain; no independent peer-release precondition is introduced. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Std.Do
open Queues.RxCredits StagingOccurrences
namespace TransmitEntry

theorem joined {action : WG.M α} (left : Hoare action P Q) (right : Hoare action R S) :
    Hoare action (fun w => P w ∧ R w) (fun result w => Q result w ∧ S result w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp left w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp right w a result v b before.2 run⟩

abbrev Pending (temporary : Credits.Ledger) (initial : WGWorld) (peer : Option PeerId) (w : WGWorld) :=
  Held temporary w ∧ XmitPending initial peer w
abbrev Closed (temporary : Credits.Ledger) (initial : WGWorld) (w : WGWorld) :=
  Held temporary w ∧ XmitClosed initial w
abbrev Selected (temporary : Credits.Ledger) (initial : WGWorld)
    (result : Except Int (PeerId × List WG.Packet)) (w : WGWorld) :=
  Held temporary w ∧ SelectedXmit initial result w

theorem pending_ready (pending : XmitPending initial (some pid) w) : PeerReleaseReady pid w := by
  obtain ⟨o,slot,positive,delta,step⟩ := pending.2
  have budget := step.count o
  simp only [List.count_cons_self,List.count_nil,Nat.add_zero] at budget
  have plenty : 1 < RxCredits.balance w o := by omega
  cases resident : RxCredits.resident w o with
  | none => simp [RxCredits.balance,resident] at plenty
  | some p =>
    obtain ⟨d,device,_,stored,_⟩ := resident_fields resident
    have count : 1 < p.refcount := by simpa [RxCredits.balance,resident] using plenty
    intro q found final
    have same : q = p := by
      simpa [peerAt,device,←slot,stored] using found.symm
    subst q
    omega

theorem repay_keys (account : HolderAccount temporary w) (pending : XmitPending initial peer w)
    (a b : Ambient) (run : ((peerPut peer).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  cases peer with
  | none => cases run; exact account
  | some pid => exact account.peer_put (pending_ready pending) a b run

theorem repay (initial : WGWorld) (peer : Option PeerId) :
    Hoare (peerPut peer) (Pending temporary initial peer) (fun _ => Closed temporary initial) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact ⟨⟨repay_keys before.1.1 before.2 a b run,
    (hoare_iff_run_ambient _ _ _).mp (geometry_bound (peer_put_geometry peer)) w a () v b before.1.2 run⟩,
    (hoare_iff_run_ambient _ _ _).mp (pending_repay initial peer) w a () v b before.2 run⟩

theorem pending_frame {action : WG.M α} (held : Preserves (Held temporary) action)
    (reply : SameView replyView action) (initial : WGWorld) (peer : Option PeerId) :
    Preserves (Pending temporary initial peer) action :=
  joined held (RxCredits.pending_frame (project := id) reply initial peer)

theorem closed_frame {action : WG.M α} (held : Preserves (Held temporary) action)
    (reply : SameView replyView action) (initial : WGWorld) :
    Preserves (Closed temporary initial) action :=
  joined held (RxCredits.closed_frame (project := id) reply initial)

theorem select (initial : WGWorld) (family : Nat) (ps : List WG.Packet) (mtu : Nat) (peer : Option PeerId) :
    Hoare (Packets.txSelect family ps mtu peer) (Pending temporary initial peer)
      (fun result => Selected temporary initial result) := by
  have branch_rule {α : Type} (d : Decision) (value : Bool) (f : Bool → WG.M α)
      (P : WGWorld → Prop) (Q : α → WGWorld → Prop) (hf : Hoare (f value) P Q) :
      Hoare (branch d value >>= f) P Q := by
    apply hoare_bind _ _ (branch_predicate_native P d value)
    intro result
    apply (hoare_iff_run_ambient _ _ _).mpr
    rintro w ambient x v ambient' ⟨rfl,hi⟩ hr
    exact (hoare_iff_run_ambient _ _ _).mp hf w ambient x v ambient' hi hr
  have getter (P : WGWorld → Prop) (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hi hr
    exact (getPeer_normal pid w v p ambient ambient' hr).1 ▸ hi
  have errors := fun ret => closed_frame (temporary := temporary) (error family (ps.head?.getD {bytes := []}) ret)
    (txError_reply family (ps.head?.getD {bytes := []}) ret) initial
  cases peer with
  | none =>
    have body : Hoare (Packets.txSelect family ps mtu none) (Closed temporary initial)
        (fun result => Selected temporary initial result) := by
      unfold Packets.txSelect
      apply branch_rule
      simp only [Option.isNone_none,ite_true]
      material_lower
      repeat' first
        | unfold Preserves
        | (index_material_head Packets.txError; exact errors _)
        | rx_stack_step
        | rx_stack_return
        | material_component
        | material_join
        | material_join_use
        | material_intro
        | (index_material_head ite; split)
        | material_reduce
        | material_match
    exact hoare_consequence body (fun _ h => ⟨h.1,h.2.2,h.2.1⟩) (fun _ _ h => h)
  | some pid =>
    unfold Packets.txSelect
    apply branch_rule
    simp only [Option.isNone_some,Bool.false_eq_true,ite_false]
    unfold WG.andM envOk
    material_lower
    repeat' first
      | unfold Preserves
      | (rx_stack_bind_head peerPut
         apply hoare_bind _ _ (repay initial (some pid))
         intro x)
      | (index_material_head Packets.txError; exact errors _)
      | (index_material_head Lifetimes.xmitTrim
         exact pending_frame (trim pid)
           (reply_views (project := id) (xmitTrim_protect pid) (xmitTrim_keyView pid)) initial (some pid))
      | (index_material_head Packets.txWalk
         exact pending_frame (store (txWalk_kernel ps mtu []))
           (reply_kernel (project := id) (txWalk_kernel ps mtu [])) initial (some pid))
      | (index_material_head getPeer; exact getter _ _)
      | rx_stack_step
      | rx_stack_return
      | material_component
      | material_join
      | material_join_use
      | material_intro
      | (index_material_head ite; split)
      | material_reduce
      | material_match
      | contradiction

end TransmitEntry
end Leanux.Proofs.WG.RetirementSecurity
