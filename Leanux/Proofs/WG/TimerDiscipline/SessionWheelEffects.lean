import Leanux.Proofs.WG.TimerDiscipline.SessionWheelModel

/-! Pure refinement of the complete original arm effect to the selected zero-key slot and its zero-or-one enqueue. Other timer fields and the selected peer stamp are retained. The history lemma extracts an actual adjacent pair from the paired grammar. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

theorem placement_zero (entry : Campaign2.State) (d : Device) (pid : PeerId) (p : Peer)
    (device : entry.device=some d) (expires clk : UInt64) :
    WheelDelta entry (wheelPlacementView entry pid p .zeroKeyMaterial expires clk) pid p := by
  cases place : TimerWheel.place p .zeroKeyMaterial expires clk with
  | kept we =>
    simp only [wheelPlacementView,place]
    refine ⟨p.setTimer .zeroKeyMaterial (some expires),?_,rfl,?_,?_,Or.inl ⟨rfl,rfl⟩⟩
    · simp [device]
    · simp [Peer.timer,Peer.setTimer]
    · intro t other
      cases t <;> simp_all [Peer.timer,Peer.wheel,Peer.setTimer]
  | enqueued slot bucketExpiry =>
    simp only [wheelPlacementView,place]
    let we : WheelEntry := ⟨slot,bucketExpiry,entry.timerEnqueues+1⟩
    refine ⟨(p.setTimer .zeroKeyMaterial (some expires)).setWheel .zeroKeyMaterial (some we),
      ?_,rfl,?_,?_,Or.inr ⟨we,rfl,rfl,rfl⟩⟩
    · simp [device,we]
    · simp [Peer.timer,Peer.setTimer,Peer.setWheel]
    · intro t other
      cases t <;> simp_all [Peer.timer,Peer.wheel,Peer.setTimer,Peer.setWheel]

theorem arm_zero_delta (entry : Campaign2.Snapshot) (d : Device) (pid : PeerId) (p : Peer)
    (device : entry.wg.device=some d) (resident : d.peers[pid]?=some p)
    (final : Campaign2.State)
    (effect : peerTimerArmEffect entry pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS final) :
    WheelDelta entry.wg final pid p := by
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller,now,unit,_,_,effect⟩:=effect
    split at effect
    · subst final
      refine ⟨p,?_,rfl,?_,?_,Or.inl ⟨rfl,rfl⟩⟩
      · simp [recordedArmPrefixView,device,resident]
      · rename_i same
        rw [same]
        intro impossible
        cases impossible
      · intro t _
        exact ⟨rfl,rfl⟩
    · obtain ⟨clk,changed⟩:=effect
      rw [changed]
      let base := {recordedArmPrefixView entry.wg pid .zeroKeyMaterial now unit with timerClk:=some clk}
      have baseDevice : base.device=some d := device
      have placed := placement_zero base d pid p baseDevice (caller+ZERO_KEY_MATERIAL_TICKS.toUInt64) clk
      change WheelDelta entry.wg (wheelPlacementView base pid p .zeroKeyMaterial _ clk) pid p
      unfold WheelDelta at placed ⊢
      exact placed
  · subst final
    exact placement_zero entry.wg d pid p device _ _
theorem Paired.hook_origin {h : List Event} (paired : Paired h)
    (r : HookJournal.Receipt) (kind : r.hook=.sessionDerived)
    (member : Event.hook r∈h) :
    ∃ before s after, h=before++[.session s,.hook r]++after ∧ SessionDerivedLink s r := by
  induction paired with
  | nil => cases member
  | quiet quiet prior other ih =>
    rcases List.mem_append.mp member with old|fresh
    · obtain ⟨before,s,after,same,link⟩:=ih old
      exact ⟨before,s,after++[.hook quiet],by simp [same,List.append_assoc],link⟩
    · simp only [List.mem_singleton] at fresh
      cases fresh
      exact False.elim (other kind)
  | refused s prior notBegun ih =>
    rcases List.mem_append.mp member with old|fresh
    · obtain ⟨before,session,after,same,link⟩:=ih old
      exact ⟨before,session,after++[.session s],by simp [same,List.append_assoc],link⟩
    · simp only [List.mem_singleton] at fresh
      cases fresh
  | @derived history s fresh prior link ih =>
    rcases List.mem_append.mp member with old|new
    · obtain ⟨before,session,after,same,paired⟩:=ih old
      exact ⟨before,session,after++[.session s,.hook fresh],by simp [same,List.append_assoc],paired⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at new
      rcases new with impossible|same
      · cases impossible
      · have eq : r=fresh := Event.hook.inj same
        subst fresh
        exact ⟨history,s,[],by simp,link⟩

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
