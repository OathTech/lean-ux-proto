import Leanux.Proofs.WG.Config.GetterScalarModel
import Leanux.Proofs.WG.Noise.ClearFrames
import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims
import Leanux.Proofs.WG.Config.PeerDump

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline
theorem write_values (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]?=some p) (same : GetterScalar.cell q=GetterScalar.cell p) :
    values (some {d with peers:=d.peers.insert pid q})=values (some d) := by
  funext target
  by_cases eq:target=pid
  · subst target
    simp only [values,Option.bind_some,Std.TreeMap.getElem?_insert_self,resident,Option.map_some,same]
  · simp [values,Std.TreeMap.getElem?_insert,Ne.symm eq]

theorem clearRun_values {pid : PeerId} {d final : Device} {slots : List ClearSlot}
    (steps : ClearRun pid d slots final) : values (some final)=values (some d) := by
  induction steps with
  | nil=>rfl
  | cons d slot p middle final rest resident put tail ih=>
    refine ih.trans ?_
    have unchanged : values (some middle)=values (some (clearWrite d pid slot p)) := by
      funext target
      simp only [values,Option.bind_some,clearPut_peers put]
    rw [unchanged]
    exact write_values d pid p (slot.clear p) resident (by cases slot <;> rfl)

theorem wheel_values (entry : Campaign2.State) (d : Device) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64)
    (device : entry.device=some d) (resident : d.peers[pid]?=some p) :
    values (wheelPlacementView entry pid p timer expires clk).device=values entry.device := by
  unfold wheelPlacementView
  split
  all_goals
    simp only [device,Option.map_some]
    exact write_values d pid p _ resident (by cases timer <;> rfl)

theorem arm_values (entry : Campaign2.Snapshot) (d : Device) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (delay : Nat) (final : Campaign2.State)
    (device : entry.wg.device=some d) (resident : d.peers[pid]?=some p)
    (effect : peerTimerArmEffect entry pid p timer delay final) :
    values final.device=values entry.wg.device := by
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller,now,unit,_,_,effect⟩:=effect
    split at effect
    · rw [effect];rfl
    · obtain ⟨clk,effect⟩:=effect
      rw [effect]
      exact wheel_values _ d pid p timer _ clk device resident
  · rw [effect]
    exact wheel_values entry.wg d pid p timer _ _ device resident

theorem cell_fields (p q : Peer) (same : GetterScalar.cell p=GetterScalar.cell q) :
    p.internalId=q.internalId ∧ p.presharedKey=q.presharedKey ∧
    p.persistentKeepaliveInterval=q.persistentKeepaliveInterval ∧
    p.endpoint.map TimerDiscipline.socketEndpoint=q.endpoint.map TimerDiscipline.socketEndpoint := by
  simpa only [GetterScalar.cell,Prod.mk.injEq] using same

theorem normalized_dump (p : Peer) :
    peerFixedAttrs {p with endpoint:=p.endpoint.map TimerDiscipline.socketEndpoint}=
      peerFixedAttrs p := by
  cases endpoint:p.endpoint with
  | none=>simp only [peerFixedAttrs,endpoint,Option.map_none]
  | some e=>
    simp only [peerFixedAttrs,endpoint,Option.map_some,TimerDiscipline.socketEndpoint]

theorem cell_fromFull (p : Peer) : cell p=fromFull (PeerScalarRetention.cell p) := rfl

theorem observation_fromFull (s : Campaign2.Snapshot) (pid : PeerId) :
    observation s pid=(PeerScalarRetention.observation s pid).map fromFull := by
  simp only [observation,values,PeerScalarRetention.observation,PeerScalarRetention.peerValues,
    Option.map_map,Function.comp_def]
  rfl

end Leanux.Proofs.WG.Config.GetterScalar
