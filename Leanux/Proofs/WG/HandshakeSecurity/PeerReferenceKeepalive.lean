import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceStaging

/-! A saved peer record carries its positive count through keepalive allocation
choices. The source uses the same staging callback as packet sends. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem keepalive (pid : PeerId) : Observed (E := E) (Driver.keepaliveObserved EntrySource.hooks (E := E) pid) := by
  rw [Driver.keepalive_native _ rfl]
  unfold Driver.keepaliveInline
  let Saved := fun (p : Peer) h w (_ : Ambient) => StateInv (E := E) h w ∧ 0 < p.refcount
  have read : StatePrefixEnsures (fun h w _ => StateInv (E := E) h w) (Safe (E := E)) (liftWGPrefix (getPeer pid)) Saved := by
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
    intro h w a p v b hi run
    obtain ⟨positive,count⟩ := (hoare_iff_run_ambient _ _ _).mp (read_saved pid) w a p v b hi.2 run
    exact ⟨⟨hi.1,positive⟩,count⟩
  have effect (p : Peer) {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (Saved p) (Safe (E := E)) (liftWGPrefix (monadLift a : WG.M α)) := by
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1)
    intro h w b x v c hi run
    exact (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient a (fun w => StateInv (E := E) h w ∧ 0 < p.refcount))
      w b x v c hi run
  have finish (p : Peer) {α : Type} {action : WGPrefix E α} (checked : Observed (E := E) action) :
      StatePrefixEnsures (Saved p) (Safe (E := E)) action (fun _ h w _ => StateInv (E := E) h w) :=
    checked.consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)
  apply StatePrefixEnsures.bind read
  intro p
  apply StatePrefixEnsures.bind (effect p _)
  intro empty
  split
  · apply StatePrefixEnsures.bind (effect p _)
    intro allocated
    apply StatePrefixEnsures.bind (effect p _)
    intro failed
    split
    · exact finish p (pure ())
    · apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
        (P := Saved p) (Q := fun _ => Saved p) getDev (fun _ _ _ hi => hi.1.1) ?_)
      · intro d
        apply StatePrefixEnsures.bind (StatePrefixEnsures.lift
          (P := Saved p) (Q := fun _ h w _ => StateInv (E := E) h w)
          (setPeer pid {p with staged := p.staged ++ [{mtu := d.mtu}]})
          (fun _ _ _ hi => hi.1.1) ?_)
        · intro _
          exact staging pid
        · intro h w a result v b hi run
          exact ⟨hi.1.1,(hoare_iff_run_ambient _ _ _).mp
            (write_positive pid {p with staged := p.staged ++ [{mtu := d.mtu}]} hi.2) w a result v b hi.1.2 run⟩
      · intro h w a d v b hi run
        have kept := (hoare_iff_run_ambient _ _ _).mp (store getDev_sameWGStore) w a d v b hi.1.2 run
        exact ⟨⟨hi.1.1,kept⟩,hi.2⟩
  · exact finish p (staging pid)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
