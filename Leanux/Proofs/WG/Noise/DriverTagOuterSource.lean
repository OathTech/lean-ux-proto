import Leanux.Proofs.WG.Noise.DriverTagOuterFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Outer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Leanux.Proofs.WG.Configuration

theorem socketCallOn_tag_variant (entry : TagMap) (fd : Nat) (body : ProductObs Int)
    (hb : PrefixPreserves (StateInv entry) ValidHistory body) :
    PrefixPreserves (StateInv entry) ValidHistory
      (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply PrefixPreserves.bind (lift_fs entry (fdget fd))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure (safe entry) _
  · intro _
    exact hb.bind (fun ret => (lift_fs entry (fdput f)).bind
      (fun _ => PrefixPreserves.pure (safe entry) ret))

theorem netlinkRequest_tag_variant (entry : TagMap) (body : ProductObs Int)
    (hb : PrefixPreserves (StateInv entry) ValidHistory body) :
    PrefixPreserves (StateInv entry) ValidHistory
      (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply PrefixPreserves.bind
    (socketCallOn_tag_variant entry _ _ ((lift_ambient entry (AmbientM.skipCut allocCuts)).bind
      (fun _ => hb.bind (fun ret => (lift_ambient entry (AmbientM.skipCut allocCuts)).bind
        (fun _ => PrefixPreserves.pure (safe entry) ret)))))
  intro ret
  exact (socketCallOn_tag_variant entry _ _ (PrefixPreserves.pure (safe entry) 0)).bind
    (fun _ => PrefixPreserves.pure (safe entry) ret)

macro "driver_outer_step " entry:term : tactic => `(tactic| first
  | (current_env_at unsupported; exact lift_ambient $entry (AmbientM.unsupported _))
  | (current_env_at skipCut; exact lift_ambient $entry (AmbientM.skipCut _))
  | (current_env_at liftPrefix; first
      | exact lift_fs $entry _
      | exact lift_task $entry _
      | exact lift_ambient $entry _
      | exact lift_seccomp $entry _
      | exact lift_get $entry
      | exact lift_modify $entry _ (fun _ => rfl))
  | (current_env_at Pure.pure; exact PrefixPreserves.pure (safe $entry) _)
  | (current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (current_env_at ite; apply PrefixPreserves.ite)
  | (current_env_at dite; split)
  | (maintenance_intro; try dsimp only)
  | current_env_match)

theorem rtnetlinkRequest_tag_variant (entry : TagMap) (body : ProductObs Int)
    (hb : PrefixPreserves (StateInv entry) ValidHistory body) :
    PrefixPreserves (StateInv entry) ValidHistory
      (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (current_env_at socketCallOnWith; apply socketCallOn_tag_variant entry)
    | driver_outer_step entry


theorem socketCallOn_erases (fd : Nat) (body : ProductObs Int) (action : Leanux.M Int)
    (hb : ErasesPrefix body action) :
    ErasesPrefix (socketCallOnWith (fun {_} a => liftPrefix a) fd body)
      (Leanux.socketCallOn fd action) := by
  rw [socketCallOn_factor]
  unfold socketCallOnWith
  repeat' first
    | exact hb
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem netlinkRequest_erases (body : ProductObs Int) (action : Leanux.M Int)
    (hb : ErasesPrefix body action) :
    ErasesPrefix (netlinkRequestWith (fun {_} a => liftPrefix a) body)
      (Leanux.netlinkRequest action) := by
  rw [netlinkRequest_factor]
  unfold netlinkRequestWith socketCallOnWith
  repeat' first
    | exact hb
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem rtnetlinkRequest_erases (body : ProductObs Int) (action : Leanux.M Int)
    (hb : ErasesPrefix body action) :
    ErasesPrefix (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body)
      (Leanux.rtnetlinkRequest action) := by
  rw [rtnetlinkRequest_factor]
  unfold rtnetlinkRequestWith socketCallOnWith
  repeat' first
    | exact hb
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | (split <;> try contradiction)

end Leanux.Proofs.WG.Noise.DriverTags.Outer

