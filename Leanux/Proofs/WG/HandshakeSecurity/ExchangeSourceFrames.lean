import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1Frames

/-! Source-carrier transport is separate from native frame assumptions.
Saved writes carry the tag actually read by the native getter. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem StateInv.safe {h : List Event} {w : WGWorld} (hi : StateInv h w) : Safe h :=
  ⟨hi.choose,hi.choose_spec.1⟩

theorem frame_tag (h : List Event) (action : WG.M α) (same : H1TagSame action) :
    Framing.Preserves (StateInv h) action := by
  apply frame h action
  intro w v a b result run pid tag found _
  rw [← (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run]
  exact found

theorem frame_store (h : List Event) (action : WG.M α) (same : SameWGStore action) :
    Framing.Preserves (StateInv h) action :=
  frame_tag h action (same.of_factor
    (fun s : WGStoreView => fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.handshakeState)
    handshakeTagAt (fun _ => rfl))

theorem lift (action : WG.M α) (keeps : ∀ h, Framing.Preserves (StateInv h) action) :
    Preserves (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ hi => hi.safe)
    (fun h w a result v b hi run => (hoare_iff_run_ambient _ _ _).mp (keeps h) w a result v b hi run)

theorem lift_tag (action : WG.M α) (same : H1TagSame action) : Preserves (liftWGPrefix action) :=
  lift action (fun h => frame_tag h action same)

theorem pure (value : α) : Preserves (Pure.pure value : WGPrefix Event α) :=
  StatePrefixEnsures.pure value (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)

theorem ambient (action : AmbientM α) : Preserves (liftWGPrefix (monadLift action : WG.M α)) :=
  lift _ (fun h => hoare_liftAmbient action (StateInv h))

theorem conditional (condition : Prop) [Decidable condition]
    (a b : WGPrefix Event α) (ha : Preserves a) (hb : Preserves b) :
    Preserves (if condition then a else b) := by
  by_cases chosen : condition <;> simp only [chosen,↓reduceIte] <;> assumption

def Saved (pid : PeerId) (p : Peer) (h : List Event) (w : WGWorld) : Prop :=
  StateInv h w ∧ handshakeTagAt w pid = some p.handshakeState

theorem read_saved (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => StateInv h w) Safe (liftWGPrefix (getPeer pid))
      (fun p h w _ => Saved pid p h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
  intro h w a p v b hi run
  obtain ⟨rfl,_,d,device,resident⟩ := getPeer_normal pid w v p a b run
  exact ⟨hi,by simp [handshakeTagAt,device,resident]⟩

theorem saved_ambient (pid : PeerId) (p : Peer) (action : AmbientM α) :
    StatePrefixPreserves (fun h w _ => Saved pid p h w) Safe
      (liftWGPrefix (monadLift action : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.safe)
  intro h w a result v b hi run
  exact (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (Saved pid p h))
    w a result v b hi run

theorem saved_tag (pid : PeerId) (p : Peer) (action : WG.M α)
    (same : H1TagSame action) :
    StatePrefixPreserves (fun h w _ => Saved pid p h w) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.safe)
  intro h w a result v b hi run
  have tags := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (frame_tag h action same) w a result v b hi.1 run,?_⟩
  exact (congrFun tags pid).trans hi.2

theorem saved_pure (pid : PeerId) (p : Peer) (value : α) :
    StatePrefixPreserves (fun h w _ => Saved pid p h w) Safe
      (Pure.pure value : WGPrefix Event α) :=
  StatePrefixEnsures.pure value (fun _ _ _ hi => hi.1.safe) (fun _ _ _ hi => hi)

theorem write_saved (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (tag : (f p).handshakeState = p.handshakeState) :
    StatePrefixEnsures (fun h w _ => Saved pid p h w) Safe (liftWGPrefix (setPeer pid (f p)))
      (fun _ h w _ => StateInv h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.safe)
  intro h w a result v b hi run
  cases run
  apply retained hi.1
  intro target value found _
  cases device : w.dev with
  | none => simp [handshakeTagAt,device] at found
  | some d =>
    by_cases equal : pid = target
    · subst target
      have valueEq : (f p).handshakeState = value := by simpa [handshakeTagAt,device] using found
      exact hi.2.trans (congrArg some (tag.symm.trans valueEq))
    · simpa [handshakeTagAt,device,Std.TreeMap.getElem?_insert,equal] using found

theorem update_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WGPrefix Event α)
    (same : ∀ p, (f p).handshakeState = p.handshakeState)
    (tail : ∀ u, Preserves (next u)) :
    Preserves (liftWGPrefix (getPeer pid) >>= fun p => liftWGPrefix (setPeer pid (f p)) >>= next) :=
  StatePrefixEnsures.bind (read_saved pid) (fun p => StatePrefixEnsures.bind
    (write_saved pid p f (same p)) tail)

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
