import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueFrames
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerSource
import Leanux.Proofs.WG.Queues.DecryptCarrier

/-! Exact read/pop transport at the shared native handshake-worker source.
The callback receives validity from the actual occupied ring slot. Its safe
history contract applies on both success and Stop after that pop. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

abbrev StateInv (Valid : List UInt8 → Prop) (Safe : List E → Prop)
    (h : List E) (w : WGWorld) (_ : Ambient) : Prop := Inv Valid w ∧ Safe h

theorem frame {action : WG.M α} (same : SameView view action) : Preserves (Inv Valid) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact transport ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run) before

theorem state_frame (Valid : List UInt8 → Prop) (Safe : List E → Prop)
    {action : WG.M α} (same : SameView view action) :
    StatePrefixPreserves (StateInv Valid Safe) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before=>before.2)
  intro h w a value v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (frame same) w a value v b before.1 run,before.2⟩

theorem getDev_checked (Valid : List UInt8 → Prop) (Safe : List E → Prop) :
    StatePrefixEnsures (StateInv Valid Safe) Safe (liftWGPrefix getDev)
      (fun d h w a=>StateInv Valid Safe h w a ∧ w.dev=some d) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before=>before.2)
  intro h w a value v b before run
  obtain ⟨rfl,rfl,device⟩:=RxCredits.DecryptCarrier.getDev_current a b run
  exact ⟨before,device⟩

theorem pop_checked (Valid : List UInt8 → Prop) (Safe : List E → Prop)
    (d : Device) (msg : List UInt8) (src : SkbSource) (ring : PtrRing (List UInt8 × SkbSource))
    (poll : d.handshakeQueue.consume=(some (msg,src),ring)) :
    StatePrefixEnsures (fun h w a=>StateInv Valid Safe h w a ∧ w.dev=some d) Safe
      (liftWGPrefix (modifyDev fun current=>{current with handshakeQueue:=ring}))
      (fun _ h w a=>StateInv Valid Safe h w a ∧ Valid msg) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before=>before.1.2)
  intro h w a value v b before run
  have valid:=popped before.1.1 before.2 poll
  have residual : Ring (fun entry=>Valid entry.1) ring := by
    simpa only [poll] using (consumed _ _ (before.1.1 d before.2)).1
  have equal : (((),{w with dev:=some {d with handshakeQueue:=ring}}),a)=((value,v),b) := by
    simpa [modifyDev,before.2] using run
  cases equal
  refine ⟨⟨?_,before.1.2⟩,valid⟩
  intro current device
  cases device
  exact residual

private theorem branch_checked (P : List E → WGWorld → Ambient → Prop) (Safe : List E → Prop)
    (safe : ∀h w a,P h w a→Safe h) (decision : Decision) (value : Bool)
    (ambient_free : ∀h w a b,P h w a→P h w b) :
    StatePrefixPreserves P Safe (liftWGPrefix (branch decision value)) := by
  apply StatePrefixEnsures.lift _ safe
  intro h w a result v b before run
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch decision value) (fun current=>current=w)) w a result v b rfl run
  exact same ▸ ambient_free h w a b before

theorem worker (Valid : List UInt8 → Prop) (Safe : List E → Prop)
    (receive : List UInt8 → SkbSource → WGPrefix E Unit)
    (receives : ∀msg src,StatePrefixEnsures
      (fun h w a=>StateInv Valid Safe h w a ∧ Valid msg) Safe (receive msg src)
      (fun _=>StateInv Valid Safe)) :
    StatePrefixPreserves (StateInv Valid Safe) Safe
      (AuthenticatedEffects.HandshakeWorker.workerWith receive) := by
  unfold AuthenticatedEffects.HandshakeWorker.workerWith
  apply StatePrefixEnsures.bind (getDev_checked Valid Safe)
  intro d
  cases poll : d.handshakeQueue.consume with
  | mk item ring=>
    cases item with
    | none=>
      apply StatePrefixEnsures.bind (branch_checked _ _ (fun _ _ _ before=>before.1.2) _ _
        (fun _ _ _ _ before=>before))
      intro _
      exact StatePrefixEnsures.pure false (fun _ _ _ before=>before.1.2)
        (fun _ _ _ before=>before.1)
    | some entry=>
      obtain ⟨msg,src⟩:=entry
      apply StatePrefixEnsures.bind (branch_checked _ _ (fun _ _ _ before=>before.1.2) _ _
        (fun _ _ _ _ before=>before))
      intro _
      apply StatePrefixEnsures.bind (pop_checked Valid Safe d msg src ring poll)
      intro _
      apply StatePrefixEnsures.bind (receives msg src)
      intro _
      apply StatePrefixEnsures.bind (state_frame Valid Safe
        (modify (fun d=>{d with handshakeQueueLen:=d.handshakeQueueLen-1}) (fun _=>rfl)))
      intro _
      exact StatePrefixEnsures.pure true (fun _ _ _ before=>before.2) (fun _ _ _ before=>before)

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
