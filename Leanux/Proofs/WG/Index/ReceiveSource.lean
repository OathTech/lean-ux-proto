import Leanux.Proofs.WG.Index.ReceiveFrames
import Leanux.Proofs.WG.Index.ConsumeSource
import Leanux.Proofs.WG.Index.ResponseSource
import Leanux.Proofs.WG.Index.StagedSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The actual post-load body retains lookup, installation and release. -/
theorem receivePacketBody_tables (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    Ensures (receivePacketBody msg src underLoad) TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α)
      TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
  have hread (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g ambient result final after pre run).1
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  unfold receivePacketBody WG.andM WG.orM
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | with_reducible exact hstop _
    | with_reducible exact hread _
    | with_reducible exact consumeInitiation_tables _
    | with_reducible exact consumeResponse_tables _
    | with_reducible exact sendHandshakeResponse_tables _
    | with_reducible exact sendKeepalive_tables _
    | with_reducible exact (ensures_iff _ _ _).mpr (beginSession_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (cookieValidatePacket_tables _ _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (sendHandshakeCookie_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeerEndpointFromSkb_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (timersSessionDerived_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (timersHandshakeComplete_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (timersAnyAuthenticatedPacketReceived_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (traversal_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerPut_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (receiveStats_tables _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (with_reducible refine hif _ _ _ ?_ ?_)
    | split

/-- Compose the actual load prefix and packet body, preserving all Stops. -/
theorem receiveHandshakePacket_tables (msg : List UInt8) (src : SkbSource) :
    Ensures (receiveHandshakePacket msg src) TablesSafeWG (fun _ => TablesSafeWG) := by
  rw [← receivePacket_source]
  unfold receivePacketSource
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branch .hsCookie _) TablesSafeWG)) ?_
  intro isCookie
  cases isCookie with
  | true =>
    simp only [ite_true]
    refine ensures_bind _ _ (cookieMessageConsume_tables msg) ?_
    intro _ g ambient result final after pre run
    cases run
    exact pre
  | false =>
    simpa only [Bool.false_eq_true, ite_false] using
      (ensures_iff _ _ _).mpr (receiveLoadThen_tables_native (receivePacketBody msg src)
        (fun b => (ensures_iff _ _ _).mp (receivePacketBody_tables msg src b)))

/-- One actual queue iteration: consume the ring before the packet body, then
reduce the queue-length counter only after normal body completion. -/
theorem receiveStep_tables : Ensures receiveStep TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure (value : Bool) : Ensures (pure value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hbranch (value : Bool) : Ensures (branch .workerConsumed value : WG.M Bool)
      TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .workerConsumed value) TablesSafeWG)
  have hmodify (f : Device → Device)
      (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  unfold receiveStep
  refine ensures_bind _ _ hdev ?_
  intro d
  cases consumed : d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none => exact ensures_bind _ _ (hbranch false) (fun _ => hpure false)
    | some packet =>
      obtain ⟨msg, src⟩ := packet
      exact ensures_bind _ _ (hbranch true) (fun _ =>
        ensures_bind _ _ (hmodify _ (fun _ => rfl)) (fun _ =>
          ensures_bind _ _ (receiveHandshakePacket_tables msg src) (fun _ =>
            ensures_bind _ _ (hmodify _ (fun _ => rfl)) (fun _ => hpure true))))

end Leanux.Proofs.WG.Index
