import Leanux.Proofs.WG.HandshakeSecurity.ResponderCoreTraffic
import Leanux.Proofs.WG.Origins.SessionMaterial

/-! Native survivor frames for immutable sending material. Session derivation
is confined to its actual fresh numeric slot. No forward residency or key
reference credit is assumed. These are local source facts, not initialized
packet provenance. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Responder Origins Origins.Retaining

theorem rotation_core (pid : PeerId) (kid : KeypairId) :
    CoreRetains (addNewKeypair pid kid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => Responder.Retains initial (pool w))
    (Q := fun _ w => Responder.Retains initial (pool w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    rw [h]
    exact Responder.Retains.refl _
  unfold addNewKeypair
  material_lower
  repeat' first
    | (index_material_head keypairPut; exact (keypairPut_core _ _).wp initial)
    | core_traffic (Responder.Retains initial)

theorem session_tail_core (pid : PeerId) (kid : KeypairId) :
    CoreRetains (SessionOrigin.tail pid kid) := by
  apply ProjectedAction.of_wp
  intro initial
  refine hoare_consequence
    (P := fun w => Responder.Retains initial (pool w))
    (Q := fun _ w => Responder.Retains initial (pool w)) ?_ ?_ (fun _ _ h => h)
  rotate_left
  · intro w h
    rw [h]
    exact Responder.Retains.refl _
  unfold SessionOrigin.tail SessionOrigin.tailWith handshakeZero
  material_lower
  repeat' first
    | (index_material_head addNewKeypair; exact (rotation_core _ _).wp initial)
    | core_traffic (Responder.Retains initial)
  apply hoare_liftIndex
  intro w d table hi hd
  change Responder.Retains initial (fun q => (d.keypairs[q]?).map keyCore)
  change Responder.Retains initial (fun q => (w.dev.bind fun d => d.keypairs[q]?).map keyCore) at hi
  simpa only [hd,Option.bind_some] using hi

/-- The session changes immutable sending material only at its actual newly
allocated slot. An old slot below the entry frontier, if still resident after
rotation, has exactly its earlier allocation stamp, role and sending bytes. -/
theorem session_below (pid : PeerId) (w v : WGWorld) (a b : Ambient) (result : Bool)
    (device : w.dev = some d)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b))
    (slot : KeypairId) (below : slot < d.nextKeypairId) (core : KeyCore)
    (resident : pool v slot = some core) : pool w slot = some core := by
  rw [SessionOrigin.factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨front,middle,clock,entered,tail⟩ := run
  cases front with
  | none =>
    cases tail
    have same := Origins.front_none pid w v a b entered
    simpa only [same] using resident
  | some context =>
    have old := (ProjectedAction.iff_run_ambient _ _ _).mp
      (session_tail_core pid context.slot) middle clock result v b tail slot core resident
    obtain ⟨source,key,present,_,_,_,fresh,view,_⟩ :=
      Origins.front_effect pid context w middle a clock entered
    have sourceSame := Option.some.inj (present.symm.trans device)
    subst source
    have different : context.slot ≠ slot := by rw [fresh]; exact Ne.symm (Nat.ne_of_lt below)
    rw [pool_factor,view] at old
    simpa only [Option.bind_some,different,↓reduceIte,pool,device] using old

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
