import Leanux.Proofs.WG.Noise.InitiationReadyFrames

/-! Allocation-arming metadata is preserved by initiation and index insertion. -/
set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem bucketHas_allocArmed (allocArmed : List String) (walk collide : Decision) (index : Nat)
    (table : List IndexEntry) :
    Product.Ensures ((Index.bucketHas walk collide index).run table)
      (fun ambient => ambient.allocArmed = allocArmed)
      (fun _ ambient => ambient.allocArmed = allocArmed) :=
  InitiationReady.bucketHas_metadata (fun _ armed => armed = allocArmed) walk collide index table

theorem indexInsert_allocArmed (allocArmed : List String) (owner : IndexOwner)
    (table : List IndexEntry) :
    Product.Ensures ((indexInsert owner).run table)
      (fun ambient => ambient.allocArmed = allocArmed)
      (fun _ ambient => ambient.allocArmed = allocArmed) :=
  InitiationReady.indexInsert_metadata (fun _ armed => armed = allocArmed) owner table

theorem createInitiation_allocArmed (allocArmed : List String) (pid : PeerId)
    (state : WGWorld) :
    Product.Ensures ((createInitiation pid).run state)
      (fun ambient => ambient.allocArmed = allocArmed)
      (fun _ ambient => ambient.allocArmed = allocArmed) :=
  InitiationReady.createInitiation_metadata (fun _ armed => armed = allocArmed) pid state

end Leanux.Proofs.WG.TimerDiscipline.SendReady
