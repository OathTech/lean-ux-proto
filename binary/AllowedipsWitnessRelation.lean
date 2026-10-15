import AllowedipsWitnessTrie
import AllowedipsWitnessFields
namespace Binary.AllowedipsWitness
open Leanux Leanux.WG AllowedipsRelation
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def config4 : Config := {
  root := some 7, bits := 32, key := key4, nodes := nodeAddress, peers := peerAddress,
  focus := ⟨some 5, some 3⟩, incomingSteps := [], rxSection := 0 }

def config6 : Config := {
  root := some 1, bits := 128, key := key6, nodes := nodeAddress, peers := peerAddress,
  focus := ⟨some 8, some 4⟩, incomingSteps := [], rxSection := 0 }

def view : View := ⟨nodes, some 1⟩

theorem project4 : project config4 world = some view := by rfl

theorem project6 : project config6 world = some view := by rfl

theorem related4 : R config4 [initial4] [LookupObservation.call "lookup" initial4] initial4 world := by
  refine ⟨rfl, ⟨view, project4, ?_⟩, ?_⟩
  · refine ⟨trie4, ?_⟩
    refine ⟨1, rfl, by decide, ?_⟩
    exact count4_read
  · exact ⟨rfl,rfl⟩

theorem related6 : R config6 [initial6] [LookupObservation.call "lookup" initial6] initial6 world := by
  refine ⟨rfl, ⟨view, project6, ?_⟩, ?_⟩
  · refine ⟨trie6, ?_⟩
    refine ⟨1, rfl, by decide, ?_⟩
    exact count6_read
  · exact ⟨rfl,rfl⟩

theorem selected4 : AllowedipsSource.select nodes (some 7) 32 key4 = some (some 5) := by decide

theorem selected6 : AllowedipsSource.select nodes (some 1) 128 key6 = some (some 8) := by decide

#print axioms related4
#print axioms related6
#print axioms selected4
#print axioms selected6
end Binary.AllowedipsWitness
