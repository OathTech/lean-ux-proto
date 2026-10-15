import LookupCallHistory
import PeerCountPhase

namespace Binary.PeerCountPhase

/-- Ordinary instructions leave the pending count unchanged. Both trigger
    PCs are checked explicitly; absence of correspondence cuts is not enough. -/
theorem edge_ordinary (pending : Option Pending) (before after : MachineState)
    (noReturn : before.pc ≠ Image.PeerGet.entry+0xaf)
    (noIncrement : before.pc ≠ Image.PeerGet.entry+0x4a) :
    edge pending before after = pending := by
  simp only [edge, noReturn, ite_false, noIncrement, false_and]

/-- A real CALL followed by the named service's no-reentry history preserves
    the pending count phase, including all of the service's internal states. -/
theorem scan_call_service (pending : Option Pending) (front : List MachineState)
    (before called : MachineState) (tail : List MachineState)
    (noReturn : before.pc ≠ Image.PeerGet.entry+0xaf)
    (noIncrement : before.pc ≠ Image.PeerGet.entry+0x4a)
    (service : TrustBase.NoAnchoredReentry (called :: tail)) :
    scan pending (front ++ before :: called :: tail) = scan pending (front ++ [before]) := by
  rw [scan_splice pending front before (called :: tail)]
  change scan (edge (scan pending (front ++ [before])) before called) (called :: tail) = _
  rw [edge_ordinary _ before called noReturn noIncrement]
  exact scan_service _ _ service

#print axioms edge_ordinary
#print axioms scan_call_service
end Binary.PeerCountPhase
