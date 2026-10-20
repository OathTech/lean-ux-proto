import AllowedipsImage
import LookupObservation

namespace Binary.AllowedipsObservation
open Leanux LookupObservation

/-- The allowedips observer uses only actual consecutive Kraken states and
    the incoming NET_RX context. Calls and returns match the logged source;
    there is no expected source decision stream among its inputs. -/
def edge (rxSection : Nat) (s t : MachineState) : Except String (List Point) := do
  let l := AllowedipsImage.Lookup.entry
  let c := AllowedipsImage.CommonBits.entry
  if s.pc = l+0x41 then
    return [decision rxSection .swapEndian32 (← choice t.pc (l+0x171) (l+0x47)) t]
  if s.pc = l+0x5b then
    return [decision rxSection .swapEndian128 (← choice t.pc (l+0x14f) (l+0x61)) t]
  if s.pc = l+0x81 then
    let more ← choice t.pc (l+0x87) (l+0x184)
    return [decision rxSection .findNodeNode more t] ++
      if more then [] else [decision rxSection .lookupFound false t]
  if s.pc = l+0xd3 then
    return [decision rxSection .findNodeNode (← choice t.pc (l+0xd5) (l+0x101)) t]
  if s.pc = c+0x24 then
    return [decision rxSection .commonBits32 (← choice t.pc (c+0x4c) (c+0x26)) t]
  if s.pc = c+0x3c then
    return [decision rxSection .commonBits128 (← choice t.pc (c+0x75) (c+0x3e)) t]
  if s.pc = c+0x91 then
    return [decision rxSection .fls128High (← choice t.pc (c+0x93) (c+0xc4)) t]
  if s.pc = l+0xff then
    return [decision rxSection .findNodePrefixMatches (← choice t.pc (l+0x90) (l+0x101)) t]
  if s.pc = l+0x9b then
    let _ ← choice t.pc (l+0x9f) (l+0x9f)
    return [decision rxSection .findNodeHasPeer (s.data.regs.rax != 0) t]
  if s.pc = l+0xb2 then
    return [decision rxSection .findNodeFullLength (← choice t.pc (l+0x101) (l+0xb4)) t]
  if s.pc = l+0x109 then
    return [decision rxSection .lookupFound (← choice t.pc (l+0x10b) (l+0x184)) t]
  if s.pc = l+0x11c then
    return [decision rxSection .lookupPeerGone (← choice t.pc (l+0x74) (l+0x122)) t]
  if s.pc = l+0xe5 then
    if t.pc != c then throw "allowedips common_bits call reached a different callee"
    return [call "common_bits" t]
  if s.pc = c+0x4b ∨ s.pc = c+0x74 ∨ s.pc = c+0xc3 then
    if t.pc != l+0xea then throw "allowedips common_bits returned to a different caller"
    return [returned "common_bits" t]
  if s.pc = l+0x114 then
    if t.pc != Image.PeerGet.entry then throw "allowedips peer-get call reached a different callee"
    return [call "wg_peer_get_maybe_zero" t]
  if s.pc = l+0x14e then return [returned "lookup" t]
  if s.pc = Image.PeerGet.entry+0xaf then
    if t.pc != l+0x119 then throw "allowedips peer-get returned to a different caller"
    return [returned "wg_peer_get_maybe_zero" t]
  if (Image.fetchIn Image.PeerGet.entry Image.PeerGet.code s.pc).isSome then
    return ← LookupObservation.edge rxSection s t
  return []

def observe (rxSection : Nat) (history : List MachineState) : Except String (List Point) := do
  let initial :: _ := history | throw "empty allowedips execution history"
  if initial.pc != AllowedipsImage.Lookup.entry then
    throw "allowedips history does not start at its entry"
  return call "lookup" initial :: (← observeHistory (edge rxSection) history)

/-- Incremental history observation, retaining every actual repeated visit
    and every compiler-merged decision point. -/
theorem observe_snoc (rxSection : Nat) (history : List MachineState)
    (current next : MachineState) (events delta : List Point)
    (last : history.getLast? = some current)
    (observed : observe rxSection history = .ok events)
    (newEdge : edge rxSection current next = .ok delta) :
    observe rxSection (history ++ [next]) = .ok (events ++ delta) := by
  cases history with
  | nil => cases last
  | cons initial rest =>
    by_cases entry : initial.pc = AllowedipsImage.Lookup.entry
    · cases raw : observeHistory (edge rxSection) (initial :: rest) with
      | error e => simp [observe, entry, raw] at observed; cases observed
      | ok prior =>
        have he : call "lookup" initial :: prior = events := by
          have h := observed
          simp [observe, entry, raw] at h
          exact Except.ok.inj h
        have extended := observeHistory_snoc (edge rxSection) (initial :: rest)
          current next prior delta last raw newEdge
        change observeHistory (edge rxSection) (initial :: (rest ++ [next])) = .ok (prior ++ delta) at extended
        simp [observe, entry, extended, ← he]
        rfl
    · simp [observe, entry] at observed
      cases observed

#print axioms observe_snoc
end Binary.AllowedipsObservation
