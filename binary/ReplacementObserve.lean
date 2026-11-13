import ProbeSupport

namespace Binary.ReplacementObserve
open Lean Leanux Leanux.WG

structure Selection where
  replay : RecordedPrefix
  entry : ReplacementEntryObservation
  cursor : Nat

/-- Bounded pilot: exactly one replacement in the named operation. Both
executions use only recorded source inputs, never native heap values. -/
def select (input : ProbeInput) (operation ordinal : Nat) : Except String Selection := do
  unless ordinal == 0 do throw "observer.pilot-requires-ordinal-zero"
  let disabled ← replayRecordedPrefixRun input.trace (operation + 1)
  let enabled ← replayRecordedPrefixRun input.trace (operation + 1) (some operation)
  unless disabled.entries.isEmpty do throw "observer.disabled-produced-output"
  unless disabled.checkpoints == enabled.checkpoints do throw "observer.changed-execution"
  let #[(op, entry)] := enabled.entries | throw "observer.expected-exactly-one-entry"
  unless op == operation do throw "observer.wrong-operation"
  let trace ← Runner.parseTrace input.trace
  let some original := trace.hidden.bind (·[operation]?) | throw "observer.original-records-missing"
  let some remaining := entry.hidden | throw "observer.remaining-records-missing"
  unless remaining.length ≤ original.length do throw "observer.record-cursor-outside-operation"
  let cursor := original.length - remaining.length
  unless original.drop cursor == remaining do throw "observer.records-are-not-original-suffix"
  return ⟨enabled, entry, cursor⟩

def hiddenJson (record : HiddenRecord) : Json :=
  Json.mkObj [("site", toJson record.site), ("bytes", toJson (record.bytes.map UInt8.toNat))]

def report (selection : Selection) (operation ordinal : Nat) : Json :=
  let e := selection.entry
  Json.mkObj [
    ("status", toJson "observed"), ("operation", toJson operation), ("ordinal", toJson ordinal),
    ("observation_count", toJson selection.replay.entries.size),
    ("unchanged_checkpoints", toJson selection.replay.checkpoints.size),
    ("comparison_scope", toJson "syscall returns, Device, allocation counters, complete Steps, remaining hidden records, environment call counts, extra output, user bytes and file descriptors; not extensional equality of function-valued World fields"),
    ("peer", toJson e.peer), ("keypair", toJson e.keypair),
    ("peer_counter", toJson e.peerCounter), ("keypair_counter", toJson e.keypairCounter),
    ("record_cursor", toJson selection.cursor),
    ("remaining_records", toJson ((e.hidden.getD []).map hiddenJson)),
    ("steps", toJson e.steps.size), ("net_rx_section", toJson e.netRxSection),
    ("suspended_count", toJson e.suspended.length),
    ("pending_work", toJson e.pendingWork), ("unit_peers", toJson e.unitPeers)]

end Binary.ReplacementObserve
