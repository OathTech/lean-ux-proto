import Leanux.Proofs.WG.Lifetimes.SocketSend

/-! The cookie tunnel path has its only datagram append as its final action. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes

def tunnelReplyFront (e : Endpoint) (bytes : List UInt8) (r : Route) : WG.M Nat := do
  if r.dev == WG0_IFINDEX then unsupported "a datagram routed back into wg0"
  skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]
  modifyDev fun d => {d with txPackets := d.txPackets + 1, txBytes := d.txBytes + bytes.length}
  socketPort e.family

def tunnelDatagram (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route)
    (sport : Nat) : SentDatagram :=
  {family := e.family, addr := e.addr, port := e.port, bytes, ds, sport, src := r.src}

theorem tunnelReply_factor (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) :
    tunnelXmitSource e bytes ds r false = (do
      let sport ← tunnelReplyFront e bytes r
      modify fun w => {w with sent := w.sent ++ [tunnelDatagram e bytes ds r sport]}) := by
  unfold tunnelXmitSource tunnelReplyFront tunnelDatagram
  simp only [Bool.false_eq_true, ↓reduceIte]
  split <;> simp only [bind_assoc]

/-- Native nested-state bind, exposing precisely its intermediate normal state. -/
theorem native_bind_run (f : WG.M α) (g : α → WG.M β) (w : WGWorld) (a : Ambient) :
    (((f >>= g).run w).run a) = match ((f.run w).run a) with
    | .error e => .error e
    | .ok ((x,v),b) => ((g x).run v).run b := by
  simp only [StateT.run_bind]
  cases result : ((f.run w).run a) with
  | error err => rfl
  | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl

end Leanux.Proofs.WG.AuthenticatedEffects
