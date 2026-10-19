import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorSix

/-! The actual observed socket has a fixed prefix before its sole append.
Its remaining append/result suffix is total and emits no lifetime event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

def tunnelFront (e : Endpoint) (bytes : List UInt8) (r : Route) (exactRx : Bool) : MixedM Nat := do
  if r.dev == WG0_IFINDEX then liftWGPrefix (unsupported "a datagram routed back into wg0")
  if exactRx then loopbackSendPrefix ([.ipIdentKey,.ipIdentReserve,.flowHashSecret] ++ allocCuts) true
  else liftWGPrefix (skipCut [.ipIdentKey,.ipIdentReserve,.flowHashSecret,.sectionStart .netRx,.sectionStop .netRx])
  liftWGPrefix (modifyDev fun d => {d with txPackets := d.txPackets + 1,txBytes := d.txBytes + bytes.length})
  liftWGPrefix (socketPort e.family)

def datagram (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (sport : Nat) : SentDatagram :=
  {family := e.family,addr := e.addr,port := e.port,bytes,ds,sport,src := r.src}

def appendResult : Except Int SentDatagram → MixedM Int
  | .error err => pure err
  | .ok sent => do
    liftWGPrefix (modify fun w => {w with sent := w.sent ++ [sent]})
    pure 0

def route (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx ipv4 : Bool) : MixedM (Except Int Route) :=
  if ipv4 then Four.socket4Front e cache bytes ds exactRx else Six.front e cache

def afterRoute (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Except Int Route → MixedM (Except Int SentDatagram)
  | .error err => pure (.error err)
  | .ok r => do
    let sport ← tunnelFront e bytes r exactRx
    pure (.ok (datagram e bytes ds r sport))

def beforeAppend (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx ipv4 : Bool) : MixedM (Except Int SentDatagram) :=
  route e cache bytes ds exactRx ipv4 >>= afterRoute e bytes ds exactRx

theorem tunnel_factor (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    tunnelXmitPrefix e bytes ds r exactRx = (do
      let sport ← tunnelFront e bytes r exactRx
      liftWGPrefix (modify fun w => {w with sent := w.sent ++ [datagram e bytes ds r sport]})) := by
  unfold tunnelXmitPrefix tunnelFront datagram
  by_cases inside : r.dev == WG0_IFINDEX
  all_goals cases exactRx <;> simp only [inside,Bool.false_eq_true,↓reduceIte,bind_assoc]

theorem result_factor (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (result : Except Int Route) :
    Four.socketResult e bytes ds exactRx result =
      (afterRoute e bytes ds exactRx result >>= appendResult) := by
  cases result <;> simp only [Four.socketResult,afterRoute,appendResult,pure_bind,tunnel_factor,bind_assoc]

theorem send_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx ipv4 : Bool) :
    (if ipv4 then send4Prefix e cache bytes ds exactRx else send6Prefix e cache bytes ds exactRx) =
      (beforeAppend e cache bytes ds exactRx ipv4 >>= appendResult) := by
  cases ipv4 <;> simp only [Bool.false_eq_true,↓reduceIte,Four.socket4Front_factor,
    Six.socket6Front_factor,beforeAppend,route,bind_assoc]
  all_goals apply congrArg _ (funext (result_factor e bytes ds exactRx))

def appended (w : WGWorld) : Except Int SentDatagram → WGWorld
  | .error _ => w
  | .ok sent => {w with sent := w.sent ++ [sent]}

def resultCode : Except Int SentDatagram → Int
  | .error err => err
  | .ok _ => 0

theorem append_total (result : Except Int SentDatagram) (w : WGWorld) (ambient : Ambient)
    (history : List LifetimeEvent) :
    runPrefix (appendResult result w) ambient history =
      (.ok ((resultCode result,appended w result),ambient),history) := by
  cases result <;> rfl

/-- The full observed socket can stop only before the total append/result suffix.
The failed prefix has its actual history and no invented outgoing world. -/
theorem send_cases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx ipv4 : Bool) (w : WGWorld) (ambient : Ambient)
    (history : List LifetimeEvent) :
    runPrefix ((if ipv4 then send4Prefix e cache bytes ds exactRx else send6Prefix e cache bytes ds exactRx) w) ambient history =
      match runPrefix (beforeAppend e cache bytes ds exactRx ipv4 w) ambient history with
      | (.error stop,journal) => (.error stop,journal)
      | (.ok ((result,u),next),journal) =>
        (.ok ((resultCode result,appended u result),next),journal) := by
  rw [send_factor]
  change runStatePrefix (beforeAppend e cache bytes ds exactRx ipv4 >>= appendResult) w ambient history = _
  rw [runStatePrefix_bind]
  simp only [runStatePrefix,StateT.run]
  cases runPrefix (beforeAppend e cache bytes ds exactRx ipv4 w) ambient history with
  | mk result journal => cases result with
    | error stop => rfl
    | ok value => rcases value with ⟨⟨result,u⟩,next⟩; exact append_total result u next journal

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
