import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorObserved

/-! Fixed native tunnel checks, counter write, port read and append boundary.
Every successful intermediate world is obtained from its original prefix;
failed primitives retain their actual input and output history only. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

def tunnelChecks (r : Route) (exactRx : Bool) : MixedM Unit := do
  if r.dev == WG0_IFINDEX then liftWGPrefix (unsupported "a datagram routed back into wg0")
  if exactRx then loopbackSendPrefix ([.ipIdentKey,.ipIdentReserve,.flowHashSecret] ++ allocCuts) true
  else liftWGPrefix (skipCut [.ipIdentKey,.ipIdentReserve,.flowHashSecret,.sectionStart .netRx,.sectionStop .netRx])

def countedWorld (bytes : List UInt8) (w : WGWorld) : WGWorld :=
  {w with dev := w.dev.map fun d =>
    {d with txPackets := d.txPackets + 1,txBytes := d.txBytes + bytes.length}}

def countedPrefix (bytes : List UInt8) (r : Route) (exactRx : Bool) : MixedM Unit := do
  tunnelChecks r exactRx
  liftWGPrefix (modifyDev fun d => {d with txPackets := d.txPackets + 1,txBytes := d.txBytes + bytes.length})

theorem tunnel_checks_factor (e : Endpoint) (bytes : List UInt8) (r : Route) (exactRx : Bool) :
    tunnelFront e bytes r exactRx = (do
      tunnelChecks r exactRx
      liftWGPrefix (modifyDev fun d => {d with txPackets := d.txPackets + 1,txBytes := d.txBytes + bytes.length})
      liftWGPrefix (socketPort e.family)) := by
  unfold tunnelFront tunnelChecks
  by_cases inside : r.dev == WG0_IFINDEX
  all_goals cases exactRx <;> simp only [inside,Bool.false_eq_true,↓reduceIte,bind_assoc]

theorem tunnel_counted_factor (e : Endpoint) (bytes : List UInt8) (r : Route) (exactRx : Bool) :
    tunnelFront e bytes r exactRx = (countedPrefix bytes r exactRx >>= fun _ => liftWGPrefix (socketPort e.family)) := by
  rw [tunnel_checks_factor]
  simp only [countedPrefix,bind_assoc]

theorem count_total (bytes : List UInt8) (w : WGWorld) (ambient : Ambient) (history : List LifetimeEvent) :
    runStatePrefix (liftWGPrefix (modifyDev fun d =>
      {d with txPackets := d.txPackets + 1,txBytes := d.txBytes + bytes.length})) w ambient history =
        (.ok (((),countedWorld bytes w),ambient),history) := rfl

theorem count_view (bytes : List UInt8) (w : WGWorld) :
    StagedEntry.view (countedWorld bytes w) = StagedEntry.view w := by
  change StagedEntry.view {dev := w.dev.map (fun d =>
    {d with txPackets := d.txPackets + 1,txBytes := d.txBytes + bytes.length})} =
      StagedEntry.view {dev := w.dev}
  cases w.dev <;> rfl

/-- A Stop after the counter write is represented by the actual subsequent
port-read run from the counted world, not an error post-world. -/
theorem tunnel_cases (e : Endpoint) (bytes : List UInt8) (r : Route) (exactRx : Bool)
    (w : WGWorld) (ambient : Ambient) (history : List LifetimeEvent) :
    runStatePrefix (tunnelFront e bytes r exactRx) w ambient history =
      match runStatePrefix (tunnelChecks r exactRx) w ambient history with
      | (.error stop,journal) => (.error stop,journal)
      | (.ok (((),u),next),journal) =>
        runStatePrefix (liftWGPrefix (socketPort e.family)) (countedWorld bytes u) next journal := by
  rw [tunnel_checks_factor,runStatePrefix_bind]
  cases runStatePrefix (tunnelChecks r exactRx) w ambient history with
  | mk result journal => cases result with
    | error stop => rfl
    | ok value =>
      rcases value with ⟨⟨value,u⟩,next⟩
      cases value
      dsimp only
      rw [runStatePrefix_bind,count_total]

/-- The original route prefix selects either an errno result or this actual
tunnel child. Cache reads and writes remain inside that same source prefix. -/
theorem before_append_cases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx ipv4 : Bool) (w : WGWorld) (ambient : Ambient) (history : List LifetimeEvent) :
    runStatePrefix (beforeAppend e cache bytes ds exactRx ipv4) w ambient history =
      match runStatePrefix (route e cache bytes ds exactRx ipv4) w ambient history with
      | (.error stop,journal) => (.error stop,journal)
      | (.ok ((.error code,u),next),journal) => (.ok ((.error code,u),next),journal)
      | (.ok ((.ok r,u),next),journal) =>
        let out := runStatePrefix (tunnelFront e bytes r exactRx) u next journal
        (out.1.map (fun ((sport,v),last) => ((Except.ok (datagram e bytes ds r sport),v),last)),out.2) := by
  rw [beforeAppend,runStatePrefix_bind]
  cases runStatePrefix (route e cache bytes ds exactRx ipv4) w ambient history with
  | mk out journal => cases out with
    | error stop => rfl
    | ok value =>
      rcases value with ⟨⟨result,u⟩,next⟩
      cases result with
      | error code => rfl
      | ok r =>
        simp only [afterRoute]
        rw [runStatePrefix_bind]
        cases runStatePrefix (tunnelFront e bytes r exactRx) u next journal with
        | mk value last => cases value with
          | error stop => rfl
          | ok returned => rcases returned with ⟨⟨sport,v⟩,final⟩; rfl

/-- Every successful datagram has the original packet bytes and endpoint,
with its source address and port supplied by the actual route and port read. -/
theorem append_payload (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx ipv4 : Bool) (w u : WGWorld) (ambient next : Ambient)
    (history journal : List LifetimeEvent) (sent : SentDatagram)
    (run : runStatePrefix (beforeAppend e cache bytes ds exactRx ipv4) w ambient history =
      (.ok ((.ok sent,u),next),journal)) :
    ∃ r v middle events sport,
      runStatePrefix (route e cache bytes ds exactRx ipv4) w ambient history =
        (.ok ((.ok r,v),middle),events) ∧
      runStatePrefix (tunnelFront e bytes r exactRx) v middle events =
        (.ok ((sport,u),next),journal) ∧ sent = datagram e bytes ds r sport := by
  rw [before_append_cases] at run
  cases hr : runStatePrefix (route e cache bytes ds exactRx ipv4) w ambient history with
  | mk result events =>
    rw [hr] at run
    cases result with
    | error stop => cases run
    | ok value =>
      rcases value with ⟨⟨result,v⟩,middle⟩
      cases result with
      | error code => cases run
      | ok r =>
        dsimp only at run
        cases ht : runStatePrefix (tunnelFront e bytes r exactRx) v middle events with
        | mk out last =>
          rw [ht] at run
          cases out with
          | error stop => cases run
          | ok value =>
            rcases value with ⟨⟨sport,resultWorld⟩,final⟩
            cases run
            exact ⟨r,v,middle,events,sport,rfl,ht,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
