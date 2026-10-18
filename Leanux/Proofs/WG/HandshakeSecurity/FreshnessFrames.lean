import Leanux.Proofs.WG.HandshakeSecurity.LookupFrames
import Leanux.Proofs.WG.HandshakeSecurity.TimestampFrames
import Leanux.Proofs.WG.HandshakeSecurity.RefusalClaims

/-! Freshness frames retain allocation identity together with the timestamp;
raw peer slots alone cannot identify a history across deletion and recreation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

def freshnessAt (w : WGWorld) (pid : PeerId) : Option (Nat × List UInt8) :=
  (w.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId, p.latestTimestamp)

def RetainsFreshness (w v : WGWorld) : Prop :=
  ∀ pid stamp, freshnessAt v pid = some stamp → freshnessAt w pid = some stamp

theorem RetainsFreshness.refl (w : WGWorld) : RetainsFreshness w w := fun _ _ h => h

theorem RetainsFreshness.trans {u v w : WGWorld}
    (uv : RetainsFreshness u v) (vw : RetainsFreshness v w) : RetainsFreshness u w :=
  fun pid stamp h => uv pid stamp (vw pid stamp h)

theorem RetainsHandshake.freshness {w v : WGWorld} (h : RetainsHandshake w v) :
    RetainsFreshness w v := by
  intro pid stamp found
  cases hd : v.dev with
  | none => simp [freshnessAt, hd] at found
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [freshnessAt, hd, hp] at found
    | some p =>
      have before := h pid (handshakeView p) (by simp [peerView, hd, hp])
      have projected := congrArg (Option.map fun view => (view.identity, view.timestamp)) before
      simpa [peerView, freshnessAt, handshakeView, Option.map_bind, Option.map_map,
        Function.comp_def] using projected.trans (by simpa [freshnessAt, hd, hp, handshakeView] using found)

theorem modifyPeer_freshness (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).latestTimestamp = p.latestTimestamp)
    (w v : WGWorld) (a b : Ambient) (x : Unit)
    (run : (((do setPeer pid (f (← getPeer pid))) : WG.M Unit).run w).run a =
      .ok ((x, v), b)) : RetainsFreshness w v := by
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p, read, ambient, getter, setter⟩ := run
  obtain ⟨hw, ha, d, hd, hp⟩ := Queues.getPeer_normal pid w read p a ambient getter
  subst read
  subst ambient
  change Except.ok (((), {w with dev := w.dev.map fun d =>
    {d with peers := d.peers.insert pid (f p)}}), a) = .ok ((x, v), b) at setter
  simp only [hd, Option.map_some, Except.ok.injEq, Prod.mk.injEq] at setter
  rw [← setter.1.2]
  intro j stamp found
  simp only [freshnessAt, hd, Option.bind_some, Std.TreeMap.getElem?_insert,
    Std.LawfulEqOrd.compare_eq_iff_eq] at found ⊢
  by_cases sameSlot : pid = j
  · subst j
    simpa [hp, same p] using found
  · simpa [sameSlot] using found

theorem getDev_freshness (w v : WGWorld) (a b : Ambient) (d : Device)
    (run : (getDev.run w).run a = .ok ((d, v), b)) : RetainsFreshness w v := by
  cases hd : w.dev with
  | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
  | some current =>
    simp [getDev, hd] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact .refl _

theorem out_freshness (peer ret : Option PeerId) (w v : WGWorld)
    (a b : Ambient) (x : Option PeerId)
    (run : ((Queues.RxCredits.HandshakeLoans.initiationOut peer ret).run w).run a =
      .ok ((x, v), b)) : RetainsFreshness w v := by
  cases ret with
  | none => exact (out_none_retains peer w v a b x run).freshness
  | some pid =>
    change Except.ok ((some pid, w), CounterWindow.record a .consumeFailedPut false) =
      .ok ((x, v), b) at run
    cases run
    exact .refl _

theorem writeEphemeral_freshness (pid : PeerId) (e : List UInt8) (w v : WGWorld)
    (a b : Ambient) (x : Unit)
    (run : ((writeEphemeral pid e).run w).run a = .ok ((x, v), b)) :
    RetainsFreshness w v :=
  modifyPeer_freshness pid (fun p => {p with remoteEphemeral := e}) (fun _ => ⟨rfl, rfl⟩) w v a b x run

theorem writeMaterial_freshness (pid : PeerId) (hash ck : List UInt8) (index : Nat) (w v : WGWorld)
    (a b : Ambient) (x : Unit)
    (run : ((writeMaterial pid hash ck index).run w).run a = .ok ((x, v), b)) :
    RetainsFreshness w v :=
  modifyPeer_freshness pid (fun p => {p with hash := hash, chainingKey := ck, remoteIndex := index}) (fun _ => ⟨rfl, rfl⟩) w v a b x run

theorem writeConsumption_freshness (pid : PeerId) (time : Int64) (w v : WGWorld)
    (a b : Ambient) (x : Unit)
    (run : ((writeConsumption pid time).run w).run a = .ok ((x, v), b)) :
    RetainsFreshness w v :=
  modifyPeer_freshness pid (fun p => {p with lastInitiationConsumption := time}) (fun _ => ⟨rfl, rfl⟩) w v a b x run

theorem writeConsumedTag_freshness (pid : PeerId)  (w v : WGWorld)
    (a b : Ambient) (x : Unit)
    (run : ((writeConsumedTag pid ).run w).run a = .ok ((x, v), b)) :
    RetainsFreshness w v :=
  modifyPeer_freshness pid (fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION}) (fun _ => ⟨rfl, rfl⟩) w v a b x run

end Leanux.Proofs.WG.HandshakeSecurity
