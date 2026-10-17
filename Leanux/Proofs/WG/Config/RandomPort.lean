import Leanux.Proofs.WG.Config.SocketPorts

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem littleEndian_bound (bs : List UInt8) :
    bs.foldr (fun b acc => acc * 256 + b.toNat) 0 < 256 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b rest ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    omega

theorem randomPortFirst_range (rand : Nat) (bounded : rand < 2 ^ 32) :
    LOCAL_PORT_LOW ≤ randomPortFirst rand ∧ randomPortFirst rand ≤ LOCAL_PORT_HIGH := by
  simp only [randomPortFirst, LOCAL_PORT_LOW, LOCAL_PORT_HIGH] at *
  omega

/-- Native hidden draws preserve an arbitrary outer state and return four bytes
whenever they return normally. Malformed records remain stopped executions. -/
theorem hiddenUdp_shape {σ : Type} (P : σ → Prop) :
    ⦃fun s => ⌜P s⌝⦄ (hidden .udpPortDraw : StateT σ AmbientM (List UInt8))
    ⦃⇓? bs s => ⌜P s ∧ bs.length = 4⌝⦄ := by
  have shape : ∀ ambient bs after, (AmbientM.hidden .udpPortDraw).run ambient =
      .ok (bs, after) → bs.length = 4 := by
    intro ambient bs after run
    have failure {α : Type} (stop : Stop) (a : Ambient) :
        (throw stop : AmbientM α).run a = .error stop := rfl
    have jitter : (HiddenSite.udpPortDraw == HiddenSite.retransmitJitter) = false := by decide
    cases records : ambient.hidden with
    | none =>
      cases placeholders : ambient.hiddenPlaceholders with
      | false =>
        simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
          HiddenSite.info, Worker.sectionId, Worker.index, failure, jitter,
          -List.any_eq_true, -List.any_eq_false, records, placeholders] at run
        cases run
      | true =>
        cases steered : ambient.steerValues.findIdx? (·.1 == "udp_port_draw") with
        | none =>
          simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
            HiddenSite.info, Worker.sectionId, Worker.index, jitter,
            -List.any_eq_true, -List.any_eq_false, records, placeholders, steered] at run
          rcases run with ⟨rfl, rfl⟩
          simp
        | some k =>
          cases value : (ambient.steerValues[k]?.getD default).2 with
          | none =>
            simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
              HiddenSite.info, Worker.sectionId, Worker.index, jitter,
            -List.any_eq_true, -List.any_eq_false, records, placeholders, steered, value] at run
            rcases run with ⟨rfl, rfl⟩
            simp
          | some bytes =>
            by_cases width : bytes.length = 4
            · simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
                HiddenSite.info, Worker.sectionId, Worker.index, jitter,
            -List.any_eq_true, -List.any_eq_false, records, placeholders, steered, value, width] at run
              rcases run with ⟨rfl, rfl⟩
              exact width
            · simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
                HiddenSite.info, Worker.sectionId, Worker.index, failure, jitter,
          -List.any_eq_true, -List.any_eq_false, records, placeholders, steered, value, width] at run
              cases run
    | some recordsList =>
      cases remaining : recordsList.dropWhile (fun r => HiddenSite.passive r.site) with
      | nil =>
        simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
          HiddenSite.info, Worker.sectionId, Worker.index, failure, jitter,
            -List.any_eq_true, -List.any_eq_false, records, remaining] at run
      | cons record rest =>
        by_cases site : record.site = 125
        · by_cases width : record.bytes.length = 8
          · cases padding : (record.bytes.drop 4).any (· != 0) with
            | false =>
              simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
                HiddenSite.info, Worker.sectionId, Worker.index, jitter,
                -List.any_eq_true, -List.any_eq_false, records, remaining, site, width, padding] at run
              rcases run with ⟨rfl, rfl⟩
              simp [List.length_take, width]
            | true =>
              simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
                HiddenSite.info, Worker.sectionId, Worker.index, failure, jitter,
            -List.any_eq_true, -List.any_eq_false, records, remaining, site, width, padding] at run
              cases run
          · simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
              HiddenSite.info, Worker.sectionId, Worker.index, failure, jitter,
            -List.any_eq_true, -List.any_eq_false, records, remaining, site, width] at run
            cases run
        · simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
            HiddenSite.info, Worker.sectionId, Worker.index, failure, jitter,
            -List.any_eq_true, -List.any_eq_false, records, remaining, site] at run
          cases run
  apply (Noise.ensures_iff _ _ _).mp
  intro s ambient bs final after pre run
  change ((AmbientM.hidden .udpPortDraw).run ambient).map
    (fun (value, next) => ((value, s), next)) = .ok ((bs, final), after) at run
  cases draw : (AmbientM.hidden .udpPortDraw).run ambient with
  | error stop => rw [draw] at run; cases run
  | ok pair =>
    obtain ⟨value, next⟩ := pair
    rw [draw] at run
    cases run
    exact ⟨pre, shape ambient bs after draw⟩

theorem socketInit_zero (d : Device) (net : d.creatingNet = true) :
    Ensures (socketInit 0) (fun g => g.dev = some d)
      (fun ret g => ret = 0 ∧ ∃ port,
        LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧ g.dev = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) := by
  intro g ambient ret final after device run
  have source : ((socketInit 0).run g).run ambient =
      (((do
        let bs ← hidden .udpPortDraw
        let first := randomPortFirst (bs.foldr (fun b acc => acc * 256 + b.toNat) 0)
        if g.portBound first || d.sock4 == some first || d.sock6 == some first then
          unsupported "the random port draw collides with a bound port"
        socketReinit (some first) (some first)
        pure (0 : Int)) : WG.M Int).run g).run ambient := by
    simp [socketInit, getDev, device, net]
  rw [source] at run
  change (((hidden .udpPortDraw : WG.M (List UInt8)).run g).run ambient >>=
    fun ((bytes, current), next) =>
      (((do
        let first := randomPortFirst (bytes.foldr (fun b acc => acc * 256 + b.toNat) 0)
        if g.portBound first || d.sock4 == some first || d.sock6 == some first then
          unsupported "the random port draw collides with a bound port"
        socketReinit (some first) (some first)
        pure (0 : Int)) : WG.M Int).run current).run next) = _ at run
  cases draw : ((hidden .udpPortDraw : WG.M (List UInt8)).run g).run ambient with
  | error stop => rw [draw] at run; cases run
  | ok pair =>
    obtain ⟨⟨bytes, current⟩, next⟩ := pair
    obtain ⟨resident, width⟩ := (Noise.ensures_iff _ _ _).mpr
      (hiddenUdp_shape (fun w : WGWorld => w.dev = some d)) g ambient bytes current next device draw
    rw [draw] at run
    dsimp only [Bind.bind, Except.bind] at run
    let port := randomPortFirst (bytes.foldr (fun b acc => acc * 256 + b.toNat) 0)
    have range : LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH := by
      apply randomPortFirst_range
      have bound := littleEndian_bound bytes
      rw [width] at bound
      exact bound
    change (((if g.portBound port || d.sock4 == some port || d.sock6 == some port then do
        (unsupported "the random port draw collides with a bound port" : WG.M Unit)
        socketReinit (some port) (some port)
        pure (0 : Int)
      else do
        socketReinit (some port) (some port)
        pure (0 : Int)) : WG.M Int).run current).run next = _ at run
    by_cases held : (g.portBound port || d.sock4 == some port || d.sock6 == some port) = true
    · simp [held, unsupported, AmbientM.unsupported] at run
      cases run
    · simp only [held, Bool.false_eq_true, ite_false] at run
      obtain ⟨u, out, tail, reinit, changed⟩ := socketReinit_returns (some port) (some port) d
        current next resident
      simp only [StateT.run_bind, StateT.run_pure] at run
      rw [reinit] at run
      cases run
      exact ⟨rfl, port, range.1, range.2, changed⟩

def udpDrawRecord (a b c d : UInt8) : HiddenRecord :=
  { site := HiddenSite.udpPortDraw.info.id, bytes := [a, b, c, d, 0, 0, 0, 0] }

theorem hiddenUdp_record {σ : Type} (a b c d : UInt8) (rest : List HiddenRecord)
    (P : σ → Prop) (s : σ) :
    Config.Product.Returns ((hidden .udpPortDraw : StateT σ AmbientM (List UInt8)).run s)
      (fun ambient => P s ∧ ambient.hidden = some (udpDrawRecord a b c d :: rest))
      (fun (bs, current) ambient => bs = [a, b, c, d] ∧ P current ∧ ambient.hidden = some rest) := by
  intro ambient pre
  have passive : HiddenSite.passive 125 = false := by decide
  have exactRead : (AmbientM.hidden .udpPortDraw).run ambient =
      .ok ([a, b, c, d], {ambient with hidden := some rest}) := by
    simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      pre.2, udpDrawRecord, HiddenSite.info, passive, Worker.sectionId, Worker.index, Except.pure, Except.bind]
  refine ⟨([a, b, c, d], s), {ambient with hidden := some rest}, ?_, rfl, pre.1, rfl⟩
  change ((AmbientM.hidden .udpPortDraw).run ambient).map
    (fun (value, next) => ((value, s), next)) = _
  rw [exactRead]
  rfl

/-- The exact first candidate for a supplied four-byte UDP port draw. -/
def drawnPort (a b c d : UInt8) : Nat :=
  randomPortFirst ([a, b, c, d].foldr (fun b acc => acc * 256 + b.toNat) 0)

theorem socketInit_zero_record_returns (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) (g : WGWorld) :
    Config.Product.Returns ((socketInit 0).run g)
      (fun ambient => g.dev = some d ∧
        ambient.hidden = some (udpDrawRecord a b c e :: rest) ∧ g.portBound (drawnPort a b c e) = false)
      (fun (ret, current) _ => ret = 0 ∧ current.dev = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e }) := by
  intro ambient pre
  obtain ⟨⟨bytes, middle⟩, next, draw, bytesEq, device, records⟩ :=
    hiddenUdp_record a b c e rest (fun g : WGWorld => g.dev = some d) g ambient ⟨pre.1, pre.2.1⟩
  subst bytes
  obtain ⟨u, final, after, reinit, changed⟩ :=
    socketReinit_returns (some (drawnPort a b c e)) (some (drawnPort a b c e)) d
      middle next device
  refine ⟨(0, final), after, ?_, rfl, changed⟩
  simp only [socketInit, getDev, StateT.run_bind, StateT.run_get, pre.1,
    StateT.run_pure, pure_bind, net, Bool.not_true, Bool.false_eq_true, ite_false,
    beq_self_eq_true, ite_true]
  rw [draw]
  dsimp only [Bind.bind, Except.bind]
  change (((if g.portBound (drawnPort a b c e) || d.sock4 == some (drawnPort a b c e) ||
      d.sock6 == some (drawnPort a b c e) then do
        (unsupported "the random port draw collides with a bound port" : WG.M Unit)
        socketReinit (some (drawnPort a b c e)) (some (drawnPort a b c e))
        pure (0 : Int)
      else do
        socketReinit (some (drawnPort a b c e)) (some (drawnPort a b c e))
        pure (0 : Int)) : WG.M Int).run middle).run next = _
  simp only [pre.2.2, beq_eq_false_iff_ne.mpr free4, beq_eq_false_iff_ne.mpr free6,
    Bool.false_or, Bool.false_eq_true, ite_false]
  simp only [StateT.run_bind, StateT.run_pure]
  rw [reinit]
  rfl

end Leanux.Proofs.WG.Config
