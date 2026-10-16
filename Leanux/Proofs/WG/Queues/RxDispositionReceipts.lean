import Leanux.Proofs.WG.Packets.RoutingCuts
import Leanux.Proofs.Logged.NativeCapture

/-! Plain receipts of the original consume call. Validity and named outcomes
are theorems about the captured execution, never fields supplied by callers. -/
namespace Leanux.Proofs.WG.Queues.RxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.Packets Leanux.Proofs.WG.CounterWindow Std.Do

structure ConsumeReceipt where
  peer : PeerId
  packet : RxPacket
  endpoint : Endpoint
  run : WGRunWitness (Option (List UInt8))

def ConsumeReceipt.Valid (r : ConsumeReceipt) : Prop :=
  r.run.Valid (consumeDataDone r.peer r.packet r.endpoint)

/-- The two real normal-return source routes. The second includes repayment
before the peer-mismatch decision; a Stop in repayment is not a None receipt. -/
theorem none_route (r : ConsumeReceipt) (hv : r.Valid) (hn : r.run.value = none) :
    ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore = .ok ((none, r.run.after), r.run.ambientAfter) ∨
    ∃ ready u q routed paid middle afterLookup afterPaid,
      ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore = .ok ((some ready, u), middle) ∧
      ((lookupSrc ready.protocol ready.bytes).run u).run middle = .ok ((routed, q), afterLookup) ∧
      ((peerPut routed).run q).run afterLookup = .ok (((), paid), afterPaid) ∧ routed ≠ some r.peer ∧
      ((rxAfterLookup r.peer ready routed).run q).run afterLookup = .ok ((none, r.run.after), r.run.ambientAfter) := by
  have hr := hv
  unfold ConsumeReceipt.Valid WGRunWitness.Valid at hr
  rw [hn, consumeDataDone_factor] at hr
  simp only [StateT.run_bind] at hr
  cases hp : ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore with
  | error e => simp [hp] at hr
  | ok out =>
    rcases out with ⟨⟨ready, u⟩, middle⟩
    cases ready with
    | none =>
      simp only [hp, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
      cases hr
      exact Or.inl rfl
    | some ready =>
      simp only [hp, Leanux.Proofs.WG.CounterWindow.except_ok_bind, rxFinish, StateT.run_bind] at hr
      cases hq : ((lookupSrc ready.protocol ready.bytes).run u).run middle with
      | error e => simp [hq] at hr
      | ok out =>
        rcases out with ⟨⟨routed, q⟩, afterLookup⟩
        simp only [hq, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
        have tail := hr
        unfold rxAfterLookup at hr
        simp only [StateT.run_bind] at hr
        cases hput : ((peerPut routed).run q).run afterLookup with
        | error e => simp [hput] at hr
        | ok out =>
          rcases out with ⟨⟨returned, paid⟩, afterPaid⟩
          cases returned
          have different : routed ≠ some r.peer := by
            intro he
            subst routed
            simp only [hput, except_ok_bind, branch, bne_self_eq_false] at hr
            cases hs : ((updateRxStats r.peer (ready.originalLen + MESSAGE_DATA_LEN_0)).run paid).run
                (record afterPaid .doneDishonestPeer false) <;> simp_all
          exact Or.inr ⟨ready, u, q, routed, paid, middle, afterLookup, afterPaid, rfl, hq, hput, different, tail⟩

theorem some_route (r : ConsumeReceipt) (hv : r.Valid) (bytes : List UInt8)
    (hb : r.run.value = some bytes) :
    ∃ ready u q middle afterLookup,
      ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore = .ok ((some ready, u), middle) ∧
      ((lookupSrc ready.protocol ready.bytes).run u).run middle = .ok ((some r.peer, q), afterLookup) ∧
      ((rxAfterLookup r.peer ready (some r.peer)).run q).run afterLookup = .ok ((some bytes, r.run.after), r.run.ambientAfter) ∧
      RxPrepared r.packet ready ∧ bytes = ready.bytes.take ready.ipLen := by
  apply consumeDataDone_query
  simpa only [ConsumeReceipt.Valid, WGRunWitness.Valid, hb] using hv

/-- Source header/length predicates; keepalive is normal nondelivery. -/
def PrepareRejected (pkt : RxPacket) : Prop :=
  pkt.bytes.length = 0 ∨
  ¬ (pkt.bytes.length ≥ 20 ∧ ((pkt.bytes.headD 0).toNat / 16 = 4 ∨
    ((pkt.bytes.headD 0).toNat / 16 = 6 ∧ pkt.bytes.length ≥ 40))) ∨
  (ipTunnelParseProtocol pkt.bytes = 4 ∧ beAt pkt.bytes 2 2 < 20) ∨
  (ipTunnelParseProtocol pkt.bytes = 4 ∧ beAt pkt.bytes 2 2 > pkt.bytes.length) ∨
  (ipTunnelParseProtocol pkt.bytes = 6 ∧ beAt pkt.bytes 4 2 + 40 > pkt.bytes.length)

private theorem any_spec (a : Leanux.M α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  exact fun _ _ _ _ _ => True.intro

private theorem any_spec_ambient (a : WG.M α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  exact fun _ _ _ _ _ _ _ => True.intro

/-- Every normal None from the preparation factor has an actual named
keepalive/header/length cause. Literal false arms and protocol fallthrough
supply no extra reachable rejection. -/
theorem prepare_none (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ⦃fun _ => ⌜True⌝⦄ rxPrepare pid pkt ep
    ⦃⇓? result _ => ⌜result = none → PrepareRejected pkt⌝⦄ := by
  have hep := any_spec_ambient (setPeerEndpoint pid ep)
  have hk := any_spec_ambient (receivedWithKeypair pid pkt.keypair)
  have hh := any_spec_ambient (timersHandshakeComplete pid .walltimeLastHandshakeData)
  have hst := any_spec_ambient (sendStagedPackets pid)
  have hf := any_spec_ambient (keepKeyFreshRx pid)
  have ha := any_spec_ambient (timersAnyAuthenticatedPacketReceived pid)
  have ht := any_spec_ambient (timersTraversal pid)
  have hd := any_spec_ambient (timersDataReceived pid)
  have hstats := fun len => any_spec_ambient (updateRxStats pid len)
  have herr := fun why => any_spec_ambient (dishonest why)
  have hecn := fun protocol outer bytes => any_spec_ambient (inetEcnDecapsulate protocol outer bytes)
  mvcgen [rxPrepare, hep, hk, hh, hst, hf, ha, ht, hd, hstats, herr, hecn,
    WG.andM, WG.orM, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [PrepareRejected, ipTunnelParseProtocol]
  all_goals omega

/-- Complete normal-None classification, including the actual repaid lookup
route. No packet/key validity or initialized-state premise is used. -/
theorem none_classified (r : ConsumeReceipt) (hv : r.Valid) (hn : r.run.value = none) :
    PrepareRejected r.packet ∨
    ∃ ready u q routed paid middle afterLookup afterPaid,
      ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore = .ok ((some ready, u), middle) ∧
      ((lookupSrc ready.protocol ready.bytes).run u).run middle = .ok ((routed, q), afterLookup) ∧
      ((peerPut routed).run q).run afterLookup = .ok (((), paid), afterPaid) ∧ routed ≠ some r.peer ∧
      ((rxAfterLookup r.peer ready routed).run q).run afterLookup = .ok ((none, r.run.after), r.run.ambientAfter) := by
  rcases none_route r hv hn with h | h
  · exact Or.inl ((hoare_iff_run_ambient _ _ _).mp (prepare_none r.peer r.packet r.endpoint)
      r.run.before r.run.ambientBefore none r.run.after r.run.ambientAfter True.intro h rfl)
  · exact Or.inr h

end Leanux.Proofs.WG.Queues.RxDisposition
