import Leanux.Proofs.WG.Packets.RoutingCuts

/-! An actual transmit source cut ends immediately after the staged splice.
The following send/payment tail may stop. This native factor does not introduce
an observer or claim initialized reachability. -/
namespace Leanux.Proofs.WG.Packets
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open AllowedIps Lifetimes CounterWindow

/-- The original front, including every early errno arm and both splice getters. -/
def txFront (family addr : Nat) (pkts : List Packet) (mtu : Nat) : WG.M (Except Int PeerId) := do
  if !(← txCheck family addr pkts mtu) then return .error (-EPROTONOSUPPORT)
  let peer ← lookupDst family addr
  match ← txSelect family pkts mtu peer with
  | .error err => return .error err
  | .ok (pid, packets) =>
    xmitSplice pid packets
    return .ok pid

/-- The unchanged native suffix after the handoff. -/
def txTail (pid : PeerId) : WG.M Int := do
  sendStagedPackets pid
  peerPut (some pid)
  pure 0

/-- Literal factoring is valid for every outcome, including a stopped tail. -/
theorem wgXmit_front_factor (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    wgXmit family addr pkts mtu = (do
      match ← txFront family addr pkts mtu with
      | .error err => pure err
      | .ok pid => txTail pid) := by
  rw [wgXmit_factor]
  simp only [txFront,txTail,txFinish,bind_assoc]
  apply congrArg
  funext ok
  cases ok <;> simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true,bind_assoc,pure_bind]
  apply congrArg
  funext peer
  apply congrArg
  funext selected
  cases selected with
  | error err => rfl
  | ok pair => cases pair; simp only [bind_assoc,pure_bind]

/-- Connected native receipts ending at the completed splice. There is no
hypothesis about the subsequent send/payment result. -/
def TxFrontCut (family addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w s : WGWorld) (ambient afterSplice : Ambient) (pid : PeerId) : Prop :=
  ∃ u q r a b c,
    ((txCheck family addr pkts mtu).run w).run ambient = .ok ((true,u),a) ∧
    ((lookupDst family addr).run u).run a = .ok ((some pid,q),b) ∧
    ((txSelect family pkts mtu (some pid)).run q).run b =
      .ok ((.ok (pid,pkts.map (fun pkt => {pkt with mtu})),r),c) ∧
    ((xmitSplice pid (pkts.map (fun pkt => {pkt with mtu}))).run r).run c = .ok (((),s),afterSplice)

theorem txFront_cut (family addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w s : WGWorld) (ambient afterSplice : Ambient) (pid : PeerId)
    (hr : ((txFront family addr pkts mtu).run w).run ambient = .ok ((.ok pid,s),afterSplice)) :
    TxFrontCut family addr pkts mtu w s ambient afterSplice pid := by
  unfold txFront at hr
  simp only [StateT.run_bind] at hr
  cases hc : ((txCheck family addr pkts mtu).run w).run ambient with
  | error e => simp [hc] at hr
  | ok out =>
    rcases out with ⟨⟨ok,u⟩,a⟩
    cases ok with
    | false => simp [hc] at hr
    | true =>
      simp only [hc,except_ok_bind,Bool.not_true,Bool.false_eq_true,ite_false] at hr
      simp only [StateT.run_bind] at hr
      cases hq : ((lookupDst family addr).run u).run a with
      | error e => simp [hq] at hr
      | ok out =>
        rcases out with ⟨⟨peer,q⟩,b⟩
        simp only [hq,except_ok_bind] at hr
        cases hs : ((txSelect family pkts mtu peer).run q).run b with
        | error e => simp [hs] at hr
        | ok out =>
          rcases out with ⟨⟨selected,r⟩,c⟩
          have valid := (hoare_iff_run_ambient _ _ _).mp (txSelect_spec family pkts mtu peer)
            q b selected r c True.intro hs
          cases selected with
          | error err => simp [hs] at hr
          | ok pair =>
            rcases pair with ⟨owner,packets⟩
            obtain ⟨rfl,rfl⟩ := valid
            simp only [hs,except_ok_bind,StateT.run_bind] at hr
            cases hh : ((xmitSplice owner (pkts.map (fun pkt => {pkt with mtu}))).run r).run c with
            | error e => simp [hh] at hr
            | ok out =>
              rcases out with ⟨⟨⟨⟩,final⟩,d⟩
              simp only [hh,except_ok_bind,StateT.run_pure] at hr
              obtain ⟨⟨rfl,rfl⟩,rfl⟩ := hr
              exact ⟨u,q,r,a,b,c,hc,hq,hs,hh⟩

/-- These connected receipts are exactly the normal successful front run. -/
theorem TxFrontCut.run (cut : TxFrontCut family addr pkts mtu w s ambient afterSplice pid) :
    ((txFront family addr pkts mtu).run w).run ambient = .ok ((.ok pid,s),afterSplice) := by
  obtain ⟨u,q,r,a,b,c,check,lookup,select,splice⟩ := cut
  unfold txFront
  simp only [StateT.run_bind,check,except_ok_bind,Bool.not_true,Bool.false_eq_true,ite_false,
    lookup,select,splice,StateT.run_pure]
  rfl

/-- The earlier normal-return contract contains this cut and its separately
successful tail. Its original stronger contract is left unchanged. -/
theorem TxHandoff.front (handoff : TxHandoff family addr pkts mtu w v ambient ambient' pid) :
    ∃ s afterSplice,
      ((txFront family addr pkts mtu).run w).run ambient = .ok ((.ok pid,s),afterSplice) ∧
      ((txTail pid).run s).run afterSplice = .ok ((0,v),ambient') := by
  obtain ⟨u,q,r,s,a,b,c,d,check,lookup,select,splice,tail⟩ := handoff
  exact ⟨s,d,TxFrontCut.run ⟨u,q,r,a,b,c,check,lookup,select,splice⟩,tail⟩

/-- Authorization is established at the actual completed handoff, before
any possible failure of sendStagedPackets or the final payment. -/
theorem txFront_authorized (v4 : Bool) (addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w s : WGWorld) (ambient afterSplice : Ambient) (pid : PeerId)
    (xs : FlatTable × FlatTable) (hi : RoutedView (routingView w) xs)
    (hr : ((txFront (if v4 then 4 else 6) addr pkts mtu).run w).run ambient =
      .ok ((.ok pid,s),afterSplice)) :
    TxFrontCut (if v4 then 4 else 6) addr pkts mtu w s ambient afterSplice pid ∧
      PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) (some pid) ∧
      ∀ pkt ∈ pkts, destinationField (if v4 then 4 else 6) pkt.bytes = addr := by
  have cut := txFront_cut _ addr pkts mtu w s ambient afterSplice pid hr
  have saved := cut
  obtain ⟨u,q,r,a,b,c,hc,hq,_,_⟩ := cut
  have valid := (hoare_iff_run_ambient _ _ _).mp (txCheck_valid _ addr pkts mtu)
    w ambient true u a True.intro hc rfl
  have routing : RoutedView (routingView u) xs := by
    rw [(ProjectedAction.iff_run_ambient _ _ _).mp
      (txCheck_routing _ addr pkts mtu) w ambient true u a hc]
    exact hi
  have bound : addr < 2 ^ rootWidth v4 := by
    cases pkts with
    | nil => exact False.elim (valid.1 rfl)
    | cons packet rest =>
      rw [← valid.2 packet (by simp)]
      exact destinationField_bound v4 packet.bytes
  exact ⟨saved,lookupDst_normal u q a b xs v4 addr bound (some pid) routing hq,valid.2⟩

/-- The whole source run has precisely the tail's outcome after a successful
front. In particular an error here does not erase the completed splice cut. -/
theorem wgXmit_after_front (family addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w s : WGWorld) (ambient afterSplice : Ambient) (pid : PeerId)
    (front : ((txFront family addr pkts mtu).run w).run ambient = .ok ((.ok pid,s),afterSplice)) :
    ((wgXmit family addr pkts mtu).run w).run ambient = ((txTail pid).run s).run afterSplice := by
  rw [wgXmit_front_factor]
  simp only [StateT.run_bind,front,except_ok_bind]

/-- Authorization survives a later actual source Stop. The failure remains
the whole call's result; no final World or wire transmission is invented. -/
theorem wgXmit_stopped_after_handoff (v4 : Bool) (addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w s : WGWorld) (ambient afterSplice : Ambient) (pid : PeerId)
    (xs : FlatTable × FlatTable) (stop : Stop)
    (routing : RoutedView (routingView w) xs)
    (front : ((txFront (if v4 then 4 else 6) addr pkts mtu).run w).run ambient =
      .ok ((.ok pid,s),afterSplice))
    (tail : ((txTail pid).run s).run afterSplice = .error stop) :
    ((wgXmit (if v4 then 4 else 6) addr pkts mtu).run w).run ambient = .error stop ∧
      TxFrontCut (if v4 then 4 else 6) addr pkts mtu w s ambient afterSplice pid ∧
      PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) (some pid) ∧
      ∀ pkt ∈ pkts, destinationField (if v4 then 4 else 6) pkt.bytes = addr :=
  ⟨(wgXmit_after_front _ addr pkts mtu w s ambient afterSplice pid front).trans tail,
    txFront_authorized v4 addr pkts mtu w s ambient afterSplice pid xs routing front⟩

end Leanux.Proofs.WG.Packets
