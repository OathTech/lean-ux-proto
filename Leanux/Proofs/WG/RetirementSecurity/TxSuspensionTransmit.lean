import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionRx

/-! Routed transmit preserves suspended actors through the original selected
peer reference, plaintext edits, staged allocation and refusal bookkeeping. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem trim (pid : PeerId) : Keeps (xmitTrim pid) := by
  suspension_source [xmitTrim] using [peer,modify_device,set_peer,branch]

theorem splice (pid : PeerId) (packets : List WG.Packet) : Keeps (xmitSplice pid packets) := by
  suspension_source [xmitSplice] using [peer,set_peer]

theorem env_ok (site : EnvSite) : Keeps (envOk site : WG.M Bool) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.envOk at run
  simp only [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  obtain ⟨_,u,written,returned⟩:=tail
  cases written
  cases returned
  rfl

theorem route_call (family src dst : Nat) : Keeps (monadLift (Net.routeLookup family src dst) : WG.M (Except Int Route)) :=
  routing_call (route family src dst)

theorem route_output_call (src dst : Nat) : Keeps (monadLift (Net.routeOutput4 src dst) : WG.M (Except Int Route)) :=
  routing_call (route_output src dst)

theorem inet_type_call (dev : Option Nat) (addr : Nat) : Keeps (monadLift (Net.Fib.inetDevAddrType dev addr) : WG.M Net.Fib.RouteType) :=
  routing_call (inet_type dev addr)

theorem neighbour_call (dev : Nat) : Keeps (monadLift (Net.neighbourClassify dev) : WG.M Unit) :=
  routing_call (neighbour dev)

theorem front (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Keeps (Packets.txFront family addr packets mtu) := by
  suspension_source [Packets.txFront,Packets.txCheck,Packets.txSelect,Packets.txError,
      Packets.txHeaders,Packets.txWalk,WG.andM]
    using [peer,lookup_dst,trim,splice,peer_put,loopback,branch,invariant,unsupported,
      cut_sites,env_ok,modify_device,route_call,route_output_call,inet_type_call,neighbour_call]

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Keeps (wgXmit family addr packets mtu) := by
  rw [Packets.wgXmit_front_factor]
  suspension_source [Packets.txTail] using [front,staged,peer_put]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
