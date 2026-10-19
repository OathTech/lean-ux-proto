import Leanux.Proofs.WG.Config.RequestInputModel
import Leanux.Proofs.WG.Config.RequestOrderEffects
import Leanux.Proofs.WG.Config.RunningPort

/-! Pure receipt-language and field-transform composition; no execution state is reconstructed. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

theorem Portless.append {left right : List Receipt}
    (hl : Portless left) (hr : Portless right) : Portless (left ++ right) := by
  intro r member port
  rcases List.mem_append.mp member with old | new
  · exact hl r old port
  · exact hr r new port

theorem Portless.input {attrs : DeviceAttrs} {initial : Campaign2.State}
    {h : List Receipt} (point : Portless h) : InputHistory attrs initial h :=
  fun r member port kind => False.elim (point r member port kind)

theorem InputHistory.append {attrs : DeviceAttrs} {initial : Campaign2.State}
    {left right : List Receipt} (hl : InputHistory attrs initial left)
    (hr : InputHistory attrs initial right) : InputHistory attrs initial (left ++ right) := by
  intro r member port kind
  rcases List.mem_append.mp member with old | new
  · exact hl r old port kind
  · exact hr r new port kind

theorem event_portSilent (kind : Kind) (silent : ∀ port, kind ≠ .port port) :
    PortSilent (Language.event kind) := by
  intro h point
  rcases point with rfl | ⟨r,rfl,selected⟩
  · simp [Portless]
  · intro other member port k
    have equal : other = r := by simpa using member
    subst other
    exact silent port (selected.symm.trans k)

theorem bind_portSilent {α β : Type} {A : Language α} {B : α → Language β}
    (silent : PortSilent A) (prefixes : ∀ ret h, A.normal ret h → A.prefixes h)
    (next : ∀ ret, PortSilent (B ret)) : PortSilent (A.bind B) := by
  intro h point
  rcases point with first | ⟨ret,left,right,first,last,rfl⟩
  · exact silent h first
  · exact (silent left (prefixes ret left first)).append (next ret right last)

theorem peers_portSilent (attrs : DeviceAttrs) : PortSilent (Language.peers attrs) := by
  intro h point r member port kind
  have eq : peerReceipts h = h := PeerPartial.peerReceipts point
  have selected : r ∈ peerReceipts h := by rw [eq]; exact member
  simp only [peerReceipts,List.mem_filter] at selected
  cases k : r.kind <;> simp_all

theorem keyed_portSilent (attrs : DeviceAttrs) : PortSilent (keyedLanguage attrs) :=
  bind_portSilent (event_portSilent .keyStage (by intro p h; cases h))
    (by intro ret h point; obtain ⟨r,eq,k,_⟩ := point; exact Or.inr ⟨r,eq,k⟩)
    (fun _ => peers_portSilent attrs)

theorem afterPort_portSilent (attrs : DeviceAttrs) (flags : UInt32) :
    PortSilent (afterPortLanguage attrs flags) := by
  unfold afterPortLanguage
  split
  · exact bind_portSilent (event_portSilent .replacement (by intro p h; cases h))
      (by intro ret h point; obtain ⟨r,eq,k,_⟩ := point; exact Or.inr ⟨r,eq,k⟩)
      (fun _ => keyed_portSilent attrs)
  · exact keyed_portSilent attrs

theorem fwmarkObserved_portSilent (attrs : DeviceAttrs) :
    PortSilent (Language.closed (α := Unit) (ClearPrefix attrs)) := by
  intro h point r member port kind
  obtain ⟨pid,clear⟩ := point.1 r member
  cases clear.symm.trans kind

theorem PortInput.resident {attrs : DeviceAttrs} {initial : Campaign2.State}
    {r : Receipt} (point : PortInput attrs initial r) (d : Device)
    (entry : initial.device = some d) :
    ∃ current, r.before.wg.device = some current ∧
      withoutPeers current = withoutPeers (prefixDevice attrs d) ∧
      ClaimView.clearedPeers d r.before.wg.toCore
        (if attrs.fwmark.isSome then d.peerList else []) ∧
      r.before.wg.portBound = initial.portBound ∧
      r.before.wg.nlSock7 = initial.nlSock7 ∧
      r.before.wg.fixtureNetDevices = initial.fixtureNetDevices := by
  have header : r.before.wg.device.map withoutPeers =
      some (withoutPeers (prefixDevice attrs d)) := by
    simpa only [PortInput,MarkInput,incrementState,entry,Option.map_some,
      markDevice,prefixDevice] using point.1
  obtain ⟨current,resident,same⟩ := Option.map_eq_some_iff.mp header
  refine ⟨current,resident,same,?_,point.2.2⟩
  exact point.2.1 {d with deviceUpdateGen := d.deviceUpdateGen + 1}
    (by simp [incrementState,entry])

theorem clearedPeers_compose (initial middle : Device) (final : Campaign2.Core)
    (seen all : List PeerId) (subset : ∀ q, q ∈ seen → q ∈ all)
    (before : ClaimView.clearedPeers initial
      {final with device := some middle} seen)
    (after : ClaimView.clearedPeers middle final all) :
    ClaimView.clearedPeers initial final all := by
  intro q
  by_cases selected : q ∈ all
  · simp only [selected,ite_true]
    have selectedEffect := after q
    simp only [selected,ite_true] at selectedEffect
    obtain ⟨p,reset,resident,done⟩ := selectedEffect
    by_cases prior : q ∈ seen
    · obtain ⟨old,first,oldResident,oldState⟩ := by
        simpa only [ClaimView.clearedPeers,prior,ite_true,Option.bind_some] using before q
      have same : p = clearedSource old first := Option.some.inj (resident.symm.trans oldState)
      exact ⟨old,reset,oldResident,by simpa only [same,clearedSource_twice] using done⟩
    · have oldState : middle.peers[q]? = initial.peers[q]? := by
        simpa only [ClaimView.clearedPeers,prior,ite_false,Option.bind_some] using before q
      exact ⟨p,reset,oldState.symm.trans resident,done⟩
  · have prior : q ∉ seen := fun member => selected (subset q member)
    have oldState : middle.peers[q]? = initial.peers[q]? := by
      simpa only [ClaimView.clearedPeers,prior,ite_false,Option.bind_some] using before q
    simpa only [ClaimView.clearedPeers,selected,ite_false,oldState] using after q

theorem portOutcome_code_frame (left right : Device) (port : Nat) (bound : Nat → Bool)
    (same : withoutPeers left = withoutPeers right) :
    (portOutcome left port bound).1 = (portOutcome right port bound).1 := by
  have running := congrArg Device.running same
  have net := congrArg Device.creatingNet same
  have sock4 := congrArg Device.sock4 same
  have sock6 := congrArg Device.sock6 same
  change left.running = right.running at running
  change left.creatingNet = right.creatingNet at net
  change left.sock4 = right.sock4 at sock4
  change left.sock6 = right.sock6 at sock6
  simp only [portOutcome,socketOutcome,running,net,sock4,sock6]
  repeat' first | rfl | split

theorem portOutcome_refused (d : Device) (port : Nat) (bound : Nat → Bool)
    (refused : (portOutcome d port bound).1 ≠ 0) :
    (portOutcome d port bound).2 = d := by
  unfold portOutcome socketOutcome at refused ⊢
  split at refused <;> simp_all
  split at refused <;> simp_all
  split at refused <;> simp_all

end Leanux.Proofs.WG.Config.RequestOrder
