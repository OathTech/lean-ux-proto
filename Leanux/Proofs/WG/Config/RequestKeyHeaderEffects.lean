import Leanux.Proofs.WG.Config.RequestKeyHeaderModel
import Leanux.Proofs.WG.Config.RequestInputEffects

/-! Pure history extension, header projections and scalar extraction. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
open Leanux Leanux.WG TimerDiscipline

theorem PortOrigin.mono {attrs : DeviceAttrs} {initial : Campaign2.State}
    {h k : List Receipt} {actual : Option Nat}
    (subset : ∀r,r∈h→r∈k) (pre : PortOrigin attrs initial h actual) :
    PortOrigin attrs initial k actual := by
  cases port : attrs.listenPort with
  | none => simpa only [PortOrigin,port] using pre
  | some p =>
    simp only [PortOrigin,port] at pre ⊢
    obtain ⟨r,member,kind,zero,same⟩:=pre
    exact ⟨r,subset r member,kind,zero,same⟩

theorem At.mono {attrs : DeviceAttrs} {initial current : Campaign2.State}
    {h k : List Receipt} (subset : ∀r,r∈h→r∈k) (pre : At attrs initial h current) :
    At attrs initial k current := ⟨pre.1,pre.2.mono subset⟩

theorem History.append {attrs : DeviceAttrs} {initial : Campaign2.State}
    {h k : List Receipt} (pre : History attrs initial h)
    (fresh : ∀r∈k,r.kind=.keyStage→At attrs initial (h++k) r.before.wg) :
    History attrs initial (h++k) := by
  intro r member kind
  rcases List.mem_append.mp member with old | new
  · exact (pre r old kind).mono (fun _ seen=>List.mem_append_left _ seen)
  · exact fresh r new kind

theorem At.header {attrs : DeviceAttrs} {initial current next : Campaign2.State}
    {h : List Receipt} (pre : At attrs initial h current)
    (same : next.device.map sendConfiguration=current.device.map sendConfiguration) :
    At attrs initial h next := by
  have fixedEq := congrArg (fun m=>m.map (fun v : SendConfiguration=>
    (v.1,v.2.1,0,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2))) same
  have portEq := congrArg (fun m=>m.map (fun v : SendConfiguration=>v.2.2.1)) same
  simp only [Option.map_map,Function.comp_def] at fixedEq portEq
  change next.device.map fixed=current.device.map fixed at fixedEq
  change next.device.map Device.incomingPort=current.device.map Device.incomingPort at portEq
  exact ⟨fixedEq.trans pre.1,portEq ▸ pre.2⟩

theorem MarkInput.core {attrs : DeviceAttrs} {initial current : Campaign2.State}
    (pre : MarkInput attrs (incrementState initial) current) : CoreInput attrs initial current := by
  have fields := congrArg (fun m=>m.map fixed) pre.1
  simp only [incrementState,Option.map_map,Function.comp_def] at fields
  exact fields

theorem MarkInput.portless {attrs : DeviceAttrs} {initial current : Campaign2.State}
    {h : List Receipt} (none : attrs.listenPort=Option.none)
    (pre : MarkInput attrs (incrementState initial) current) : At attrs initial h current := by
  refine ⟨MarkInput.core pre,?_⟩
  have fields := congrArg (fun m=>m.map Device.incomingPort) pre.1
  simpa only [PortOrigin,none,incrementState,Option.map_map,Function.comp_def,markDevice,
    withoutPeers] using fields

theorem At.resident {attrs : DeviceAttrs} {initial current : Campaign2.State}
    {h : List Receipt} (pre : At attrs initial h current) (d : Device)
    (device : initial.device=some d) :
    ∃ after,current.device=some after ∧ Fields attrs d after ∧
      PortOrigin attrs initial h (some after.incomingPort) := by
  have projected : current.device.map fixed=some (fixed (prefixDevice attrs d)) := by
    simpa only [CoreInput,device,Option.map_some] using pre.1
  obtain ⟨after,present,same⟩:=Option.map_eq_some_iff.mp projected
  refine ⟨after,present,?_,?_⟩
  · simpa [Fields,fixed,sendConfiguration,prefixDevice] using same
  · simpa only [present,Option.map_some] using pre.2

theorem portOutcome_success (d : Device) (port : Nat) (bound : Nat→Bool)
    (ok : (portOutcome d port bound).1=0) :
    (portOutcome d port bound).2.incomingPort=port := by
  unfold portOutcome socketOutcome at ok ⊢
  split <;> simp_all
  split <;> simp_all [ENONET]
  split <;> simp_all [EADDRINUSE]

end Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
