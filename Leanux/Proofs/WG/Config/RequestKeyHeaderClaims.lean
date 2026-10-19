import Leanux.Proofs.WG.Config.RequestKeyHeaderSource

/-! Whole-request key-entry fields from actual completed receipts, on normal outcomes and before later Stops. No initial namespace permission, account, address-shape or successful-request premise is supplied. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
open Leanux Leanux.WG TimerDiscipline

theorem certificate_history (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result) :
    History attrs initial.wg result.receipts := by
  obtain ⟨g,a,rfl,rfl⟩:=certificate.1.1
  exact inspection_history attrs g a

theorem original_request (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun initial outcome=>∃ result : Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧ History attrs initial.wg result.receipts) := by
  intro g a _
  exact ⟨inspection attrs g a,inspection_outcome attrs g a,inspection_certificate attrs g a,
    inspection_history attrs g a⟩

theorem receipt_nonzero_selected (attrs : DeviceAttrs) (r : Receipt) (port : Nat)
    (valid : Valid attrs r) (kind : r.kind=.port port) (nonzero : port≠0)
    (d : Device) (device : r.before.wg.device=some d) (ok : r.result=0) :
    r.after.wg.device.map Device.incomingPort=some port := by
  have effect:=receipt_nonzero_port attrs r valid port kind d nonzero device
  by_cases same : d.incomingPort=port
  · simp only [same,ite_true] at effect
    rw [effect.2]
    simp only [Option.map_some,same]
  · simp only [same,ite_false] at effect
    have result : (portOutcome d port r.before.wg.portBound).1=0:=effect.1.symm.trans ok
    have fields:=congrArg (fun m=>m.map Device.incomingPort) effect.2.1
    simpa only [Option.map_map,Function.comp_def,Option.map_some,withoutPeers,
      portOutcome_success d port r.before.wg.portBound result] using fields

theorem certificate_key_fields (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d) :
    ∃ current,r.before.wg.device=some current ∧ Fields attrs d current ∧
      PortOrigin attrs initial.wg result.receipts (some current.incomingPort) :=
  ((certificate_history attrs initial result certificate) r member key).resident d device

theorem certificate_key_nonzero_port (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (port : Nat) (selected : attrs.listenPort=some port) (nonzero : port≠0) :
    ∃ current,r.before.wg.device=some current ∧ Fields attrs d current ∧
      current.incomingPort=port := by
  obtain ⟨current,present,fields,origin⟩:=
    certificate_key_fields attrs initial result certificate r member key d device
  simp only [PortOrigin,selected] at origin
  obtain ⟨p,inHistory,kind,ok,actual⟩:=origin
  have input:=certificate_port_input attrs initial result certificate p inHistory port kind
  obtain ⟨before,beforePresent,_,_,_⟩:=input.resident d device
  have effect:=receipt_nonzero_selected attrs p port (certificate.1.2.1 p inHistory)
    kind nonzero before beforePresent ok
  exact ⟨current,present,fields,Option.some.inj (actual.trans effect)⟩

theorem certificate_port_permission (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts)
    (d : Device) (device : initial.wg.device=some d)
    (port : Nat) (selected : attrs.listenPort=some port) :
    d.creatingNet=true := by
  obtain ⟨g,a,entry,observed⟩:=certificate.1.1
  cases net : d.creatingNet with
  | true => rfl
  | false =>
    have native : g.dev=some d := by simpa only [←entry,Campaign2.snapshot,Campaign2.core] using device
    have empty:=no_net_history attrs port selected (accepted attrs) d net g a native []
    have noReceipt : result.receipts=[] := by
      rw [←observed]
      exact empty
    simp only [noReceipt,List.not_mem_nil] at member

theorem certificate_key_no_port (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (selected : attrs.listenPort=none) :
    ∃ current,r.before.wg.device=some current ∧ Fields attrs d current ∧
      current.incomingPort=d.incomingPort := by
  obtain ⟨current,present,fields,origin⟩:=
    certificate_key_fields attrs initial result certificate r member key d device
  exact ⟨current,present,fields,by simpa only [PortOrigin,selected,device,Option.map_some,
    Option.some.injEq] using origin⟩

theorem certificate_key_zero_port (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (selected : attrs.listenPort=some 0) :
    ∃ current,r.before.wg.device=some current ∧ Fields attrs d current ∧
      ZeroPortRequestChoice d current.incomingPort := by
  obtain ⟨current,present,fields,origin⟩:=
    certificate_key_fields attrs initial result certificate r member key d device
  simp only [PortOrigin,selected] at origin
  obtain ⟨p,inHistory,kind,_,actual⟩:=origin
  have input:=certificate_port_input attrs initial result certificate p inHistory 0 kind
  obtain ⟨before,beforePresent,header,_⟩:=input.resident d device
  have permission:=certificate_port_permission attrs initial result certificate r member d device 0 selected
  have net : before.creatingNet=true := (congrArg Device.creatingNet header).trans permission
  have port : before.incomingPort=d.incomingPort := by simpa only [withoutPeers,prefixDevice] using congrArg Device.incomingPort header
  have running : before.running=d.running := by simpa only [withoutPeers,prefixDevice] using congrArg Device.running header
  have effect:=(receipt_zero_port attrs p (certificate.1.2.1 p inHistory) kind before net beforePresent).2
  refine ⟨current,present,fields,?_⟩
  unfold ClaimView.zeroPortEffects at effect
  simp only [port,running] at effect
  by_cases same : d.incomingPort=0
  · simp only [same,ite_true] at effect
    have scalar : current.incomingPort=0 := by simpa only [effect,Option.map_some,
      Option.some.injEq,port,same] using actual
    simpa only [ZeroPortRequestChoice,same,ite_true] using scalar
  · simp only [same,ite_false] at effect
    cases live : d.running with
    | false =>
      simp only [live,Bool.false_eq_true,ite_false] at effect
      have scalar := congrArg (fun o=>o.map Device.incomingPort) effect.2
      have done : current.incomingPort=0 := by
        simpa only [Option.map_map,Function.comp_def,withoutPeers,Option.map_some,
          ←actual,Option.some.injEq] using scalar
      simpa only [ZeroPortRequestChoice,same,ite_false,live,Bool.false_eq_true] using done
    | true =>
      simp only [live,ite_true] at effect
      obtain ⟨chosen,low,high,changed⟩:=effect.2
      have scalar := congrArg (fun o=>o.map Device.incomingPort) changed
      have done : current.incomingPort=chosen := by
        simpa only [Option.map_map,Function.comp_def,withoutPeers,Option.map_some,
          ←actual,Option.some.injEq] using scalar
      simpa only [ZeroPortRequestChoice,same,ite_false,live,ite_true,done] using And.intro low high

end Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
