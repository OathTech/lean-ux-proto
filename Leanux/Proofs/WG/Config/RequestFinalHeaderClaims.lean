import Leanux.Proofs.WG.Config.RequestFinalHeaderSource
import Leanux.Proofs.WG.Config.RequestKeyHeaderClaims
import Leanux.Proofs.WG.Config.KeyIdentityClaims

/-! Original-entry header, private-key and selector consequences for a normal request with an actual completed key-stage receipt. The return code may be a later peer-command errno; Stops retain no claimed final state. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
open Leanux Leanux.WG Noise TimerDiscipline
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem receipt_header (attrs : DeviceAttrs) (r : Receipt)
    (valid : Valid attrs r) (kind : r.kind=.keyStage) :
    r.after.wg.device.map header=r.before.wg.device.map header := by
  have contract : Campaign2.Ensures (keyStage attrs)
      (fun s=>s.wg.device.map header=r.before.wg.device.map header)
      (fun _ s=>s.wg.device.map header=r.before.wg.device.map header) := by
    intro g a ret v b pre run
    exact ((ProjectedAction.iff_run_ambient _ _ _).mp (stage attrs) g a ret v b run).trans pre
  exact valid.ensures kind contract rfl

theorem certificate_final_fields (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d) :
    ∃ current,final.wg.device=some current ∧ Fields attrs d current ∧
      PortSelected attrs d current.incomingPort := by
  obtain ⟨before,beforePresent,fields,origin⟩:=
    KeyHeader.certificate_key_fields attrs initial result certificate r member key d device
  have receipt:=receipt_header attrs r (certificate.1.2.1 r member) key
  have suffix:=certificate_key_final_metadata attrs initial result certificate ret final normal r member key
  have projection:=congrArg (fun m=>m.map (fun v : SendConfiguration × SendSocketContext=>
    (v.1.1,v.1.2.1,v.1.2.2.1,v.1.2.2.2.1,v.1.2.2.2.2.2))) suffix
  have endpoint : final.wg.device.map header=some (header before) := by
    have source : r.after.wg.device.map header=final.wg.device.map header := by
      cases left : r.after.wg.device <;> cases right : final.wg.device <;>
        simp_all [getterMetadataObservation,header,sendConfiguration]
    rw [←source,receipt,beforePresent]
    rfl
  obtain ⟨current,present,same⟩:=Option.map_eq_some_iff.mp endpoint
  refine ⟨current,present,?_,?_⟩
  · exact And.intro ((congrArg (fun x:Header=>x.1) same).trans fields.1)
       (And.intro ((congrArg (fun x:Header=>x.2.1) same).trans fields.2.1)
        (And.intro ((congrArg (fun x:Header=>x.2.2.2.1) same).trans fields.2.2.1)
         ((congrArg (fun x:Header=>x.2.2.2.2) same).trans fields.2.2.2.2)))
  · have port : current.incomingPort=before.incomingPort:=congrArg (fun x:Header=>x.2.2.1) same
    cases selected : attrs.listenPort with
    | none =>
      obtain ⟨v,present,_,value⟩:=KeyHeader.certificate_key_no_port attrs initial result certificate
        r member key d device selected
      have eq: v=before:=Option.some.inj (present.symm.trans beforePresent)
      subst v
      simpa only [PortSelected,selected] using port.trans value
    | some requested =>
      by_cases zero : requested=0
      · subst requested
        obtain ⟨v,present,_,value⟩:=KeyHeader.certificate_key_zero_port attrs initial result certificate
          r member key d device selected
        have eq: v=before:=Option.some.inj (present.symm.trans beforePresent)
        subst v
        simpa only [PortSelected,selected,ite_true,port] using value
      · obtain ⟨v,present,_,value⟩:=KeyHeader.certificate_key_nonzero_port attrs initial result certificate
          r member key d device requested selected zero
        have eq: v=before:=Option.some.inj (present.symm.trans beforePresent)
        subst v
        simpa only [PortSelected,selected,zero,ite_false] using port.trans value

theorem certificate_final_private (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (key : Key) (given : attrs.privateKey=some key) :
    ∃ current,final.wg.device=some current ∧ Fields attrs d current ∧
      PortSelected attrs d current.incomingPort ∧
      current.staticIdentity.staticPrivate=
        if d.staticIdentity.staticPrivate=key then key else clamp key := by
  obtain ⟨current,present,fields,port⟩:=
    certificate_final_fields attrs initial result certificate ret final normal r member kind d device
  obtain ⟨before,after,beforePresent,afterPresent,privateValue⟩:=
    KeyStage.certificate_final_private cs loans attrs initial result certificate pre
      ret final normal r member kind key given
  have afterEq : after=current:=Option.some.inj (afterPresent.symm.trans present)
  subst after
  obtain ⟨selected,selectedPresent,entryFields,_⟩:=
    KeyHeader.certificate_key_fields attrs initial result certificate r member kind d device
  have beforeEq : selected=before:=Option.some.inj (selectedPresent.symm.trans beforePresent)
  subst selected
  exact ⟨current,present,fields,port,by simpa only [entryFields.2.2.2.1] using privateValue⟩

theorem certificate_final_unchanged_identity (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (unchanged : attrs.privateKey=none ∨ attrs.privateKey=some d.staticIdentity.staticPrivate) :
    ∃ current,final.wg.device=some current ∧ Fields attrs d current ∧
      PortSelected attrs d current.incomingPort ∧ current.staticIdentity=d.staticIdentity := by
  obtain ⟨current,present,fields,port⟩:=
    certificate_final_fields attrs initial result certificate ret final normal r member kind d device
  obtain ⟨before,after,beforePresent,afterPresent,identity⟩:=
    KeyStage.certificate_final_identity cs loans attrs initial result certificate pre
      ret final normal r member kind
  have afterEq : after=current:=Option.some.inj (afterPresent.symm.trans present)
  subst after
  obtain ⟨selected,selectedPresent,entryFields,_⟩:=
    KeyHeader.certificate_key_fields attrs initial result certificate r member kind d device
  have beforeEq : selected=before:=Option.some.inj (selectedPresent.symm.trans beforePresent)
  subst selected
  refine ⟨current,present,fields,port,?_⟩
  rcases unchanged with none | same
  · simpa only [KeyStage.IdentityEffect,none,entryFields.2.2.2.1] using identity
  · simpa only [KeyStage.IdentityEffect,same,entryFields.2.2.2.1,ite_true] using identity

theorem certificate_context (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (before after : Device) (first : initial.wg.device=some before)
    (last : final.wg.device=some after) :
    final.wg.nlSock7=initial.wg.nlSock7 ∧
      final.wg.fixtureNetDevices=initial.wg.fixtureNetDevices := by
  have same:=matches_normal_ensures attrs initial result certificate.1.1 ret final normal _ _
    (GetterContext.original_request_context attrs (GetterContext.observation initial)) rfl
  simpa only [GetterContext.observation,getterMetadataObservation,first,last,
    Option.map_some,Option.some.injEq,Prod.mk.injEq] using same

theorem certificate_selector (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (before after : Device) (first : initial.wg.device=some before)
    (last : final.wg.device=some after) (fields : Fields attrs before after)
    (selected : ClaimView.selectsDevice initial before) :
    ClaimView.selectsDevice final after := by
  have same:=certificate_context attrs initial result certificate ret final normal before after first last
  simpa only [ClaimView.selectsDevice,same.2,fields.1,fields.2.1] using selected

theorem certificate_requested_private (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (before : Device) (first : initial.wg.device=some before)
    (current : Device) (present : final.wg.device=some current) :
    Fields attrs before current ∧ PortSelected attrs before current.incomingPort ∧
      current.staticIdentity.staticPrivate=requestedPrivate attrs before := by
  cases given : attrs.privateKey with
  | none =>
    obtain ⟨out,found,fields,port,identity⟩:=certificate_final_unchanged_identity
      cs loans attrs initial result certificate pre ret final normal r member kind
      before first (Or.inl given)
    have equal : out=current:=Option.some.inj (found.symm.trans present)
    subst out
    exact ⟨fields,port,by simp only [requestedPrivate,given,identity]⟩
  | some key =>
    obtain ⟨out,found,fields,port,value⟩:=certificate_final_private
      cs loans attrs initial result certificate pre ret final normal r member kind
      before first key given
    have equal : out=current:=Option.some.inj (found.symm.trans present)
    subst out
    exact ⟨fields,port,by simpa only [requestedPrivate,given] using value⟩


end Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
