import C1ServiceCallbackText
import CallbackLeafHistory

/-! The shared callbacks in the form the allowed-IPs results consume
(`TrustBase.AllowedipsServiceReturns`: the landed contract, and no state inside
the callback at an instruction of the allowed-IPs image), from agreement on
the shared service bodies alone. The landed leaf proofs (`pc_run`,
`const_cmp1_run`, `const_cmp4_run`, `bh_run`) are used as they stand.

This module depends on landed modules only (nothing of result C1). -/
namespace Binary.Callback.Text
open TrustBase
local instance : Labels := Image.linkedLabels

/-- A leaf run over the service image gives the allowed-IPs form of its contract. -/
theorem allowedips_service {fetch address ready writes effect}
    (agree : ServiceDecoderAgreement fetch)
    (run : ∀ s ra, s.pc=address → ready s → EntryFrame s ra →
      Eventually (guardedStep ServiceImage.fetch (leafGuard s.data.regs.rsp))
        (fun t => Returned s t ra ∧ EqualOutside (writes s) s.data.dmem t.data.dmem ∧ effect s t) s) :
    AllowedipsServiceReturns fetch address ready writes effect := by
  intro s ra pc ready frame
  have guarded : Eventually (guardedStep fetch
      (fun q => leafGuard s.data.regs.rsp q ∧ AllowedipsImage.fetch q.pc = none)) _ s :=
    guarded_agreement agree (change_guard (fun q inside => ⟨inside.1,service_apart inside.2⟩)
      (in_service (run s ra pc ready frame)))
  have history := guarded_history fetch _ _ s guarded [] (by simp)
  apply eventually_weaken (historyStep fetch) _ _ _ _ history
  rintro t ⟨⟨returned,framed,effect⟩,interior⟩
  exact ⟨returned,framed,effect,fun q member => (interior q member).1.2,
    fun q member => (interior q member).2⟩

theorem pc_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    AllowedipsTracePcContract fetch := by
  apply allowedips_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact pc_run s ra ready frame

theorem const_cmp1_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    AllowedipsTraceConstCmp1Contract fetch := by
  apply allowedips_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact const_cmp1_run s ra ready frame

theorem const_cmp4_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    AllowedipsTraceConstCmp4Contract fetch := by
  apply allowedips_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact const_cmp4_run s ra ready frame

theorem bh_contract (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    AllowedipsBhEnableContract fetch := by
  apply allowedips_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  rcases ready with ⟨count,read,hardirq,pending,apart⟩
  apply eventually_weaken (guardedStep ServiceImage.fetch (leafGuard s.regs.rsp))
    _ _ _ _ (bh_run s ra count read hardirq pending apart frame)
  rintro t ⟨returned,framed,changed⟩
  refine ⟨returned,framed,?_⟩
  intro old oldRead
  have equal : old=count := by
    apply BitVec.eq_of_toNat_eq
    exact_mod_cast Option.some.inj (oldRead.symm.trans read)
  subst old
  exact changed

#print axioms pc_contract
#print axioms const_cmp1_contract
#print axioms const_cmp4_contract
#print axioms bh_contract
end Binary.Callback.Text
