import CallbackGuarded
import HistoryGuard
import ServiceObservation

namespace Binary.Callback
open TrustBase
local instance : Labels := Image.linkedLabels

/-- A proved leaf-service interface retaining its actual history and fixed
interior stack. This is a conclusion of image execution, never a new premise
of a public refinement theorem. -/
def LeafService (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s ra, s.pc=address → ready s → EntryFrame s ra →
    Eventually (historyStep fetch) (fun t =>
      Returned s t.machine ra ∧ EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
      effect s t.machine ∧ ∀ q∈t.history.dropLast, leafGuard s.data.regs.rsp q) ⟨s,[s]⟩

theorem leaf_history {fetch address ready writes effect}
    (agree : ServiceDecoderAgreement fetch)
    (run : ∀ s ra, s.pc=address → ready s → EntryFrame s ra →
      Eventually (guardedStep ServiceImage.fetch (leafGuard s.data.regs.rsp))
        (fun t => Returned s t ra ∧ EqualOutside (writes s) s.data.dmem t.data.dmem ∧ effect s t) s) :
    LeafService fetch address ready writes effect := by
  intro s ra pc ready frame
  have history := guarded_history fetch _ _ s (guarded_agreement agree (run s ra pc ready frame)) [] (by simp)
  apply eventually_weaken (historyStep fetch) _ _ _ _ history
  rintro t ⟨⟨returned,framed,effect⟩,interior⟩
  exact ⟨returned,framed,effect,interior⟩

theorem pc_leaf (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc) := by
  apply leaf_history agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact pc_run s ra ready frame

theorem cmp4_leaf (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4) := by
  apply leaf_history agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact cmp4_run s ra ready frame

theorem const_cmp4_leaf (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4) := by
  apply leaf_history agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact const_cmp4_run s ra ready frame

theorem const_cmp1_leaf (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch) :
    LeafService fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1) := by
  apply leaf_history agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact const_cmp1_run s ra ready frame

theorem LeafService.forget {fetch address ready writes effect}
    (leaf : LeafService fetch address ready writes effect) :
    ServiceReturns fetch address ready writes effect := by
  intro s ra pc ready frame
  apply eventually_weaken (historyStep fetch) _ _ _ _ (leaf s ra pc ready frame)
  rintro t ⟨ret,framed,effect,interior⟩
  exact ⟨ret,framed,effect,fun q hq => (interior q hq).2⟩

#print axioms pc_leaf
#print axioms cmp4_leaf
#print axioms const_cmp4_leaf
#print axioms const_cmp1_leaf
end Binary.Callback
