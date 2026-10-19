import Leanux.Proofs.WG.Config.RequestOrderEffects
/-! Pure normal-request language classification; all prefixes retain their existing meaning. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

theorem keyed_normal_has_key (attrs : DeviceAttrs) (ret : Int) (h : List Receipt)
    (normal : (keyedLanguage attrs).normal ret h) :
    ∃ r ∈ h, r.kind = .keyStage := by
  obtain ⟨_,left,right,⟨r,rfl,kind,_⟩,_,rfl⟩ := normal
  exact ⟨r,List.mem_append_left _ (List.mem_singleton_self _),kind⟩

theorem afterPort_normal_has_key (attrs : DeviceAttrs) (flags : UInt32)
    (ret : Int) (h : List Receipt)
    (normal : (afterPortLanguage attrs flags).normal ret h) :
    ∃ r ∈ h, r.kind = .keyStage := by
  unfold afterPortLanguage at normal
  split at normal
  · obtain ⟨_,left,right,_,done,rfl⟩ := normal
    obtain ⟨r,member,kind⟩ := keyed_normal_has_key attrs ret right done
    exact ⟨r,List.mem_append_right _ member,kind⟩
  · exact keyed_normal_has_key attrs ret h normal

theorem afterFwmark_normal_cases (attrs : DeviceAttrs) (flags : UInt32)
    (ret : Int) (h : List Receipt)
    (normal : (afterFwmarkLanguage attrs flags).normal ret h) :
    (∃ port r, attrs.listenPort = some port ∧ r ∈ h ∧
      r.kind = .port port ∧ r.result ≠ 0) ∨
    ∃ r ∈ h, r.kind = .keyStage := by
  unfold afterFwmarkLanguage at normal
  split at normal
  · rename_i present
    obtain ⟨value,left,right,⟨r,rfl,kind,result⟩,done,rfl⟩ := normal
    dsimp only at done
    split at done
    · rename_i refused
      refine Or.inl ⟨attrs.listenPort.getD 0,r,?_,
        List.mem_append_left _ (List.mem_singleton_self _),kind,?_⟩
      · cases selected : attrs.listenPort with
        | none => simp only [selected,Option.isSome_none,Bool.false_eq_true] at present
        | some port => simp only [Option.getD_some]
      · intro zero
        have : value = 0 := result.symm.trans zero
        simp only [this,bne_self_eq_false,Bool.false_eq_true] at refused
    · obtain ⟨other,member,key⟩ := afterPort_normal_has_key attrs flags ret right done
      exact Or.inr ⟨other,List.mem_append_right _ member,key⟩
  · exact Or.inr (afterPort_normal_has_key attrs flags ret h normal)

theorem request_normal_cases (attrs : DeviceAttrs) (ret : Int) (h : List Receipt)
    (normal : (requestLanguage attrs).normal ret h) :
    h = [] ∨
    (∃ port r, attrs.listenPort = some port ∧ r ∈ h ∧
      r.kind = .port port ∧ r.result ≠ 0) ∨
    ∃ r ∈ h, r.kind = .keyStage := by
  rcases normal with empty | accepted
  · exact Or.inl empty
  · obtain ⟨_,first,rest,_,updated,rfl⟩ := accepted
    obtain ⟨_,clears,last,_,done,rfl⟩ := updated
    rcases afterFwmark_normal_cases attrs (attrs.flags.getD 0) ret last done with
      ⟨port,r,selected,member,kind,refused⟩ | ⟨r,member,kind⟩
    · exact Or.inr (Or.inl ⟨port,r,selected,
        List.mem_append_right _ (List.mem_append_right _ member),kind,refused⟩)
    · exact Or.inr (Or.inr ⟨r,List.mem_append_right _
        (List.mem_append_right _ member),kind⟩)
end Leanux.Proofs.WG.Config.RequestOrder
