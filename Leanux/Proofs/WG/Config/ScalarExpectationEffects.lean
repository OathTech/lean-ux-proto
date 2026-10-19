import Leanux.Proofs.WG.Config.ScalarExpectationModel

/-! Exact source-effect factoring and pure deletion-aware fold transport.
The source connection must separately supply each actual command action and Step;
there is no whole-request or getter execution claim in these lemmas. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG

theorem sourceResult_exact (p : Peer) (attrs : PeerAttrs) (ret : Int) :
    sourceResult p attrs ret=
      fromFull (ScalarTail.tailCell attrs ret
        (ScalarTail.prefixCell p attrs.presharedKey attrs.endpoint)) := by
  cases psk:attrs.presharedKey <;> cases endpoint:attrs.endpoint with
  | none =>
    by_cases negative:ret<0 <;>
      simp [sourceResult,sourcePatch,applyPatch,endpointPatch,psk,endpoint,
        cell,fromFull,ScalarTail.tailCell,ScalarTail.prefixCell,ScalarFinish.finishCell,
        ScalarFinish.intervalCell,PeerScalarRetention.cell,ScalarPrefix.effectPeer,
        ScalarPrefix.keyedPeer,negative]
  | some a =>
    cases decoded:endpointAttribute a with
    | none =>
      by_cases negative:ret<0 <;>
        simp [sourceResult,sourcePatch,applyPatch,endpointPatch,psk,endpoint,decoded,
          cell,fromFull,ScalarTail.tailCell,ScalarTail.prefixCell,ScalarFinish.finishCell,
          ScalarFinish.intervalCell,PeerScalarRetention.cell,ScalarPrefix.effectPeer,
          ScalarPrefix.keyedPeer,endpointAttributePeer,negative]
    | some e =>
      cases equal:endpointSame e p.endpoint <;> by_cases negative:ret<0 <;>
        simp [sourceResult,sourcePatch,applyPatch,endpointPatch,psk,endpoint,decoded,equal,
          cell,fromFull,ScalarTail.tailCell,ScalarTail.prefixCell,ScalarFinish.finishCell,
          ScalarFinish.intervalCell,PeerScalarRetention.cell,ScalarPrefix.effectPeer,
          ScalarPrefix.keyedPeer,endpointAttributePeer,endpointStoredPeer,negative]

theorem sourceResult_stamp (p : Peer) (attrs : PeerAttrs) (ret : Int) :
    (sourceResult p attrs ret).1=p.internalId := rfl

theorem sourceResult_interval_negative (p : Peer) (attrs : PeerAttrs) (ret : Int)
    (negative : ret<0) : (sourceResult p attrs ret).2.2.1=p.persistentKeepaliveInterval := by
  simp [sourceResult,applyPatch,sourcePatch,cell,negative]

theorem sourceResult_interval_nonnegative (p : Peer) (attrs : PeerAttrs) (ret : Int)
    (nonnegative : ¬ret<0) :
    (sourceResult p attrs ret).2.2.1=attrs.keepalive.getD p.persistentKeepaliveInterval := by
  simp [sourceResult,applyPatch,sourcePatch,cell,nonnegative]

theorem sourceResult_of_fullCell (p q : Peer) (attrs : PeerAttrs) (ret : Int)
    (same : PeerScalarRetention.cell p=PeerScalarRetention.cell q) :
    sourceResult p attrs ret=sourceResult q attrs ret := by
  obtain ⟨stamp,psk,interval,endpoint⟩ :
      p.internalId=q.internalId ∧ p.presharedKey=q.presharedKey ∧
      p.persistentKeepaliveInterval=q.persistentKeepaliveInterval ∧ p.endpoint=q.endpoint := by
    simpa only [PeerScalarRetention.cell,Prod.mk.injEq] using same
  simp only [sourceResult,applyPatch,sourcePatch,endpointPatch,cell,stamp,psk,interval,endpoint]

theorem birthResult_exact (stamp : Nat) (attrs : PeerAttrs) (ret : Int) :
    birthResult stamp attrs ret=
      fromFull (ScalarTail.tailCell attrs ret
        (ScalarTail.prefixCell (birthPeer stamp attrs) attrs.presharedKey attrs.endpoint)) :=
  sourceResult_exact _ attrs ret

theorem birthResult_stamp (stamp : Nat) (attrs : PeerAttrs) (ret : Int) :
    (birthResult stamp attrs ret).1=stamp := rfl

theorem Agrees.refl (m : Map) : Agrees m m := fun _ _ h=>h

theorem Agrees.trans {before middle after : Map}
    (first : Agrees before middle) (last : Agrees middle after) : Agrees before after :=
  fun pid c h=>first pid c (last pid c h)

theorem step_advance {action : Action} {before after expected : Map}
    (step : Step action before after) (agree : Agrees expected before) :
    Agrees (advance expected action) after := by
  cases action with
  | quiet=>exact agree.trans step
  | update pid p attrs ret=>
    obtain ⟨old,selected,other⟩:=step
    have known:=agree pid (cell p) old
    intro q c present
    by_cases same:q=pid
    · subst q
      have eq : c=sourceResult p attrs ret := Option.some.inj (present.symm.trans selected)
      subst c
      simp only [advance,write,ite_true,known,Option.bind_some,cell,sourceResult,applyPatch,
        sourcePatch,Option.getD,ite_true]
    · simpa only [advance,write,same,ite_false] using agree q c (other q c same present)
  | birth pid stamp attrs ret=>
    obtain ⟨selected,other⟩:=step
    intro q c present
    by_cases same:q=pid
    · subst q
      have eq : c=birthResult stamp attrs ret := Option.some.inj (present.symm.trans selected)
      subst c
      simp only [advance,write,ite_true]
    · simpa only [advance,write,same,ite_false] using agree q c (other q c same present)

theorem Steps.advance {initial final expected : Map} {actions : List Action}
    (steps : Steps initial actions final) (agree : Agrees expected initial) :
    Agrees (fold expected actions) final := by
  induction steps generalizing expected with
  | nil m=>exact agree
  | cons step tail ih=>
    exact ih (step_advance step agree)

theorem Steps.fold {initial final : Map} {actions : List Action}
    (steps : Steps initial actions final) : Agrees (fold initial actions) final :=
  steps.advance (Agrees.refl initial)

end Leanux.Proofs.WG.Config.GetterScalar.Expectation
