import Leanux.Proofs.WG.Config.GetterScalarModel
import Leanux.Proofs.WG.Config.ScalarTailModel

/-! Pure scalar expectations for future source-connected completed commands.
The normalized expectation omits local endpoint cache fields, but each update's
decision input retains its actual full before-peer. Quiet steps allow deletion;
birth steps reset the selected slot. This module asserts no original call rule. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG

/-- The endpoint field is a replacement only; absent or ignored attributes keep it. -/
structure Patch where
  psk : Option Key
  interval : Option Nat
  endpoint : Option Endpoint

def endpointPatch (before : Peer) (attrs : PeerAttrs) : Option Endpoint :=
  attrs.endpoint.bind fun a=>(endpointAttribute a).bind fun e=>
    if endpointSame e before.endpoint then none else some (TimerDiscipline.socketEndpoint e)

/-- The endpoint decision reads the actual full before-peer, including cached
source fields. It is not recomputed from the normalized expectation map. -/
def sourcePatch (before : Peer) (attrs : PeerAttrs) (ret : Int) : Patch :=
  ⟨attrs.presharedKey,if ret<0 then none else attrs.keepalive,endpointPatch before attrs⟩

def applyPatch (patch : Patch) (c : Cell) : Cell :=
  (c.1,patch.psk.getD c.2.1,patch.interval.getD c.2.2.1,
    match patch.endpoint with | none=>c.2.2.2 | some e=>some e)

def sourceResult (before : Peer) (attrs : PeerAttrs) (ret : Int) : Cell :=
  applyPatch (sourcePatch before attrs ret) (cell before)

/-- Scalar defaults of actual allocation; unrelated peer fields are immaterial. -/
def birthPeer (stamp : Nat) (attrs : PeerAttrs) : Peer :=
  {internalId:=stamp,remoteStatic:=attrs.publicKey.getD [],
    presharedKey:=attrs.presharedKey.getD (List.replicate 32 0),
    precomputedStaticStatic:=List.replicate 32 0}

def birthResult (stamp : Nat) (attrs : PeerAttrs) (ret : Int) : Cell :=
  sourceResult (birthPeer stamp attrs) attrs ret

inductive Action where
  | quiet
  | update (pid : PeerId) (before : Peer) (attrs : PeerAttrs) (ret : Int)
  | birth (pid : PeerId) (stamp : Nat) (attrs : PeerAttrs) (ret : Int)

def write (m : Map) (pid : PeerId) (value : Option Cell) : Map :=
  fun q=>if q=pid then value else m q

/-- A stamp mismatch makes the computed expectation absent; source-connected
steps will establish the matching entry cell, so this case is never assumed away. -/
def advance (m : Map) : Action→Map
  | .quiet=>m
  | .update pid before attrs ret=>
      write m pid ((m pid).bind fun old=>
        if old.1=before.internalId then some (applyPatch (sourcePatch before attrs ret) old) else none)
  | .birth pid stamp attrs ret=>write m pid (some (birthResult stamp attrs ret))

def fold (initial : Map) (actions : List Action) : Map :=
  actions.foldl advance initial

def Agrees (expected actual : Map) : Prop :=
  ∀pid c,actual pid=some c→expected pid=some c

/-- Pure per-command premises to be discharged from the original completed
call. No theorem in this module asserts that an arbitrary original call has them. -/
def Step (action : Action) (before after : Map) : Prop :=
  match action with
  | .quiet=>Agrees before after
  | .update pid p attrs ret=>
      before pid=some (cell p) ∧ after pid=some (sourceResult p attrs ret) ∧
        ∀q c,q≠pid→after q=some c→before q=some c
  | .birth pid stamp attrs ret=>
      after pid=some (birthResult stamp attrs ret) ∧
        ∀q c,q≠pid→after q=some c→before q=some c

inductive Steps : Map→List Action→Map→Prop
  | nil (m) : Steps m [] m
  | cons {before middle after action rest}
      (step : Step action before middle) (tail : Steps middle rest after) :
      Steps before (action::rest) after

end Leanux.Proofs.WG.Config.GetterScalar.Expectation
