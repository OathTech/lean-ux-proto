import Leanux.Proofs.WG.Noise.DriverTagDeferredAtomsSource

/-! Deferred sources retain the actual schedule callback. Every other leaf
and helper-bearing callback is concrete; the final scheduler instance supplies
this one remaining callback obligation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.DeferredCalls
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

def crypt (schedule : ProductObs Unit) : ProductObs Unit :=
  RxHistory.DeferredSource.cryptWith schedule

def send (schedule : ProductObs Unit) : ProductObs Unit :=
  Deferred.sendWith hooks schedule

def afterXmit (schedule : ProductObs Unit) : ProductObs Unit :=
  RxHistory.DeferredSource.afterXmitWith (fun {_} a => old a) (crypt schedule) (send schedule)

def timers (schedule : ProductObs Unit) (j : UInt64) : ProductObs Bool :=
  Deferred.timersWith (fun {_} a => old a) hooks (crypt schedule) j

def placeholder (schedule : ProductObs Unit) (j : UInt64) : ProductObs Unit :=
  Deferred.placeholderWith (fun {_} a => old a) hooks (crypt schedule) (send schedule) j

def idle (schedule : ProductObs Unit) : ProductObs Unit :=
  RxHistory.DeferredSource.idleWith (fun {_} a => old a) (timers schedule) (placeholder schedule)

def afterAdvance (schedule : ProductObs Unit) : ProductObs Unit :=
  RxHistory.DeferredSource.afterAdvanceWith (fun {_} a => old a)
    (timers schedule) (placeholder schedule)

def observed (schedule : ProductObs Unit) (call : EnvDeferredCall) : ProductObs call.Result :=
  Deferred.deferredWith (fun {_} a => old a) hooks (crypt schedule) (send schedule)
    (afterXmit schedule) (timers schedule) (placeholder schedule)
    (idle schedule) (afterAdvance schedule) call

theorem crypt_preserves (entry : TagMap) (schedule : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory schedule) :
    PrefixPreserves (StateInv entry) ValidHistory (crypt schedule) :=
  RxHistory.DeferredSource.crypt_preserves (safe entry) (state_product_store entry) schedule hs

theorem send_preserves (entry : TagMap) (schedule : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory schedule) :
    PrefixPreserves (StateInv entry) ValidHistory (send schedule) :=
  Deferred.send_preserves (safe entry) (state_product_store entry) hooks (hooks_preserve entry) schedule hs

theorem afterXmit_preserves (entry : TagMap) (schedule : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory schedule) :
    PrefixPreserves (StateInv entry) ValidHistory (afterXmit schedule) :=
  Deferred.afterXmit_preserves (safe entry) (state_product_store entry) _ (atoms entry)
    _ _ (crypt_preserves entry schedule hs) (send_preserves entry schedule hs)

theorem timers_preserves (entry : TagMap) (schedule : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory schedule) (j : UInt64) :
    PrefixPreserves (StateInv entry) ValidHistory (timers schedule j) :=
  Deferred.timers_preserves (safe entry) (state_product_store entry) _ (atoms entry)
    hooks (hooks_preserve entry) _ (crypt_preserves entry schedule hs) j

theorem placeholder_preserves (entry : TagMap) (schedule : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory schedule) (j : UInt64) :
    PrefixPreserves (StateInv entry) ValidHistory (placeholder schedule j) :=
  Deferred.placeholder_preserves (safe entry) (state_product_store entry) _ (atoms entry)
    hooks (hooks_preserve entry) _ _ (crypt_preserves entry schedule hs)
    (send_preserves entry schedule hs) j

theorem idle_preserves (entry : TagMap) (schedule : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory schedule) :
    PrefixPreserves (StateInv entry) ValidHistory (idle schedule) :=
  Deferred.idle_preserves (safe entry) (state_product_store entry) _ (atoms entry) _ _
    (timers_preserves entry schedule hs) (placeholder_preserves entry schedule hs)

theorem afterAdvance_preserves (entry : TagMap) (schedule : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory schedule) :
    PrefixPreserves (StateInv entry) ValidHistory (afterAdvance schedule) :=
  Deferred.afterAdvance_preserves (safe entry) (state_product_store entry) _ (atoms entry) _ _
    (timers_preserves entry schedule hs) (placeholder_preserves entry schedule hs)

theorem observed_preserves (entry : TagMap) (schedule : ProductObs Unit)
    (hs : PrefixPreserves (StateInv entry) ValidHistory schedule) (call : EnvDeferredCall) :
    PrefixPreserves (StateInv entry) ValidHistory (observed schedule call) :=
  Deferred.deferred_preserves _ (atoms entry) hooks (hooks_preserve entry) _ _ _ _ _ _ _
    (crypt_preserves entry schedule hs) (send_preserves entry schedule hs)
    (afterXmit_preserves entry schedule hs) (timers_preserves entry schedule hs)
    (placeholder_preserves entry schedule hs) (idle_preserves entry schedule hs)
    (afterAdvance_preserves entry schedule hs) call

theorem crypt_erases (schedule : ProductObs Unit) (hs : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (crypt schedule) Env.runCryptWorkers := Deferred.crypt_erases schedule hs

theorem send_erases (schedule : ProductObs Unit) (hs : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (send schedule) Env.runSendWorkers := Deferred.send_erases hooks hooks_erase schedule hs

theorem afterXmit_erases (schedule : ProductObs Unit) (hs : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (afterXmit schedule) Env.afterXmit :=
  Deferred.afterXmit_erases _ atoms_erases _ _ (crypt_erases schedule hs) (send_erases schedule hs)

theorem timers_erases (schedule : ProductObs Unit) (hs : ErasesPrefix schedule (Env.schedule none))
    (j : UInt64) : ErasesPrefix (timers schedule j) (Env.runTimers j) :=
  Deferred.timers_erases _ atoms_erases hooks hooks_erase _ (crypt_erases schedule hs) j

theorem placeholder_erases (schedule : ProductObs Unit) (hs : ErasesPrefix schedule (Env.schedule none))
    (j : UInt64) : ErasesPrefix (placeholder schedule j) (Env.runTimersPlaceholder j) :=
  Deferred.placeholder_erases _ atoms_erases hooks hooks_erase _ _ (crypt_erases schedule hs)
    (send_erases schedule hs) j

theorem idle_erases (schedule : ProductObs Unit) (hs : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (idle schedule) Env.idleTimers :=
  Deferred.idle_erases _ atoms_erases _ _ (timers_erases schedule hs) (placeholder_erases schedule hs)

theorem afterAdvance_erases (schedule : ProductObs Unit) (hs : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (afterAdvance schedule) Env.afterAdvance :=
  Deferred.afterAdvance_erases _ atoms_erases _ _ (timers_erases schedule hs) (placeholder_erases schedule hs)

theorem observed_erases (schedule : ProductObs Unit) (hs : ErasesPrefix schedule (Env.schedule none))
    (call : EnvDeferredCall) : ErasesPrefix (observed schedule call) call.original :=
  Deferred.deferred_erases _ atoms_erases hooks hooks_erase _ _ _ _ _ _ _
    (crypt_erases schedule hs) (send_erases schedule hs) (afterXmit_erases schedule hs)
    (timers_erases schedule hs) (placeholder_erases schedule hs) (idle_erases schedule hs)
    (afterAdvance_erases schedule hs) call

end Leanux.Proofs.WG.Noise.DriverTags.DeferredCalls

