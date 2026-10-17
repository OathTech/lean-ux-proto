import Leanux.Proofs.WG.Roaming.NapiPublicationModel
import Leanux.Proofs.WG.Roaming.PollEndpointSource
import Leanux.Env.Batch

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Env Noise

/-- Actual NAPI entry through section start; all skips and original failures remain. -/
def napiPublicationFront : Leanux.M (Option (List PeerId)) := do
  let d ← getDev
  let pending := d.peers.toList.filterMap fun (pid, p) => if p.napiScheduled then some pid else none
  if pending.isEmpty then return none
  if (← getAmbient).hidden.isSome && (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return none
  if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
  _ ← hidden (.sectionStart .netRx)
  modifyAmbient fun s => { s with netRxSection := s.netRxSections }
  return some pending

def napiPublicationTail (pending : Option (List PeerId)) : Leanux.M Unit := do
  match pending with
  | none => pure ()
  | some peers =>
    for pid in peers do
      discard <| WG.rxPoll pid WG.NAPI_POLL_WEIGHT fun pkts => pkts.forM deliverInner
    modifyAmbient fun s => { s with netRxSection := 0 }
    _ ← hidden (.sectionStop .netRx)

def napiIrqPublicationFront : Leanux.M (Option (List PeerId)) := do
  if (← getAmbient).hidden.isNone then return none
  if !(← getDev).peers.toList.any (·.2.napiScheduled) then return none
  if (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return none
  let here := (← getEnv).napiBeforePut.headD false
  modifyEnv fun e => { e with napiBeforePut := e.napiBeforePut.drop 1, napiAmbiguous := e.napiAmbiguous + 1 }
  if here then napiPublicationFront else pure none

theorem napiSoftirq_publication_source :
    napiSoftirq = (napiPublicationFront >>= napiPublicationTail) := by
  have bind_if {α β : Type} (p : Prop) [Decidable p]
      (yes no : Leanux.M α) (f : α → Leanux.M β) :
      ((if p then yes else no) >>= f) = if p then yes >>= f else no >>= f := by
    split <;> rfl
  have netRx : (Worker.netRx == Worker.netRx) = true := rfl
  simp only [napiSoftirq, napiPublicationFront, runWorker, bind_assoc, pure_bind,
    bind_if, napiPublicationTail, netRx, ite_true]

theorem napiIrqExit_publication_source :
    napiIrqExit = (napiIrqPublicationFront >>= napiPublicationTail) := by
  have bind_if {α β : Type} (p : Prop) [Decidable p]
      (yes no : Leanux.M α) (f : α → Leanux.M β) :
      ((if p then yes else no) >>= f) = if p then yes >>= f else no >>= f := by
    split <;> rfl
  simp only [napiIrqExit, napiIrqPublicationFront, bind_assoc, pure_bind,
    bind_if, napiPublicationTail, napiSoftirq_publication_source]

/-- Inspect only the first actual poll prefix; execute every original poll and
section finish on the same actual entry. Skips have no invented poll. -/
def observedNapiFirst (pending : Option (List PeerId)) : Leanux.M (Option NapiFirstCut) := do
  let cut ← match pending.bind List.head? with
    | none => pure none
    | some pid => do
      let entry ← Campaign2.Product.read
      let poll ← Campaign2.Product.inspect (pollInitialPrefix pid NAPI_POLL_WEIGHT)
      pure (some ⟨pid,entry,poll⟩)
  napiPublicationTail pending
  return cut

def observedNapiIrqFirst : Leanux.M (Option NapiFirstCut) := do
  let pending ← napiIrqPublicationFront
  observedNapiFirst pending

def observedNativeDecryptFirstPoll : Leanux.M (Bool × Option (PublicationCut × Option NapiFirstCut)) := do
  let found ← publicationPrefix napiSoftirq
  match found with
  | none => return (false,none)
  | some pub =>
    let cut ← observedNapiIrqFirst
    peerPut (some pub.owner)
    napiSoftirq
    return (true,some (pub,cut))

theorem observedNapiFirst_erase (pending : Option (List PeerId)) :
    (do let _ ← observedNapiFirst pending; pure ()) = napiPublicationTail pending := by
  have finish : (fun _ : Unit => (pure () : Leanux.M Unit)) = pure := by
    funext x; cases x; rfl
  funext w
  unfold observedNapiFirst
  cases selected : pending.bind List.head? <;>
    simp only [bind_assoc,pure_bind,finish,bind_pure] <;> rfl

theorem observedNapiIrqFirst_erase :
    (do let _ ← observedNapiIrqFirst; pure ()) = napiIrqExit := by
  rw [napiIrqExit_publication_source]
  simp only [observedNapiIrqFirst,bind_assoc,observedNapiFirst_erase]

theorem observedNativeDecryptFirstPoll_erase :
    (do let result ← observedNativeDecryptFirstPoll; pure result.1) =
      decryptStep napiSoftirq napiIrqExit := by
  rw [decryptStep_publication,← observedNapiIrqFirst_erase]
  simp only [observedNativeDecryptFirstPoll,bind_assoc]
  congr 1
  funext found
  cases found <;> simp only [publicationSuffix,bind_assoc,pure_bind]


end Leanux.Proofs.WG.Roaming
