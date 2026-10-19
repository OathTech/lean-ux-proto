import Leanux.Proofs.WG.TransmitSecurity.CompletionOriginHistory
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHistory

/-! Allocation and AEAD events in the same journal. An encryption certificate
names an allocation in the strict preceding prefix, rather than merely an
allocation somewhere in a separate observer's output. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
variable {id : SkbId}

def watched? : Journal.Event → Option Unit
  | .encrypted _ => some ()
  | .disposition (.completion _ _) => some ()
  | _ => none

def Checked (pre : List Journal.Event) : Journal.Event → Prop
  | .encrypted r => r.Valid ∧ ReadOrigin pre r.id r.read
  | .disposition (.completion _ items) => CompletionOrigin.Certificate pre items
  | _ => True

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked pre event

def JournalInv (h : List Journal.Event) (w : WGWorld) : Prop := Inv h w ∧ Safe h

theorem ReadOrigin.mono (origin : ReadOrigin h id r) (included : h ⊆ later) : ReadOrigin later id r := by
  obtain ⟨generation,epoch,certificate⟩ := origin
  exact ⟨generation,epoch,certificate.mono included⟩

theorem Safe.append (old : Safe h)
    (new : ∀ pre event post, s = pre ++ event :: post → Checked (h ++ pre) event) : Safe (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s old new

theorem checked_quiet (quiet : watched? event = none) : Checked pre event := by
  cases event <;> try exact True.intro
  case encrypted => cases quiet
  case disposition value =>
    cases value <;> first | exact True.intro | cases quiet

theorem Safe.quiet (old : Safe h) (quiet : watched? event = none) : Safe (h ++ [event]) := by
  apply old.append
  intro pre e post position
  have member : e ∈ [event] := by rw [position]; simp
  have same := List.mem_singleton.mp member
  subst e
  exact checked_quiet quiet

theorem Safe.worker (old : Safe h) : Good h (h.filterMap Journal.encryption?) := by
  intro r member
  obtain ⟨event,inside,encoded⟩ := List.mem_filterMap.mp member
  cases event <;> simp only [Journal.encryption?,Option.some.injEq,reduceCtorEq] at encoded
  rename_i value
  subst value
  obtain ⟨pre,post,position⟩ := List.mem_iff_append.mp inside
  obtain ⟨valid,origin⟩ := old pre (.encrypted r) post position
  refine ⟨valid,origin.mono ?_⟩
  intro e present
  rw [position]
  exact List.mem_append_left _ present

theorem Safe.encrypted (old : Safe h) (fresh : Good h suffix) : Safe (h ++ suffix.map Journal.Event.encrypted) := by
  apply old.append
  intro pre event post position
  have member : event ∈ suffix.map Journal.Event.encrypted := by rw [position]; simp
  obtain ⟨r,inside,rfl⟩ := List.mem_map.mp member
  obtain ⟨valid,origin⟩ := fresh r inside
  exact ⟨valid,origin.mono (fun _ present => List.mem_append_left _ present)⟩

theorem initial_journal (net bare : Bool) : JournalInv [] (Runner.initialWG net bare) :=
  ⟨initial net bare,by intro pre event post position; cases pre <;> cases position⟩

theorem allocate (packets : List DataPacket) :
    StatePrefixPreserves (fun h w _ => JournalInv h w) Safe (Journal.allocate packets) := by
  intro w a h hi
  unfold Journal.allocate
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb))
    (Journal.Event.allocated packets) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((packets.mapM newTxSkb).run w).run a with
  | error stop => exact ⟨[],by simp,hi.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨item,v⟩,b⟩ := out
    let r : WGRunWitness (List SkbId) := ⟨item,w,v,a,b⟩
    have safe := hi.2.quiet (event := .allocated packets r) rfl
    exact ⟨[.allocated packets r],rfl,safe,allocated packets r run hi.1,safe⟩

theorem encrypt_focus (item : Option (List SkbId)) :
    PrefixPreserves (fun h w => JournalInv h w.wg) Safe
      (focusPrefix Journal.Event.encrypted Journal.encryption? (WorkerEncryption.tail item)) := by
  intro w h hi
  obtain ⟨suffix,eq,good,post⟩ := tail_safe (bank := h) item w (h.filterMap Journal.encryption?) ⟨hi.1,hi.2.worker⟩
  have out := focusPrefix_suffix Journal.Event.encrypted Journal.encryption?
    (WorkerEncryption.tail item) w h _ suffix (Prod.ext rfl eq)
  have fresh : Good h suffix := by
    intro r member
    apply good r
    rw [eq]
    exact List.mem_append_right _ member
  have safe := hi.2.encrypted fresh
  rw [out]
  refine ⟨suffix.map Journal.Event.encrypted,rfl,safe,?_⟩
  cases result : (runPrefix (WorkerEncryption.tail item) w (h.filterMap Journal.encryption?)).1 with
  | error stop => trivial
  | ok value =>
    simp only [result] at post
    exact ⟨post.1.mono (fun _ member => List.mem_append_left _ member),safe⟩

private theorem emit_return (item : Option (List SkbId)) (r : RunWitness Bool) :
    PrefixPreserves (fun h (w : World) => JournalInv h w.wg) Safe (emitPrefix (.encryptionReturn item r)) := by
  intro w h hi
  have safe := hi.2.quiet (event := .encryptionReturn item r) rfl
  exact ⟨[.encryptionReturn item r],rfl,safe,
    hi.1.mono (fun _ member => List.mem_append_left _ member),safe⟩

theorem encrypt (item : Option (List SkbId)) :
    PrefixPreserves (fun h w => JournalInv h w.wg) Safe (Journal.encrypt item) := by
  unfold Journal.encrypt receiptObserved
  have inner : PrefixEnsures (fun h (w : World) => JournalInv h w.wg) Safe
      (focusPrefix Journal.Event.encrypted Journal.encryption? (WorkerEncryption.tail item))
      (fun _ h w => JournalInv h w.wg) := encrypt_focus item
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (PrefixEnsures.captureObserved inner)
  intro r w h hi
  rw [← hi.1]
  exact PrefixPreserves.bind (emit_return item r)
    (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) r.value) r.after h hi.2.1

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
