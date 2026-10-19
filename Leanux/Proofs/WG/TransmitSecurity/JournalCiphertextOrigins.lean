import Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertextStep
import Leanux.Proofs.WG.TransmitSecurity.JournalSocketHistory

/-! Socket payload certificates name encryption in the strict preceding
shared-journal prefix. Actual encryption and completion update the same carrier. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
variable {id : SkbId} {read : RunWitness DataPacket}

def receipts (h : List Journal.Event) := h.filterMap Journal.encryption?

def Checked (pre : List Journal.Event) : Journal.Event → Prop
  | .socket r => CompletionCiphertext.ReadOrigin (receipts pre) r.id r.packet
  | _ => True

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked pre event

def JournalInv (h : List Journal.Event) (w : WGWorld) : Prop := Inv (receipts h) w ∧ Safe h

theorem receipts_mono (included : h ⊆ later) : receipts h ⊆ receipts later := by
  intro r member
  obtain ⟨e,present,decoded⟩ := List.mem_filterMap.mp member
  exact List.mem_filterMap.mpr ⟨e,included present,decoded⟩

theorem read_mono (origin : CompletionCiphertext.ReadOrigin bank id read)
    (included : bank ⊆ later) : CompletionCiphertext.ReadOrigin later id read :=
  fun generation atEpoch nonempty => (origin generation atEpoch nonempty).mono included

theorem Safe.append (old : Safe h)
    (new : ∀ pre event post, s = pre ++ event :: post → Checked (h ++ pre) event) : Safe (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s old new

theorem Safe.quiet_suffix (old : Safe h) (quiet : suffix.filterMap Journal.SocketHistory.socket? = []) :
    Safe (h ++ suffix) := by
  apply old.append
  intro pre e post position
  have member : e ∈ suffix := by rw [position]; simp
  cases e <;> simp only [Checked]
  rename_i r
  have found : r ∈ suffix.filterMap Journal.SocketHistory.socket? :=
    List.mem_filterMap.mpr ⟨.socket r,member,rfl⟩
  rw [quiet] at found
  cases found

theorem Safe.quiet (old : Safe h) (quiet : Journal.SocketHistory.socket? event = none) : Safe (h ++ [event]) :=
  old.quiet_suffix (by simp only [List.filterMap_cons,List.filterMap_nil,quiet])

theorem Safe.completion (old : Safe h) :
    CompletionCiphertext.Good (receipts h) (h.filterMap Journal.completion?) := by
  intro r member
  have maps : (fun x => (Journal.completion? x).bind Completion.socket?) = Journal.SocketHistory.socket? := by
    funext e
    cases e <;> rfl
  rw [List.filterMap_filterMap,maps] at member
  obtain ⟨e,inside,decoded⟩ := List.mem_filterMap.mp member
  cases e <;> simp only [Journal.SocketHistory.socket?,Option.some.injEq,reduceCtorEq] at decoded
  rename_i value
  subst value
  obtain ⟨pre,post,position⟩ := List.mem_iff_append.mp inside
  apply read_mono (old pre (.socket r) post position)
  apply receipts_mono
  intro e present
  rw [position]
  exact List.mem_append_left _ present

theorem Safe.completed (old : Safe h)
    (fresh : CompletionCiphertext.Good (receipts h) suffix) :
    Safe (h ++ suffix.map Journal.completionEvent) := by
  apply old.append
  intro pre event post position
  have member : event ∈ suffix.map Journal.completionEvent := by rw [position]; simp
  obtain ⟨e,inside,rfl⟩ := List.mem_map.mp member
  cases e with
  | disposition value => trivial
  | socket r =>
    apply read_mono (fresh r (List.mem_filterMap.mpr ⟨.socket r,inside,rfl⟩))
    exact receipts_mono (fun _ present => List.mem_append_left _ present)

theorem initial_journal (net bare : Bool) : JournalInv [] (Runner.initialWG net bare) :=
  ⟨initial net bare,by intro pre event post position; cases pre <;> cases position⟩

theorem allocate (packets : List DataPacket) (empty : ∀ p ∈ packets, p.bytes = []) :
    StatePrefixPreserves (fun h w _ => JournalInv h w) Safe (Journal.allocate packets) := by
  intro w a h before
  unfold Journal.allocate
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb))
    (Journal.Event.allocated packets) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((packets.mapM newTxSkb).run w).run a with
  | error stop => exact ⟨[],by simp,before.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨item,v⟩,b⟩ := out
    let r : WGRunWitness (List SkbId) := ⟨item,w,v,a,b⟩
    have safe := before.2.quiet (event := .allocated packets r) rfl
    have kept := allocated packets empty r run before.1
    refine ⟨[.allocated packets r],rfl,safe,?_,safe⟩
    exact kept.mono (receipts_mono (fun _ member => List.mem_append_left _ member))

theorem encrypt_focus (item : Option (List SkbId)) :
    PrefixPreserves (fun h w => JournalInv h w.wg) Safe
      (focusPrefix Journal.Event.encrypted Journal.encryption? (WorkerEncryption.tail item)) := by
  intro w h before
  obtain ⟨suffix,eq,_,post⟩ := tail item w (receipts h) before.1
  have out := focusPrefix_suffix Journal.Event.encrypted Journal.encryption?
    (WorkerEncryption.tail item) w h _ suffix (Prod.ext rfl eq)
  have safe := before.2.quiet_suffix (suffix := suffix.map Journal.Event.encrypted) (by
    simp [List.filterMap_map,Function.comp_def,Journal.SocketHistory.socket?])
  rw [out]
  refine ⟨suffix.map Journal.Event.encrypted,rfl,safe,?_⟩
  cases result : (runPrefix (WorkerEncryption.tail item) w (receipts h)).1 with
  | error stop => simp only [receipts] at result; simp only [result]
  | ok value =>
    simp only [receipts] at result post
    simp only [result] at post ⊢
    have history : receipts (h ++ suffix.map Journal.Event.encrypted) =
        (runPrefix (WorkerEncryption.tail item) w (receipts h)).2 := by
      rw [eq]
      simp only [receipts,List.filterMap_append,List.filterMap_map,Function.comp_def,
        Journal.encryption?,List.filterMap_some]
    exact ⟨by rw [history]; exact post,safe⟩

private theorem emit_return (item : Option (List SkbId)) (r : RunWitness Bool) :
    PrefixPreserves (fun h (w : World) => JournalInv h w.wg) Safe (emitPrefix (.encryptionReturn item r)) := by
  intro w h before
  have safe := before.2.quiet (event := .encryptionReturn item r) rfl
  exact ⟨[.encryptionReturn item r],rfl,safe,
    before.1.mono (receipts_mono (fun _ member => List.mem_append_left _ member)),safe⟩

theorem encrypt (item : Option (List SkbId)) :
    PrefixPreserves (fun h w => JournalInv h w.wg) Safe (Journal.encrypt item) := by
  unfold Journal.encrypt receiptObserved
  have inner : PrefixEnsures (fun h (w : World) => JournalInv h w.wg) Safe
      (focusPrefix Journal.Event.encrypted Journal.encryption? (WorkerEncryption.tail item))
      (fun _ h w => JournalInv h w.wg) := encrypt_focus item
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (PrefixEnsures.captureObserved inner)
  intro r w h before
  rw [← before.1]
  exact PrefixPreserves.bind (emit_return item r)
    (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) r.value) r.after h before.2.1

theorem completion (pid : PeerId) :
    PrefixPreserves (fun h w => JournalInv h w.wg) Safe (Journal.transmit pid) := by
  intro w h before
  obtain ⟨suffix,eq,good,post⟩ := CompletionCiphertext.step pid w
    (h.filterMap Journal.completion?) ⟨before.1,before.2.completion⟩
  have out := focusPrefix_suffix Journal.completionEvent Journal.completion?
    (Completion.step pid) w h _ suffix (Prod.ext rfl eq)
  have fresh : CompletionCiphertext.Good (receipts h) suffix := by
    intro r member
    apply good r
    rw [eq,List.filterMap_append]
    exact List.mem_append_right _ member
  have safe := before.2.completed fresh
  change runPrefix (Journal.transmit pid) w h = _ at out
  rw [out]
  refine ⟨suffix.map Journal.completionEvent,rfl,safe,?_⟩
  cases result : (runPrefix (Completion.step pid) w (h.filterMap Journal.completion?)).1 with
  | error stop => trivial
  | ok value =>
    simp only [result] at post
    exact ⟨post.1.mono (receipts_mono (fun _ member => List.mem_append_left _ member)),safe⟩

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
