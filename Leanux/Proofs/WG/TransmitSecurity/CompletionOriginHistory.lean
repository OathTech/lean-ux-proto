import Leanux.Proofs.WG.TransmitSecurity.PacketOriginWorker
import Leanux.Proofs.WG.TransmitSecurity.CompletionReceipts

/-! A completion entry identifies the actual head of its batch and a prior
native allocation of that head. Queue aliases do not create new origins. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000

def Certificate (bank : List Journal.Event) (items : List SkbId) : Prop :=
  ∃ id rest generation packet, items = id :: rest ∧
    PacketOrigins.Certificate bank generation id packet

theorem Certificate.mono (cert : Certificate bank items) (included : bank ⊆ later) :
    Certificate later items := by
  obtain ⟨id,rest,generation,packet,shape,origin⟩ := cert
  exact ⟨id,rest,generation,packet,shape,origin.mono included⟩

def entry? : Completion.Event → Option (List SkbId)
  | .disposition (.completion _ items) => some items
  | _ => none

def Good (bank : List Journal.Event) (h : List Completion.Event) : Prop :=
  ∀ items ∈ h.filterMap entry?, Certificate bank items

def Inv (bank : List Journal.Event) (h : List Completion.Event) (w : World) : Prop :=
  PacketOrigins.Inv bank w.wg ∧ Good bank h

/-- A nested focus retains a projection when its actual inner source does.
This does not assume that every event in the inner event type is quiet. -/
theorem focus_frame {S E F G α : Type} (encode : E → F) (decode : F → Option E)
    (other : F → Option G) (g : PrefixT E S α) (app : Appends g)
    (frame : HistoryFrame (fun e => other (encode e)) g) :
    HistoryFrame other (focusPrefix encode decode g) := by
  intro w h
  obtain ⟨suffix,extension⟩ := app w (h.filterMap decode)
  have empty : suffix.filterMap (fun e => other (encode e)) = [] := by
    have same := frame w (h.filterMap decode)
    rw [extension,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap (fun e => other (encode e)) with
    | nil => rfl
    | cons e es => simp only [List.length_append,found,List.length_cons] at lengths; omega
  rw [focusPrefix_suffix encode decode g w h _ suffix (Prod.ext rfl extension)]
  simp only [List.filterMap_append,List.filterMap_map,Function.comp_def,empty,List.append_nil]

theorem access_frame (a : MixedM α) : HistoryFrame entry? (Completion.access a) := by
  apply focus_frame _ _ _ _ (Appends.focus _ _ _)
  exact focusPrefix_other _ _ _ (fun _ => rfl) _

theorem quiet {g : PrefixM Completion.Event α} (app : Appends g)
    (frame : HistoryFrame entry? g) :
    PrefixPreserves (fun h _ => Good bank h) (Good bank) g := by
  intro w h before
  obtain ⟨suffix,extension⟩ := app w h
  have good : Good bank (runPrefix g w h).2 := by
    unfold Good
    rw [frame w h]
    exact before
  exact ⟨suffix,extension,good,by cases (runPrefix g w h).1 <;> trivial⟩

theorem access_good (a : MixedM α) :
    PrefixPreserves (fun h _ => Good bank h) (Good bank) (Completion.access a) :=
  quiet (Appends.focus _ _ _) (access_frame a)

theorem lift_good (a : Leanux.M α) :
    PrefixPreserves (fun h _ => Good bank h) (Good bank) (liftPrefix a) :=
  quiet (Appends.lift a) (HistoryFrame.lift _ a)

theorem socket_good (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) :
    PrefixPreserves (fun h _ => Good bank h) (Good bank)
      (Completion.socket pid id packet peer ipv4) := by
  apply quiet
  · unfold Completion.socket
    exact ((by cases ipv4 <;> exact Appends.focus _ _ _ : Appends _)).receiptObserved
  · unfold Completion.socket
    apply HistoryFrame.receiptObserved
    · cases ipv4 <;> exact access_frame _
    · intro _; rfl

theorem emit_good (pid : PeerId) (items : List SkbId) (cert : Certificate bank items) :
    PrefixPreserves (fun h (_ : World) => Good bank h) (Good bank)
      (emitPrefix (.disposition (.completion pid items))) := by
  intro w h before
  have good : Good bank (h ++ [.disposition (.completion pid items)]) := by
    intro found member
    simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,entry?,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with old | rfl
    · exact before found old
    · exact cert
  exact ⟨[.disposition (.completion pid items)],rfl,good,good⟩

macro "completion_origin_history_step" : tactic => `(tactic| first
  | (nonce_product_head Completion.access; exact access_good _)
  | (nonce_product_head liftPrefix; exact lift_good _)
  | (nonce_product_head captureObserved; exact (access_good _).captureObserved)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun h (_ : World) (hi : Good _ h) => hi) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ (fun h (_ : World) (hi : Good _ h) => hi))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem send_good (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket) :
    PrefixPreserves (fun h _ => Good bank h) (Good bank) (Completion.send pid id packet) := by
  unfold Completion.send
  repeat' first
    | (nonce_product_head Completion.socket; exact socket_good _ _ _ _ _)
    | completion_origin_history_step

theorem complete_good (pid : PeerId) (items : List SkbId) (cert : Certificate bank items) :
    PrefixPreserves (fun h _ => Good bank h) (Good bank) (Completion.complete pid items) := by
  unfold Completion.complete TxDisposition.andObs
  repeat' first
    | (nonce_product_head emitPrefix; exact emit_good _ _ cert)
    | (nonce_product_head Completion.send; exact send_good _ _ _)
    | completion_origin_history_step

end Leanux.Proofs.WG.TransmitSecurity.CompletionOrigin
