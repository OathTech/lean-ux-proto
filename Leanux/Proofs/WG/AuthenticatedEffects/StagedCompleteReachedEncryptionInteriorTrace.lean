import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorReadOnly

/-! A source-local primitive trace for the WG-read-only encryption routine.
It records each actual primitive entry before execution, so a failed primitive
retains its entry and no final World is asserted for the failure. This trace
is separate from the canonical journal and is not a history projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity
variable {initial : WGWorld}

structure PrimitiveCut where
  site : Site
  world : World

def primitiveObserved (site : Site) (action : Primitive α) : PrefixM PrimitiveCut α :=
  fun w => ExceptT.mk fun history => (action.native.run w,history ++ [⟨site,w⟩])

theorem primitive_run (site : Site) (action : Primitive α) (w : World) (history : List PrimitiveCut) :
    runPrefix (primitiveObserved site action) w history = (action.native.run w,history ++ [⟨site,w⟩]) := rfl

def PrimitiveSafe (initial : WGWorld) (history : List PrimitiveCut) : Prop :=
  ∀ cut ∈ history, cut.world.wg = initial

def PrimitiveInv (initial : WGWorld) (history : List PrimitiveCut) (w : World) : Prop :=
  w.wg = initial ∧ PrimitiveSafe initial history

theorem primitive_safe (site : Site) (action : Primitive α) :
    PrefixPreserves (PrimitiveInv initial) (PrimitiveSafe initial) (primitiveObserved site action) := by
  intro w history before
  have safe : PrimitiveSafe initial (history ++ [⟨site,w⟩]) := by
    intro cut member
    rcases List.mem_append.mp member with old | fresh
    · exact before.2 cut old
    · cases List.mem_singleton.mp fresh; exact before.1
  refine ⟨[⟨site,w⟩],rfl,safe,?_⟩
  rw [primitive_run]
  dsimp only
  cases performed : action.native.run w with
  | error reason => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    exact ⟨((ProjectedAction.iff_run _ _ _).mp action.frame w value v performed).trans before.1,safe⟩

def preparationTrace (packet : DataPacket) : PrefixM PrimitiveCut (Option Encryption.Prepared) :=
  prepareWith primitiveObserved packet

def finishTrace (slot : KeypairId) (packet : DataPacket) (prepared : Option Encryption.Prepared) :
    PrefixM PrimitiveCut (Option (List UInt8)) := finishWith primitiveObserved slot packet prepared

theorem preparation_safe (packet : DataPacket) :
    PrefixPreserves (PrimitiveInv initial) (PrimitiveSafe initial) (preparationTrace packet) := by
  unfold preparationTrace prepareWith
  repeat' first
    | (nonce_product_head primitiveObserved; exact primitive_safe _ _)
    | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ before => before.2) _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem finish_safe (slot : KeypairId) (packet : DataPacket) (prepared : Option Encryption.Prepared) :
    PrefixPreserves (PrimitiveInv initial) (PrimitiveSafe initial) (finishTrace slot packet prepared) := by
  unfold finishTrace finishWith
  cases prepared with
  | none => exact PrefixPreserves.pure (fun _ _ before => before.2) _
  | some value =>
    repeat' first
      | (nonce_product_head primitiveObserved; exact primitive_safe _ _)
      | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ before => before.2) _)
      | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
      | (nonce_product_head ite; apply PrefixPreserves.ite)
      | maintenance_intro
      | dsimp (config := {failIfUnchanged := true}) only
      | split

theorem preparation_erases (packet : DataPacket) :
    ErasesPrefix (preparationTrace packet) (Encryption.prepare Env.checksumHelp packet) := by
  rw [← prepare_native]
  unfold preparationTrace prepareWith
  repeat' first
    | (maintenance_head primitiveObserved; exact fun _ _ => rfl)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | (apply erasesPrefix_ite)
    | split

theorem finish_erases (slot : KeypairId) (packet : DataPacket) (prepared : Option Encryption.Prepared) :
    ErasesPrefix (finishTrace slot packet prepared) (Encryption.finish slot packet prepared) := by
  rw [← finish_native]
  unfold finishTrace finishWith
  cases prepared with
  | none => exact erasesPrefix_pure _
  | some value =>
    repeat' first
      | (maintenance_head primitiveObserved; exact fun _ _ => rfl)
      | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
      | (maintenance_head Bind.bind; apply erasesPrefix_bind)
      | maintenance_intro
      | dsimp (config := {failIfUnchanged := true}) only
      | (apply erasesPrefix_ite)
      | split

def encryptionTrace (slot : KeypairId) (packet : DataPacket) : PrefixM PrimitiveCut (Option (List UInt8)) :=
  preparationTrace packet >>= finishTrace slot packet

/-- All source-local primitive entries, including the final failed entry,
have the original WG projection. The complete native result or Stop is exact. -/
theorem encryption_interiors (slot : KeypairId) (packet : DataPacket) (w : World) :
    (runPrefix (encryptionTrace slot packet) w []).1 = (encryptPacket Env.checksumHelp slot packet).run w ∧
      PrimitiveSafe w.wg (runPrefix (encryptionTrace slot packet) w []).2 := by
  constructor
  · rw [Encryption.factor]
    exact erasesPrefix_bind (preparation_erases packet) (finish_erases slot packet) w []
  · have keeps := PrefixPreserves.bind (preparation_safe (initial := w.wg) packet)
      (finish_safe slot packet)
    obtain ⟨suffix,extended,safe,returned⟩ := keeps w [] ⟨rfl,by intro _ member; cases member⟩
    exact safe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
