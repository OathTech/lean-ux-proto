import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointFramed

/-! Source-generated residuals include silent native writes before access
receipts, and the decrypt capture before its receipt. A stopped primitive
has an entry, never an invented returned world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

variable {E F α β : Type}

def emitMany (events : List E) (value : α) : WGPrefix E α :=
  fun w a=>ExceptT.mk fun h=>(.ok ((value,w),a),h++events)

def receiptFrom (w : WGWorld) (a : Ambient) (body : WGPrefix E α)
    (record : WGRunWitness α → E) : WGPrefix E α := do
  let witness←captureWGObserved body
  emitStatePrefix (record {witness with before:=w,ambientBefore:=a})
  return witness.value

theorem emitMany_run (events : List E) (value : α) :
    runWGPrefix (emitMany events value) w a h=(.ok ((value,w),a),h++events) := rfl

theorem receiptFrom_run (w : WGWorld) (a : Ambient) (body : WGPrefix E α)
    (record : WGRunWitness α → E) (u : WGWorld) (b : Ambient) (h : List E) :
    runWGPrefix (receiptFrom w a body record) u b h = match runWGPrefix body u b h with
    | (.error reason,last) => (.error reason,last)
    | (.ok ((value,v),c),last) =>
        (.ok ((value,v),c),last++[record ⟨value,w,v,a,c⟩]) := by
  unfold receiptFrom
  change runStatePrefix _ u b h = _
  rw [runStatePrefix_bind]
  have captured:=runWGPrefix_captureWGObserved body u b h
  change runStatePrefix _ u b h = _ at captured
  rw [captured]
  cases run : runWGPrefix body u b h with
  | mk out last => cases out with
      | error reason => rfl
      | ok out => obtain ⟨⟨value,v⟩,c⟩:=out; rfl

inductive Site where
  | entry | returned | nativeBeforeReceipt | beforeDecryptReceipt
  | left (site : Site) | right (site : Site)
  | focused (site : Site) | captured (site : Site)

inductive Point : {E α : Type} → {action : WGPrefix E α} → Shape action →
    WGWorld → Ambient → List E → Site → WGWorld → Ambient → List E → WGPrefix E α → Prop where
  | entry {E α : Type} {action : WGPrefix E α} (shape : Shape action) {w : WGWorld} {a : Ambient} {h : List E} : Point shape w a h .entry w a h action
  | returned {E α : Type} {action : WGPrefix E α} {value : α} (shape : Shape action)
      {w v : WGWorld} {a b : Ambient} {h last : List E}
      (performed : runWGPrefix action w a h=(.ok ((value,v),b),last)) :
      Point shape w a h .returned v b last (pure value)
  | native {E α : Type} {action : WGPrefix E α} {value : α} (token : Access action)
      {w v : WGWorld} {a b : Ambient} {h : List E}
      (performed : (token.native.run w).run a=.ok ((value,v),b)) :
      Point (.access token) w a h .nativeBeforeReceipt v b h (emitMany (token.events w value) value)
  | left {E α β : Type} {body : WGPrefix E α} {next : α → WGPrefix E β} {head : Shape body}
      (tail : ∀value,Shape (next value))
      {w v : WGWorld} {a b : Ambient} {h middle : List E} {site : Site} {remaining : WGPrefix E α}
      (point : Point head w a h site v b middle remaining) :
      Point (.bind head tail) w a h (.left site) v b middle (remaining >>= next)
  | right {E α β : Type} {body : WGPrefix E α} {next : α → WGPrefix E β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      {w u v : WGWorld} {a b c : Ambient} {h middle last : List E} {site : Site}
      {value : α} {remaining : WGPrefix E β}
      (leading : runWGPrefix body w a h=(.ok ((value,u),c),middle))
      (point : Point (tail value) u c middle site v b last remaining) :
      Point (.bind head tail) w a h (.right site) v b last remaining
  | focus {E F α : Type} (encode : E → F) (decode : F → Option E) (inverse : ∀event,decode (encode event)=some event)
      {body : WGPrefix E α} {shape : Shape body}
      {w v : WGWorld} {a b : Ambient} {h : List F} {middle : List E} {site : Site} {remaining : WGPrefix E α}
      (point : Point shape w a (h.filterMap decode) site v b middle remaining) :
      Point (.focus encode decode inverse shape) w a h (.focused site) v b
        (h++(middle.drop (h.filterMap decode).length).map encode)
        (focusStatePrefix encode decode remaining)
  | receipt {E α : Type} {body : WGPrefix E α} {shape : Shape body} (record : WGRunWitness α→E)
      {w v : WGWorld} {a b : Ambient} {h middle : List E} {site : Site} {remaining : WGPrefix E α}
      (point : Point shape w a h site v b middle remaining) :
      Point (.receipt shape record) w a h (.captured site) v b middle (receiptFrom w a remaining record)
  | receiptNative {E α : Type} {body : WGPrefix E α} (shape : Shape body) (record : WGRunWitness α→E)
      {w v : WGWorld} {a b : Ambient} {h middle : List E} {value : α}
      (performed : runWGPrefix body w a h=(.ok ((value,v),b),middle)) :
      Point (.receipt shape record) w a h .beforeDecryptReceipt v b middle
        (emitMany [record ⟨value,w,v,a,b⟩] value)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
