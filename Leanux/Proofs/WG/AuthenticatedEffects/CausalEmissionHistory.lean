import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.Logged.PrefixState
import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocketCut

/-! Egress coverage is distinct from receipt validity and authorization.
This carrier identifies the native sent list with an exact ordered suffix of
all journaled append receipts. It therefore preserves transmission occurrences,
including identical datagrams; value membership would be insufficient. Local
contracts below are not an initialized whole-driver theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def added : Event → List SentDatagram
  | .old (.socket receipt) => receipt.socket.after.wg.sent.drop receipt.socket.before.wg.sent.length
  | .protocolSocket receipt => receipt.run.after.sent.drop receipt.run.before.sent.length
  | .cookieSocket receipt => [receipt.datagram.datagram]
  | _ => []

def emitted (history : List Event) : List SentDatagram := history.flatMap added

def Inv (history : List Event) (w : WGWorld) : Prop :=
  ∃ earlier, emitted history = earlier ++ w.sent

theorem emitted_append (history suffix : List Event) :
    emitted (history ++ suffix) = emitted history ++ emitted suffix := List.flatMap_append

theorem Inv.quiet (hi : Inv history w) (suffix : List Event) (quiet : emitted suffix = []) :
    Inv (history ++ suffix) w := by
  simpa only [Inv,emitted_append,quiet,List.append_nil] using hi

theorem Inv.sent_suffix (hi : Inv history w) (suffix : ∃ removed, w.sent = removed ++ v.sent) :
    Inv history v := by
  obtain ⟨earlier,historyEq⟩ := hi
  obtain ⟨removed,sentEq⟩ := suffix
  exact ⟨earlier ++ removed,by rw [historyEq,sentEq,List.append_assoc]⟩

theorem Inv.sent_equal (hi : Inv history w) (same : v.sent = w.sent) : Inv history v :=
  ⟨hi.choose,by rw [same]; exact hi.choose_spec⟩

theorem Inv.empty (empty : w.sent = []) : Inv history w :=
  ⟨emitted history,by rw [empty,List.append_nil]⟩

/-- Cover the exact difference of one actual append-only native call. -/
theorem Inv.receipt (hi : Inv history w) (event : Event)
    (grows : ∃ suffix, v.sent = w.sent ++ suffix)
    (covers : added event = v.sent.drop w.sent.length) : Inv (history ++ [event]) v := by
  obtain ⟨suffix,grows⟩ := grows
  obtain ⟨earlier,historyEq⟩ := hi
  refine ⟨earlier,?_⟩
  rw [emitted_append]
  change emitted history ++ (added event ++ []) = earlier ++ v.sent
  rw [List.append_nil,covers,grows,List.drop_left,historyEq,List.append_assoc]

abbrev StateSafe (body : WGPrefix Event α) :=
  StatePrefixPreserves (fun h w _ => Inv h w) (fun _ => True) body
abbrev ProductSafe (body : PrefixM Event α) :=
  PrefixPreserves (fun h w => Inv h w.wg) (fun _ => True) body

theorem state_pure (value : α) : StateSafe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ _ => True.intro) (fun _ _ _ hi => hi)

theorem state_native (action : WG.M α) (frame : SameView WGWorld.sent action) :
    StateSafe (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
    (fun _ w a value v b hi run => hi.sent_equal
      ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b run))

theorem state_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (preserves : StateSafe body) (tail : ∀ value, StateSafe (next value)) : StateSafe (body >>= next) :=
  StatePrefixEnsures.bind preserves tail

theorem state_ite (p : Prop) [Decidable p] {left right : WGPrefix Event α}
    (hl : p → StateSafe left) (hr : ¬p → StateSafe right) : StateSafe (if p then left else right) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hl hp
  · exact hr hp

theorem state_emit (event : Event) (quiet : added event = []) : StateSafe (emitStatePrefix event) :=
  StatePrefixEnsures.emit _ (fun _ _ _ _ => True.intro)
    (fun _ _ _ hi => hi.quiet [event] (by simp only [emitted,List.flatMap_cons,List.flatMap_nil,quiet,List.nil_append]))

theorem protocol_socket (cause : Context) (args : ProtocolSocket.Args) :
    StateSafe (ProtocolSocket.socket Event.protocolSocket cause args) := by
  intro w a h hi
  have observed := runWGPrefix_receiptWGObserved (liftWGPrefix args.action)
    (fun run => Event.protocolSocket ⟨cause,args,run⟩) w a h
  rw [runWGPrefix_lift] at observed
  simp only [runWGPrefix,runStatePrefix] at observed
  unfold ProtocolSocket.socket
  rw [observed]
  cases run : (args.action.run w).run a with
  | error stop => exact ⟨[],by simp,True.intro,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let receipt : ProtocolSocket.Receipt Context := ⟨cause,args,⟨value,w,v,a,b⟩⟩
    have emission := ProtocolSocket.Receipt.Valid.emission (receipt := receipt) run
    have grows : ∃ suffix, v.sent = w.sent ++ suffix := ⟨emission.choose,emission.choose_spec.1⟩
    exact ⟨[.protocolSocket receipt],rfl,True.intro,hi.receipt (.protocolSocket receipt) grows rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
