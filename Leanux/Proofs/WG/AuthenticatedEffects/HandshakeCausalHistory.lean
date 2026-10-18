import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausalSource
import Leanux.Proofs.WG.AuthenticatedEffects.TransportChecks

/-! Positional causes for native handshake callback entries. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausal
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def roots (h : List Event) := h.filterMap admission
def RootSafe (h : List Event) := HandshakeAdmissionFacts.Safe (roots h)
def Available (h : List Event) (pid : PeerId) := HasAdmission (roots h) pid

def Checked (pre : List Event) : Event → Prop
  | .admission _ => True
  | .callback _ pid => Available pre pid

def CallsSafe (h : List Event) : Prop := ∀ pre e post, h = pre ++ e :: post → Checked pre e

def Safe (h : List Event) := RootSafe h ∧ CallsSafe h
abbrev Inv (h : List Event) (_ : WGWorld) (_ : Ambient) := Safe h
abbrev Preserves (g : WGPrefix Event α) := StatePrefixPreserves Inv Safe g

def calls : Event → Option Unit
  | .admission _ => none
  | .callback _ _ => some ()

theorem CallsSafe.append (hi : CallsSafe h)
    (hs : ∀ pre e post, s = pre ++ e :: post → Checked (h ++ pre) e) : CallsSafe (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s hi hs

theorem CallsSafe.quiet (hi : CallsSafe h) (hs : s.filterMap calls = []) : CallsSafe (h ++ s) := by
  apply hi.append
  intro pre e post position
  cases e with
  | admission r => trivial
  | callback kind pid =>
    have member : Event.callback kind pid ∈ s := by rw [position]; simp
    have found : () ∈ s.filterMap calls := List.mem_filterMap.mpr ⟨_,member,rfl⟩
    simp [hs] at found

theorem Available.append (hi : Available h pid) (s : List Event) : Available (h ++ s) pid := by
  obtain ⟨r,member,peer⟩ := hi
  exact ⟨r,by simp only [roots,List.filterMap_append,List.mem_append]; exact Or.inl member,peer⟩

theorem Safe.callback (hi : Safe h) (kind : Kind) (pid : PeerId) (cause : Available h pid) :
    Safe (h ++ [.callback kind pid]) := by
  constructor
  · simpa only [RootSafe,roots,List.filterMap_append,List.filterMap_cons,admission,List.filterMap_nil,
      List.append_nil] using hi.1
  · apply hi.2.append
    intro pre e post position
    cases pre with
    | nil => cases position; simpa only [List.append_nil,Checked] using cause
    | cons x xs =>
      have lengths := congrArg List.length position
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega

private theorem quiet_ensures (g : WGPrefix Event α)
    (contract : StatePrefixEnsures P RootSafe g Q) (frame : StateHistoryFrame calls g) :
    StatePrefixEnsures (fun h w a => P h w a ∧ CallsSafe h) Safe g
      (fun x h w a => Q x h w a ∧ CallsSafe h) := by
  intro w a h hi
  obtain ⟨s,hs,rootSafe,post⟩ := contract w a h hi.1
  have projection := frame w a h
  rw [hs,List.filterMap_append] at projection
  have empty : s.filterMap calls = [] := by simpa using projection
  have safe : CallsSafe (runPrefix (g.run w) a h).2 := hs ▸ hi.2.quiet empty
  refine ⟨s,hs,⟨rootSafe,safe⟩,?_⟩
  cases result : (runPrefix (g.run w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨value,ambient⟩
    exact ⟨by simpa only [result] using post,safe⟩

private theorem focus_frame (g : WGPrefix HandshakeAdmission α) :
    StateHistoryFrame calls (focusStatePrefix Event.admission admission g) := by
  intro w a h
  exact focusPrefix_other Event.admission admission calls (fun _ => rfl) (g.run w) a h

theorem initiation_post (mac : HandshakeMac) (valid : mac.Valid) :
    StatePrefixEnsures Inv Safe (initiation mac)
      (fun result h _ _ => Safe h ∧ ∀ pid, result = some pid → Available h pid) := by
  have base := (admitInitiation_post mac valid).focus Event.admission admission (fun _ => rfl)
  have combined := quiet_ensures (initiation mac) base (focus_frame _)
  apply combined.consequence
  · intro h w a hi; exact ⟨hi.1,hi.2⟩
  · intro result h w a hi; exact ⟨⟨hi.1.1,hi.2⟩,hi.1.2⟩

theorem response_post (mac : HandshakeMac) (valid : mac.Valid) :
    StatePrefixEnsures Inv Safe (response mac)
      (fun result h _ _ => Safe h ∧ ∀ pid, result = some pid → Available h pid) := by
  have base := (admitResponse_post mac valid).focus Event.admission admission (fun _ => rfl)
  have combined := quiet_ensures (response mac) base (focus_frame _)
  apply combined.consequence
  · intro h w a hi; exact ⟨hi.1,hi.2⟩
  · intro result h w a hi; exact ⟨⟨hi.1.1,hi.2⟩,hi.1.2⟩

def Ready (pid : PeerId) (h : List Event) (_ : WGWorld) (_ : Ambient) := Safe h ∧ Available h pid

theorem lift_ready (pid : PeerId) (a : WG.M α) :
    StatePrefixPreserves (Ready pid) Safe (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi => hi.1) (fun _ _ _ _ _ _ hi _ => hi)

theorem call_ready (kind : Kind) (pid : PeerId) (a : WG.M α) :
    StatePrefixPreserves (Ready pid) Safe (call kind pid a) := by
  unfold call
  refine StatePrefixEnsures.bind
    (StatePrefixEnsures.emit (P := Ready pid) (S := Safe) (Q := fun _ => Ready pid) (.callback kind pid) ?_ ?_) ?_
  · intro h w a hi
    exact hi.1.callback kind pid hi.2
  · intro h w a hi
    exact ⟨hi.1.callback kind pid hi.2,hi.2.append _⟩
  · intro doneUnit
    exact lift_ready pid a

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausal
