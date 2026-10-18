import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationSource

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation
open Leanux Leanux.WG Leanux.Proofs.Logged

def Evidence (base h : List Receipt) : Prop :=
  h = base ∨ ∃ r, h = base ++ [r] ∧ r.Valid

def Completed (base h : List Receipt) : Prop :=
  ∃ r, h = base ++ [r] ∧ r.Valid

theorem Completed.evidence {base h : List Receipt} (hc : Completed base h) : Evidence base h :=
  Or.inr hc

theorem confirm_evidence (base : List Receipt) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StatePrefixEnsures (fun h _ _ => h = base) (Evidence base) (confirmObserved pid pkt ep)
      (fun confirmed h _ _ => ∃ r, h = base ++ [r] ∧ r.Valid ∧ r.peer = pid ∧
        r.packet = pkt ∧ r.endpoint = ep ∧ r.execution.value = confirmed) := by
  intro w a h hi
  subst h
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (receivedWithKeypair pid pkt.keypair))
    (fun run => (⟨pid, pkt, ep, run⟩ : Receipt)) w a base
  rw [runWGPrefix_lift] at equation
  change runStatePrefix (confirmObserved pid pkt ep) w a base = _ at equation
  unfold runStatePrefix at equation
  rw [equation]
  cases run : ((receivedWithKeypair pid pkt.keypair).run w).run a with
  | error stop => exact ⟨[], by simp, Or.inl rfl, trivial⟩
  | ok out =>
    rcases out with ⟨⟨confirmed, v⟩, b⟩
    exact ⟨_, rfl, Or.inr ⟨⟨pid, pkt, ep, ⟨confirmed, w, v, a, b⟩⟩, rfl, run⟩,
      ⟨⟨pid, pkt, ep, ⟨confirmed, w, v, a, b⟩⟩, rfl, run, rfl, rfl, rfl, rfl⟩⟩

theorem evidence (base : List Receipt) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StatePrefixEnsures (fun h _ _ => h = base) (Evidence base) (observed pid pkt ep)
      (fun _ h _ _ => Completed base h) := by
  have endpoint : StatePrefixPreserves (fun h _ _ => h = base) (Evidence base)
      (liftWGPrefix (setPeerEndpoint pid ep) : WGPrefix Receipt Unit) :=
    StatePrefixEnsures.lift _ (fun _ _ _ hi => Or.inl hi) (fun _ _ _ _ _ _ hi _ => hi)
  unfold observed
  apply StatePrefixEnsures.bind endpoint
  intro _
  apply StatePrefixEnsures.bind (confirm_evidence base pid pkt ep)
  intro confirmed
  apply StatePrefixEnsures.lift _
  · intro h w a hi
    obtain ⟨r, hh, valid, _⟩ := hi
    exact Or.inr ⟨r, hh, valid⟩
  · intro h w a result v b hi _
    obtain ⟨r, hh, valid, _⟩ := hi
    exact ⟨r, hh, valid⟩

def Valid (h : List Receipt) : Prop := ∀ r ∈ h, r.Valid

theorem evidence_valid {base h : List Receipt} (hi : Valid base) (he : Evidence base h) : Valid h := by
  rcases he with same | ⟨r, same, valid⟩
  · simpa only [same] using hi
  · rw [same]
    intro current member
    rcases List.mem_append.mp member with old | last
    · exact hi current old
    · have equal := List.mem_singleton.mp last
      simpa only [equal] using valid

theorem valid_preserves (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (observed pid pkt ep) := by
  intro w a h hi
  obtain ⟨suffix, append, safe, _⟩ := evidence h pid pkt ep w a h rfl
  have valid := evidence_valid hi safe
  refine ⟨suffix, append, valid, ?_⟩
  cases result : (runPrefix ((observed pid pkt ep).run w) a h).1 with
  | error stop => trivial
  | ok out => exact valid

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation
