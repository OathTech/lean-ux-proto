import Leanux.Proofs.Logged.ProjectsUnder
import Leanux.Proofs.WG.Lifetimes.AllocationInvariant

/-! Failure-retaining committed lifetime observations and saved consistency-filter
entries. Each saved entry refers to its own World and lifetime history, even after
later committed mutations. Speculative access histories remain separate. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

structure ProbeEntry where
  world : World
  history : List LifetimeEvent

inductive AuditEvent where
  | lifetime : LifetimeEvent → AuditEvent
  | probe : ProbeEntry → AuditEvent

def AuditEvent.lifetime? : AuditEvent → Option LifetimeEvent
  | .lifetime e => some e
  | .probe _ => none

def AuditEvent.probe? : AuditEvent → Option ProbeEntry
  | .lifetime _ => none
  | .probe p => some p

def lifetimeHistory (h : List AuditEvent) : List LifetimeEvent := h.filterMap AuditEvent.lifetime?
def probeEntries (h : List AuditEvent) : List ProbeEntry := h.filterMap AuditEvent.probe?

abbrev AuditM := PrefixM AuditEvent

def AllProbeValid (h : List AuditEvent) : Prop :=
  ∀ p ∈ probeEntries h, AllocationInv p.history p.world

def AuditInv (h : List AuditEvent) (w : World) : Prop :=
  AllocationInv (lifetimeHistory h) w ∧ AllProbeValid h

def AuditSafe (h : List AuditEvent) : Prop :=
  LifetimeEvent.Safe (lifetimeHistory h) ∧ AllProbeValid h

theorem AuditInv.safe (hi : AuditInv h w) : AuditSafe h := ⟨hi.1.safe, hi.2⟩

theorem AuditInv.kernel (hi : AuditInv h w) (he : v.k = w.k) : AuditInv h v :=
  ⟨hi.1.kernel he, hi.2⟩

theorem audit_initial (hi : AllocationInv [] w) : AuditInv [] w :=
  ⟨hi, by simp [AllProbeValid, probeEntries]⟩

def auditFocus (g : MixedM α) : AuditM α :=
  focusPrefix AuditEvent.lifetime AuditEvent.lifetime? g

theorem auditFocus_erases (he : ErasesPrefix g a) : ErasesPrefix (auditFocus g) a :=
  focusPrefix_erases _ _ he

/-- Focusing a lower observer cannot add, delete or reorder saved probe entries,
even when it stops and even without a lower append premise. -/
theorem auditFocus_probes (g : MixedM α) (w : World) (h : List AuditEvent) :
    probeEntries (runPrefix (auditFocus g) w h).2 = probeEntries h :=
  focusPrefix_other _ _ _ (fun _ => rfl) g w h

/-- Arbitrary result-dependent lower contracts carry cached identities such as
SavedPeers, together with every previously saved probe's validity. -/
theorem auditFocus_ensures (hg : PrefixEnsures P S g Q) :
    PrefixEnsures (fun h w => P (lifetimeHistory h) w ∧ AllProbeValid h)
      (fun h => S (lifetimeHistory h) ∧ AllProbeValid h) (auditFocus g)
      (fun x h w => Q x (lifetimeHistory h) w ∧ AllProbeValid h) := by
  intro w h hi
  obtain ⟨suffix, hs, hsafe, hq⟩ :=
    PrefixEnsures.focus AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl) hg w h hi.1
  have hp : AllProbeValid (runPrefix (auditFocus g) w h).2 := by
    unfold AllProbeValid
    rw [auditFocus_probes]
    exact hi.2
  refine ⟨suffix, hs, ⟨hsafe, hp⟩, ?_⟩
  change (match (runPrefix (auditFocus g) w h).1 with
    | .error _ => True
    | .ok (x, v) => Q x (lifetimeHistory (runPrefix (auditFocus g) w h).2) v) at hq
  cases hr : (runPrefix (auditFocus g) w h).1 with
  | error e => trivial
  | ok out => exact ⟨by simpa only [hr] using hq, hp⟩

theorem auditFocus_preserves (hg : PrefixPreserves AllocationInv LifetimeEvent.Safe g) :
    PrefixPreserves AuditInv AuditSafe (auditFocus g) := auditFocus_ensures hg

theorem auditFocus_projects (hg : PrefixPreserves AllocationInv LifetimeEvent.Safe g) :
    ProjectsUnder AllocationInv AuditEvent.lifetime? (auditFocus g) g :=
  hg.projects_focus _ _ (fun _ => rfl)

theorem auditLift_kernel (a : M α) (ha : SameKernel a) :
    PrefixPreserves AuditInv AuditSafe (liftPrefix a) :=
  (PrefixEnsures.lift a (fun _ _ hi => hi.safe)
    (fun _ _ _ _ hi hr => hi.kernel (ha _ _ _ hr))).preserves

/-- Capture exactly the current entry. This proof-side snapshot does not add a
mirror getter or evaluate any resident-object predicate. -/
def markProbe : AuditM Unit :=
  fun w => ExceptT.mk fun h => (.ok ((), w), h ++ [AuditEvent.probe ⟨w, lifetimeHistory h⟩])

@[simp] theorem markProbe_run (w : World) (h : List AuditEvent) :
    runPrefix markProbe w h = (.ok ((), w), h ++ [AuditEvent.probe ⟨w, lifetimeHistory h⟩]) := rfl

theorem markProbe_erases : ErasesPrefix markProbe (pure ()) := fun _ _ => rfl

theorem markProbe_preserves : PrefixPreserves AuditInv AuditSafe markProbe := by
  intro w h hi
  have hl : lifetimeHistory (h ++ [AuditEvent.probe ⟨w, lifetimeHistory h⟩]) = lifetimeHistory h := by
    simp [lifetimeHistory, AuditEvent.lifetime?, List.filterMap_append]
  have hp : AllProbeValid (h ++ [AuditEvent.probe ⟨w, lifetimeHistory h⟩]) := by
    intro p hmem
    simp only [probeEntries, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, AuditEvent.probe?, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with old | rfl
    · exact hi.2 p old
    · exact hi.1
  refine ⟨[AuditEvent.probe ⟨w, lifetimeHistory h⟩], rfl, ?_, ?_⟩
  · exact ⟨hl ▸ hi.1.safe, hp⟩
  · exact ⟨hl ▸ hi.1, hp⟩

/-- The marker is invisible to committed lifetime projection on every input. -/
theorem markProbe_projects_bind (hg : ProjectsUnder I AuditEvent.lifetime? g a) :
    ProjectsUnder I AuditEvent.lifetime? (do markProbe; g) a := by
  intro w h hi
  have hp : (h ++ [AuditEvent.probe ⟨w, lifetimeHistory h⟩]).filterMap AuditEvent.lifetime? =
      h.filterMap AuditEvent.lifetime? := by simp [List.filterMap_append, AuditEvent.lifetime?]
  have hh := hg w (h ++ [AuditEvent.probe ⟨w, lifetimeHistory h⟩]) (hp ▸ hi)
  simpa only [runPrefix_bind, markProbe_run, hp] using hh

end Leanux.Proofs.WG.Lifetimes
