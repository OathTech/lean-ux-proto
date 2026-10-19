import Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoanRepayment

/-! Exact successful index-lookup caller for the full peer loan. An initialized
owner-word positivity claim is unnecessary on this successful arm; it remains
necessary to exclude mutation by a failed zero-count acquisition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def scanStep (kinds : List IndexKind) (index : Nat)
    (entry : IndexEntry) (state : Option IndexEntry × Bool) :
    WG.M (ForInStep (Option IndexEntry × Bool)) := do
  _ ← branch .idxWalk true
  if ← branch .idxMatch (entry.index == index) then
    if ← branch .idxTypeMatch (kinds.contains entry.kind) then
      return .done (some entry,true)
    return .done (state.1,true)
  return .yield state

def scan (kinds : List IndexKind) (index : Nat) : WG.M (Option IndexEntry × Bool) := do
  let entries ← liftIndex (indexBucket index)
  forIn entries (none,false) (scanStep kinds index)

def lookupTail (state : Option IndexEntry × Bool) : WG.M (Option (IndexOwner × PeerId)) := do
  let (entry,stopped) := state
  if !stopped then _ ← branch .idxWalk false
  if ← branch .idxFound entry.isSome then
    let some entry := entry | invariant "unreachable"
    let peer ← Affiliation.acquireOwner entry.owner
    if ← branch .idxPeerAlive peer.isSome then
      let some pid := peer | invariant "unreachable"
      return some (entry.owner,pid)
  return none

theorem lookup_factor (kinds : List IndexKind) (index : Nat) :
    indexLookup kinds index = (scan kinds index >>= lookupTail) := by
  rw [←Affiliation.indexLookupSource_eq]
  simp only [Affiliation.indexLookupSource,scan,bind_assoc]
  rfl

theorem scan_same_world (kinds : List IndexKind) (index : Nat) :
    SameView (id : WGWorld → WGWorld) (scan kinds index) := by
  intro initial
  change Preserves (fun w => w = initial) _
  unfold scan
  apply preserves_bind
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a entries v b hi run
    cases hd : w.dev with
    | none => simp [liftIndex_run,hd] at run
    | some d =>
      simp [liftIndex_run,indexBucket,hd] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      simpa only [←hd] using hi
  · intro entries
    apply list_view_spec id (fun w => w = initial)
    intro entry state
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    cases same : (entry.index == index) <;> cases kind : (kinds.contains entry.kind) <;>
      simp [scanStep,branch,same,kind,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
        except_ok_bind,except_pure] at run
    all_goals rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact hi

theorem index_success (kinds : List IndexKind) (index : Nat)
    (w v : WGWorld) (owner : IndexOwner) (pid : PeerId) (a b : Ambient)
    (run : ((indexLookup kinds index).run w).run a = .ok ((some (owner,pid),v),b)) :
    Loan w pid v := by
  rw [lookup_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨⟨entry,stopped⟩,u,c,scanned,tail⟩ := run
  have same := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (scan_same_world kinds index) w a _ u c scanned
  change u = w at same
  subst u
  cases stopped <;> cases entry <;>
    simp [lookupTail,branch,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
      except_ok_bind,except_pure] at tail
  case false.some entry =>
    cases acquired : ((Affiliation.acquireOwner entry.owner).run w).run
        (record (record c .idxWalk false) .idxFound true) with
    | error err => simp [acquired] at tail
    | ok out =>
      rcases out with ⟨⟨result,u⟩,d⟩
      cases result <;> simp [acquired,except_ok_bind] at tail
      rcases tail with ⟨⟨⟨_,rfl⟩,rfl⟩,_⟩
      exact acquire entry.owner w _ _ _ _ acquired
  case true.some entry =>
    cases acquired : ((Affiliation.acquireOwner entry.owner).run w).run
        (record c .idxFound true) with
    | error err => simp [acquired] at tail
    | ok out =>
      rcases out with ⟨⟨result,u⟩,d⟩
      cases result <;> simp [acquired,except_ok_bind] at tail
      rcases tail with ⟨⟨⟨_,rfl⟩,rfl⟩,_⟩
      exact acquire entry.owner w _ _ _ _ acquired

/-- A refused response after its actual successful lookup restores all peer
records, including reference counts and nullable owner words. The loan is a
conclusion of that lookup, not an extra premise. -/
theorem response_after_lookup (msg : Key) (w u v : WGWorld) (device : Device)
    (owner pid : PeerId) (a b c : Ambient)
    (present : w.dev = some device) (identity : device.staticIdentity.hasIdentity = true)
    (lookup : ((indexLookup [.handshake] (u32le msg 8)).run w).run
      (record a .crespNoIdentity false) = .ok ((some (.handshake owner,pid),u),b))
    (refused : ((consumeResponse msg).run w).run a = .ok ((none,v),c)) :
    residents v = residents w := by
  have loan := index_success [.handshake] (u32le msg 8) w u (.handshake owner) pid _ b lookup
  rw [Queues.RxCredits.HandshakeLoans.consumeResponse_factor] at refused
  simp [getDev,present,StateT.run_bind,branch,branch_run,identity,lookup] at refused
  exact (hoare_iff_run_ambient _ _ _).mp
    (response_tail msg device.staticIdentity pid w) u _ none v c loan refused rfl

end Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
