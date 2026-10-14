import Leanux.Proofs.WG.AllowedIps.FlatHistory
import Leanux.Proofs.WG.AllowedIps.RoutingInitial
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint

/-! Finite histories of actual normal original calls. Constructors retain
actual return values and reached-input bounds/residency, never output invariants
or agreement. This is not a Netlink, parser or enclosing Runner theorem. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux
set_option maxHeartbeats 1200000
set_option pp.structureInstances false

inductive RoutingCall where
  | create (key : WG.Key) (psk : Option WG.Key) (result : Except Int WG.PeerId)
  | insert (v4 : Bool) (addr cidr pid : Nat) (result : Int)
  | remove (pid : Nat)
  | put (peer : Option WG.PeerId)
  | clear

def RoutingCall.flat (c : RoutingCall) (xs : FlatTable × FlatTable) : FlatTable × FlatTable :=
  match c with
  | .create .. | .put .. => xs
  | .insert v4 addr cidr pid result =>
    if result = 0 then
      if v4 then (flatInsert 32 addr cidr pid xs.1, xs.2)
      else (xs.1, flatInsert 128 addr cidr pid xs.2)
    else xs
  | .remove pid => (flatRemove pid xs.1, flatRemove pid xs.2)
  | .clear => ([], [])

def flatHistory (calls : List RoutingCall) (xs : FlatTable × FlatTable) : FlatTable × FlatTable :=
  calls.foldl (fun tables c => c.flat tables) xs

inductive RoutingStep : World → RoutingCall → World → Prop where
  | create (hr : (WG.peerCreate key psk).run w = .ok (result, v)) :
      RoutingStep w (.create key psk result) v
  | insert (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
      (resident : ∃ d p, w.k.wg = some d ∧ d.peers[pid]? = some p)
      (hr : (WG.insert (if v4 then 4 else 6) addr cidr pid).run w = .ok (result, v)) :
      RoutingStep w (.insert v4 addr cidr pid result) v
  | remove (hr : (WG.removeByPeer pid).run w = .ok ((), v)) :
      RoutingStep w (.remove pid) v
  | put (hr : (WG.peerPut peer).run w = .ok ((), v)) :
      RoutingStep w (.put peer) v
  | clear (hr : WG.free.run w = .ok ((), v)) : RoutingStep w .clear v

inductive RoutingHistory : World → List RoutingCall → World → Prop where
  | nil : RoutingHistory w [] w
  | cons (step : RoutingStep w c u) (tail : RoutingHistory u cs v) : RoutingHistory w (c :: cs) v

theorem removeByPeer_input_resident (w v : World) (d : WG.Device) (pid : Nat)
    (hd : w.k.wg = some d) (hr : (WG.removeByPeer pid).run w = .ok ((), v)) :
    ∃ p, d.peers[pid]? = some p := by
  cases hp : d.peers[pid]? with
  | none => simp [WG.removeByPeer, WG.getPeer, WG.getDev, getK, hd, hp, invariant] at hr
  | some p => exact ⟨p, rfl⟩

theorem RoutingStep.refines (hs : RoutingStep w c v) (hd : w.k.wg = some d)
    (hi : RoutingInvariant d t4 t6) (he4 : FlatAgree 32 t4 xs.1) (he6 : FlatAgree 128 t6 xs.2) :
    ∃ out u4 u6, v.k.wg = some out ∧ RoutingInvariant out u4 u6 ∧
      FlatAgree 32 u4 (c.flat xs).1 ∧ FlatAgree 128 u6 (c.flat xs).2 := by
  cases hs with
  | create hr =>
    obtain ⟨out, hout, hinv⟩ := peerCreate_routing_preserved _ _ d hd hi _ _ _ hr
    exact ⟨out, t4, t6, hout, hinv, he4, he6⟩
  | put hr =>
    obtain ⟨out, hout, hinv⟩ := peerPut_routing_preserved _ _ d hd hi _ hr
    exact ⟨out, t4, t6, hout, hinv, he4, he6⟩
  | clear hr =>
    obtain ⟨out, hout, hc⟩ := free_endpoint _ _ d hd t4 t6 hi hr
    exact ⟨out, .empty, .empty, by rw [hout], Cleared.routing hi hc,
      flatAgree_empty 32, flatAgree_empty 128⟩
  | @insert addr v4 cidr pid w result v ha hc resident hr =>
    obtain ⟨old, p, hold, hp⟩ := resident
    rw [hd] at hold
    cases hold
    have hb : ((if v4 then 4 else 6 : Nat) == 4) = v4 := by cases v4 <;> rfl
    obtain ⟨out, hout, ho⟩ := insert_routing_outcome w v d hd (if v4 then 4 else 6)
      addr cidr pid p hp t4 t6 hi (by simpa only [hb] using ha) (by simpa only [hb] using hc) result hr
    have hdev : v.k.wg = some out := by rw [hout]
    rcases ho.result with ⟨hresult, _, hinv⟩ | ⟨hresult, hf⟩
    · subst result
      rw [hb] at hinv
      cases v4
      · exact ⟨out, t4, (t6.insertFresh 128 d.nextNode addr cidr pid).tree, hdev, hinv,
          he4, he6.insert hi.valid6 ha hc d.nextNode pid⟩
      · exact ⟨out, (t4.insertFresh 32 d.nextNode addr cidr pid).tree, t6, hdev, hinv,
          he4.insert hi.valid4 ha hc d.nextNode pid, he6⟩
    · subst result
      refine ⟨out, t4, t6, hdev, hf.invariant, ?_, ?_⟩
      · simpa [RoutingCall.flat, ENOMEM] using he4
      · simpa [RoutingCall.flat, ENOMEM] using he6
  | @remove pid w v hr =>
    obtain ⟨p, hp⟩ := removeByPeer_input_resident w v d pid hd hr
    obtain ⟨out, hout, hm⟩ := removeByPeer_endpoint w v d hd pid p hp t4 t6 hi.forest
      hi.nodup4 hi.nodup6 hi.compressed4 hi.compressed6 hi.lists hr
    refine ⟨out, t4.eraseIds p.allowedipsList, t6.eraseIds p.allowedipsList,
      ?_, hi.removed hm, ?_, ?_⟩
    · rw [hout]
    · exact he4.remove (resident_eraseIds_entries hi.forest hi.lists hp true)
    · exact he6.remove (resident_eraseIds_entries hi.forest hi.lists hp false)

theorem RoutingHistory.refines (history : RoutingHistory w calls v) (hd : w.k.wg = some d)
    (hi : RoutingInvariant d t4 t6) (he4 : FlatAgree 32 t4 xs.1) (he6 : FlatAgree 128 t6 xs.2) :
    ∃ out u4 u6, v.k.wg = some out ∧ RoutingInvariant out u4 u6 ∧
      FlatAgree 32 u4 (flatHistory calls xs).1 ∧ FlatAgree 128 u6 (flatHistory calls xs).2 := by
  induction history generalizing d t4 t6 xs with
  | nil => exact ⟨d, t4, t6, hd, hi, he4, he6⟩
  | cons step tail ih =>
    obtain ⟨out, u4, u6, hout, hinv, he4', he6'⟩ := step.refines hd hi he4 he6
    exact ih hout hinv he4' he6'

/-- Histories begin in the actual configured fixture. No representation or
coherence hypothesis is supplied at the end or at an intermediate step. -/
theorem RoutingHistory.initialized (history : RoutingHistory w calls v)
    (hstart : w.k = Runner.initialKernel rlimit true false foreign stepped seccompChild) :
    ∃ out t4 t6, v.k.wg = some out ∧ RoutingInvariant out t4 t6 ∧
      FlatAgree 32 t4 (flatHistory calls ([], [])).1 ∧
      FlatAgree 128 t6 (flatHistory calls ([], [])).2 := by
  obtain ⟨d, hd, hi⟩ := initialKernel_routing rlimit foreign stepped seccompChild
  rw [← hstart] at hd
  exact history.refines hd hi (flatAgree_empty 32) (flatAgree_empty 128)

def selectedFlat (v4 : Bool) (xs : FlatTable × FlatTable) : FlatTable :=
  if v4 then xs.1 else xs.2

/-- Original node lookup at the reached family root returns a flat-history
longest-prefix winner. A returned node's raw owner is identified in the actual
store; this does not assert that this raw peer label is still resident. -/
theorem RoutingHistory.findNode (history : RoutingHistory w calls v)
    (hstart : w.k = Runner.initialKernel rlimit true false foreign stepped seccompChild)
    (v4 : Bool) (key : Nat) (hk : key < 2 ^ rootWidth v4) :
    ∃ (d : WG.Device) (answer : Option Entry) (finish : World), v.k.wg = some d ∧
      (WG.findNode (rootValue d v4) (rootWidth v4) key).run v =
        .ok (answer.map Entry.id, finish) ∧ finish.k = v.k ∧
      FlatWinner (rootWidth v4) key (selectedFlat v4 (flatHistory calls ([], [])))
        (answer.map (canonical (rootWidth v4))) ∧
      ∀ e ∈ answer, ∃ n, d.nodes[e.id]? = some n ∧ n.peer = some e.peer := by
  obtain ⟨d, t4, t6, hd, hi, he4, he6⟩ := history.initialized hstart
  let t := selectedTree v4 t4 t6
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have he : FlatAgree (rootWidth v4) t (selectedFlat v4 (flatHistory calls ([], []))) := by
    cases v4
    · exact he6
    · exact he4
  obtain ⟨finish, hrun, hframe⟩ := findNode_run v d (rootWidth v4) key hw hk hd t (rootSlot v4)
    (hi.selected_rep v4) (hi.selected_valid v4)
  refine ⟨d, t.lookup (rootWidth v4) key, finish, hd, ?_, hframe,
    he.winner (Tree.lookup_spec (hi.selected_valid v4) key), ?_⟩
  · simpa only [hi.selected_root v4, Tree.lookupId] using hrun
  · intro e hem
    have hwinner := Tree.lookup_spec (hi.selected_valid v4) key
    change t.lookup (rootWidth v4) key = some e at hem
    change Winner (rootWidth v4) key t.entries (t.lookup (rootWidth v4) key) at hwinner
    rw [hem] at hwinner
    obtain ⟨n, hn⟩ := (hi.selected_rep v4).resident (Tree.entry_mem_nodeIds hwinner.1)
    exact ⟨n, hn, by simpa only [hn, Option.bind_some] using (hi.selected_rep v4).entry_owner hwinner.1⟩

end Leanux.Proofs.WG.AllowedIps
