import Leanux.Proofs.WG.RetirementSecurity.ConfiguredSessionFunding
import Leanux.Proofs.WG.RetirementSecurity.SlotAnchorConsumers

/-! A data-only boundary carrier: a peer with a published key slot is live.
The actual make-dead/clear interval has explicit selected exceptions. Combined
with the existing configured registry and peer ledger, this derives the stamped
base reference needed by retirement; it does not assume key funding. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

def cell (p : Peer) := (p.isDead,slotFields p)
def view (w : WGWorld) := fun pid => (peerAt w pid).map cell

def InvExcept (pending : List PeerId) (w : WGWorld) : Prop :=
  ∀pid p,peerAt w pid=some p → pid∉pending → HasKeySlot p → p.isDead=false
abbrev Inv := InvExcept []

def Good (p : Bool × (Option KeypairId × Option KeypairId × Option KeypairId)) : Prop :=
  (p.2.1≠none ∨ p.2.2.1≠none ∨ p.2.2.2≠none) → p.1=false

theorem projection : InvExcept pending w ↔ ∀pid p,view w pid=some p → pid∉pending → Good p := by
  constructor
  · intro before pid p found outside
    obtain ⟨q,resident,rfl⟩ := Option.map_eq_some_iff.mp found
    exact before pid q resident outside
  · intro before pid p resident outside slots
    exact before pid (cell p) (by simp [view,resident]) outside slots

theorem transport (before : InvExcept pending w) (same : view v=view w) : InvExcept pending v := by
  apply projection.mpr
  intro pid p found outside
  exact projection.mp before pid p (same ▸ found) outside

theorem frame {action : WG.M α} (same : SameView view action) : Preserves (InvExcept pending) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact transport before ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem store_view {action : WG.M α} (same : SameWGStore action) : SameView view action :=
  same.of_factor (fun s : WGStoreView=>view {dev:=s.dev}) view (fun _=>rfl)

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (InvExcept pending) action :=
  frame (store_view same)

theorem peers (before : InvExcept pending w) (same : peersAt v=peersAt w) : InvExcept pending v := by
  intro pid p resident outside slots
  have found : peerAt w pid=some p := by
    have point := congrArg (fun d=>d.bind fun peers=>peers[pid]?) same
    have equality : peerAt v pid=peerAt w pid := by
      simpa only [peersAt,peerAt,Option.bind_map,Function.comp_def] using point
    exact equality.symm.trans resident
  exact before pid p found outside slots

theorem replace (before : InvExcept pending w) (device : w.dev=some d) (stored : d.peers[pid]?=some p)
    (slots : HasKeySlot q → HasKeySlot p) (alive : p.isDead=false → q.isDead=false) :
    InvExcept pending (replacePeer w d pid q) := by
  intro other current found outside present
  by_cases same : pid=other
  · subst other
    simp only [peerAt,replacePeer,Option.bind_some,Std.TreeMap.getElem?_insert_self,Option.some.injEq] at found
    subst current
    exact alive (before pid p (by simp [peerAt,device,stored]) outside (slots present))
  · exact before other current (by simpa [peerAt,replacePeer,device,Std.TreeMap.getElem?_insert,same] using found) outside present

theorem update (pid : PeerId) (f : Peer → Peer)
    (slots : ∀p,HasKeySlot (f p) → HasKeySlot p)
    (alive : ∀p,p.isDead=false → (f p).isDead=false) :
    Preserves (InvExcept pending) (getPeer pid >>= fun p=>setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,c,getter,setter⟩ := run
  obtain ⟨same,time,d,device,stored⟩ := getPeer_normal pid w read p a c getter
  subst read
  subst c
  have final : (((),replacePeer w d pid (f p)),a)=((result,v),b) := by
    simpa [setPeer,modifyDev,replacePeer,device] using setter
  cases final
  exact replace before device stored (slots p) (alive p)

theorem update_then (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (slots : ∀p,HasKeySlot (f p) → HasKeySlot p)
    (alive : ∀p,p.isDead=false → (f p).isDead=false)
    (next : ∀x,Preserves (InvExcept pending) (tail x)) :
    Preserves (InvExcept pending) (getPeer pid >>= fun p=>setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update pid f slots alive) next

theorem modify (f : Device → Device) (same : ∀d,(f d).peers=d.peers) :
    Preserves (InvExcept pending) (modifyDev f) := by
  apply hoare_modify
  intro w before
  apply peers before
  simp only [peersAt,Option.map_map,Function.comp_def,same]

theorem index (action : IndexM α) : Preserves (InvExcept pending) (liftIndex action) := by
  apply hoare_liftIndex
  intro w d table before device
  apply peers before
  simp only [peersAt,device,Option.map_some]

theorem key_put (id : Option KeypairId) (now : Bool) :
    Preserves (InvExcept pending) (keypairPut id now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact peers before (put_peers id now w v a b run)

theorem initial (net bare : Bool) : Inv (Runner.initialWG net bare) := by
  intro pid p found _ _
  unfold peerAt Runner.initialWG at found
  split at found <;> simp at found

/-- Boundary liveness, configured completeness and actual funded alignment
derive the independent stamped base reference. No numeric-slot persistence or
key credit is inferred from the peer ledger. -/
theorem references (before : Inv w) (funded : holders.Funded carriers loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w) :
    SlotPeerReferences holders loans w := by
  intro d pid p device stored slots
  exact List.mem_append_left _ (live_peer_base_reference funded coherent configured device stored
    (before pid p (by simp [peerAt,device,stored]) (by simp) slots))

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
