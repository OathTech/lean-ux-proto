import Leanux.Proofs.WG.TransmitSecurity.WorkerEpochs
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDriverCuts

/-! Historical encryption identities are excluded from pending ring aliases
and active encryption batches. Bounds retain that exclusion through fresh
packet allocation and device recreation; numeric IDs alone are insufficient. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open RetirementSecurity

structure DeviceView where
  epoch : Nat
  nextPacket : Nat
  pending : List (List SkbId)

structure View where
  nextEpoch : Nat
  device : Option DeviceView

def view (w : WGWorld) : View :=
  ⟨w.netIfindexNext,w.dev.map fun d => ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩⟩

def Protected (label : Option Nat × SkbId) (active : List (List SkbId)) (s : View) : Prop :=
  ∃ generation, label.1 = some generation ∧ generation < s.nextEpoch ∧
    ∀ d, s.device = some d → d.epoch = generation →
      label.2 < d.nextPacket ∧ label.2 ∉ (d.pending ++ active).flatten

def Inv (past : List (Option Nat × SkbId)) (active : List (List SkbId)) (s : View) : Prop :=
  past.Nodup ∧ ∀ label ∈ past, Protected label active s

theorem initial (active : List (List SkbId)) (s : View) : Inv [] active s := by
  exact ⟨by simp,by intro label member; cases member⟩

/-- Existing pending aliases may disappear, and the packet frontier may
advance, without making an already used identity available again. -/
theorem Protected.shrink (before : Protected label active s)
    (epochs : s.nextEpoch ≤ t.nextEpoch)
    (keeps : ∀ d, t.device = some d → ∃ old, s.device = some old ∧
      d.epoch = old.epoch ∧ old.nextPacket ≤ d.nextPacket ∧
      (d.pending ++ later).flatten ⊆ (old.pending ++ active).flatten) :
    Protected label later t := by
  obtain ⟨generation,tag,epochBound,safe⟩ := before
  refine ⟨generation,tag,Nat.lt_of_lt_of_le epochBound epochs,?_⟩
  intro d resident same
  obtain ⟨old,found,epoch,frontier,pending⟩ := keeps d resident
  obtain ⟨bound,excluded⟩ := safe old found (epoch.symm.trans same)
  exact ⟨Nat.lt_of_lt_of_le bound frontier,fun member => excluded (pending member)⟩

/-- Fresh admission only adds IDs at or above the former packet frontier;
all historical IDs of this epoch remain below it. -/
theorem Protected.fresh_growth (before : Protected label active s)
    (epochs : s.nextEpoch ≤ t.nextEpoch)
    (keeps : ∀ d, t.device = some d → ∃ old, s.device = some old ∧
      d.epoch = old.epoch ∧ old.nextPacket ≤ d.nextPacket ∧
      ∀ id ∈ (d.pending ++ later).flatten,
        id ∈ (old.pending ++ active).flatten ∨ old.nextPacket ≤ id) :
    Protected label later t := by
  obtain ⟨generation,tag,epochBound,safe⟩ := before
  refine ⟨generation,tag,Nat.lt_of_lt_of_le epochBound epochs,?_⟩
  intro d resident same
  obtain ⟨old,found,epoch,frontier,pending⟩ := keeps d resident
  obtain ⟨bound,excluded⟩ := safe old found (epoch.symm.trans same)
  refine ⟨Nat.lt_of_lt_of_le bound frontier,?_⟩
  intro member
  rcases pending label.2 member with retained | fresh
  · exact excluded retained
  · exact (Nat.not_lt_of_ge fresh) bound

/-- A newly registered device uses the old epoch cursor, which is strictly
beyond every historical encryption's allocation epoch. -/
theorem Protected.new_device (before : Protected label active s)
    (epochs : s.nextEpoch < t.nextEpoch)
    (fresh : ∀ d, t.device = some d → d.epoch = s.nextEpoch) : Protected label later t := by
  obtain ⟨generation,tag,bound,_⟩ := before
  refine ⟨generation,tag,Nat.lt_trans bound epochs,?_⟩
  intro d found same
  have epoch := fresh d found
  omega

theorem Protected.no_device (before : Protected label active s)
    (epochs : s.nextEpoch ≤ t.nextEpoch) (absent : t.device = none) : Protected label later t := by
  obtain ⟨generation,tag,bound,_⟩ := before
  refine ⟨generation,tag,Nat.lt_of_lt_of_le bound epochs,?_⟩
  intro d found
  rw [absent] at found
  cases found

theorem Inv.separates (before : Inv past (items :: active) (view w))
    (device : w.dev = some d) :
    ∀ id ∈ items, (some d.ifindex,id) ∉ past := by
  intro id member old
  obtain ⟨generation,tag,_,safe⟩ := before.2 _ old
  have equal : d.ifindex = generation := Option.some.inj tag
  obtain ⟨_,excluded⟩ := safe ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩
    (by simp [view,device]) equal
  apply excluded
  exact List.mem_flatten.mpr ⟨items,by simp,member⟩

/-- The physical pending invariant and this historical exclusion carrier
supply the distinctness premises of the actual worker's source theorem. -/
theorem worker_nonreuse (physical : OccurrenceStack.Ready [] (items :: active) w.wg)
    (past : Inv (h.map WorkerEpochs.identity) (items :: active) (view w.wg)) :
    ((runPrefix (WorkerEncryption.tail (some items)) w h).2.map WorkerEpochs.identity).Nodup := by
  apply WorkerEpochs.tail_nonreuse (some items) w h past.1 physical.2.2.selected_unique
  cases device : w.wg.dev with
  | none =>
    intro id member
    obtain ⟨packet,resident⟩ := physical.2.2.selected_resident physical.2.1 id member
    simp [TxDisposition.txPackets,device] at resident
  | some d =>
    simpa only [PacketOrigins.epoch,device,Option.map_some,Option.getD_some] using past.separates device

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
