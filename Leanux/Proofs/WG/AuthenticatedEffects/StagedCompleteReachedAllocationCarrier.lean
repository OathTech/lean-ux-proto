import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationFrames

/-! A partial native allocation extends the physical cell map while its fixed
ticket ledger remains selected. A transient alias names an existing selected
ticket by ordinal; it is not an additional admission or an allocated receipt.
The complete entry carrier is retained at the actual entry, not asserted of
an interior world whose newly created cells have not yet been journaled. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal

def Alias (history : List Event) (ledger : Ledger) (generation : Nat)
    (pid : PeerId) (stamp position : Nat) (packets : List DataPacket)
    (count : Nat) (items : List SkbId) (v : WGWorld) (skb : SkbId) (value : DataPacket) : Prop :=
  ∃ ordinal ticket packet,
    ordinal<count ∧ (pendingAt (.selected position) ledger)[ordinal]?=some ticket ∧
    packets[ordinal]?=some packet ∧ items[ordinal]?=some skb ∧
    Born history generation pid stamp ticket packet.plaintext ∧ packet.peer=pid ∧
    PacketMaterial.material packet=value ∧ TxDisposition.txPackets v skb=some packet

structure Interval (history : List Event) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (generation : Nat)
    (pid : PeerId) (peer : Peer) (position : Nat) (kid : KeypairId)
    (packets : List DataPacket) (w : WGWorld) (a : Ambient)
    (count : Nat) (items : List SkbId) (v : WGWorld) : Prop where
  entry : CompleteSelected.Ready ledger debts locals generation pid peer position history w a
  shape : BatchPayload.Shape pid kid peer.staged packets
  path : Path packets w a count items v

theorem Interval.device
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v) :
    ∃ d, w.dev=some d := by
  have epoch := cut.entry.vacant.1
  cases device : w.dev with
  | none=>simp [Packets.epoch,device] at epoch
  | some d=>exact ⟨d,rfl⟩

/-- The exact loop ordinal ties the new cell to the original birth and to
the still-selected fixed ticket, even when plaintexts are duplicated. -/
theorem Interval.alias_at
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v)
    (below : ordinal<n) :
    ∃ skb value, items[ordinal]?=some skb ∧
      Alias history ledger generation pid peer.internalId position packets n items v skb value := by
  have aligned := cut.entry.toHeld.allocation_alignment cut.shape
  have bound : ordinal<(pendingAt (.selected position) ledger).length := by
    rw [alignment_length aligned]
    exact Nat.lt_of_lt_of_le below cut.path.bound
  let ticket := (pendingAt (.selected position) ledger)[ordinal]
  have atTicket : (pendingAt (.selected position) ledger)[ordinal]?=some ticket :=
    List.getElem?_eq_getElem bound
  obtain ⟨packet,payload,born,owner⟩ := aligned_at aligned atTicket
  have prefixPayload : (packets.take n)[ordinal]?=some packet := by
    simpa only [List.getElem?_take_of_lt below] using payload
  obtain ⟨d,device⟩ := cut.device
  obtain ⟨skb,atCell,resident⟩ :=
    PacketAllocation.records (packets.take n) device cut.path.native ordinal packet prefixPayload
  exact ⟨skb,PacketMaterial.material packet,atCell,
    ordinal,ticket,packet,below,atTicket,payload,atCell,born,owner,rfl,resident⟩

theorem Interval.alias_member
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v)
    {skb : SkbId} (member : skb∈items) :
    ∃ value, Alias history ledger generation pid peer.internalId position packets n items v skb value := by
  obtain ⟨ordinal,atId⟩ := List.mem_iff_getElem?.mp member
  have below := (List.getElem?_eq_some_iff.mp atId).1
  rw [cut.path.length] at below
  obtain ⟨other,value,atOther,alias⟩ := cut.alias_at below
  have same : other=skb := Option.some.inj (atOther.symm.trans atId)
  subst other
  exact ⟨value,alias⟩

/-- Projection to ledger obligations: allocating a silent prefix has neither
settled nor duplicated any selected ticket. The alias uses that same entry. -/
theorem Alias.obligation
    (alias : Alias history ledger generation pid stamp position packets n items v skb value) :
    ∃ ordinal ticket packet,
      ordinal<n ∧ (ticket,Status.pending (.selected position))∈ledger ∧
      packets[ordinal]?=some packet ∧ items[ordinal]?=some skb ∧
      Born history generation pid stamp ticket packet.plaintext ∧ packet.peer=pid := by
  obtain ⟨ordinal,ticket,packet,below,atTicket,payload,atCell,born,owner,_,_⟩ := alias
  exact ⟨ordinal,ticket,packet,below,
    mem_pendingAt.mp (List.mem_iff_getElem?.mpr ⟨ordinal,atTicket⟩),payload,atCell,born,owner⟩

/-- Every interior resident cell is either an older tracked allocation or a
transient alias of this exact selected batch. No receipt is invented for it. -/
theorem Interval.covered
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v)
    {skb : SkbId} (cell : PacketMaterial.view v skb=some value) :
    (∃ epoch ticket batch ordinal,
      Packets.epoch v=some epoch ∧ Origin history batch ordinal epoch skb value ∧
      Tracked ledger debts ticket batch ordinal) ∨
    Alias history ledger generation pid peer.internalId position packets n items v skb value := by
  obtain ⟨packet,resident,material⟩ := Option.map_eq_some_iff.mp cell
  rcases RetirementSecurity.allocate_survivor (packets.take n) a a cut.path.native resident with fresh|old
  · obtain ⟨other,alias⟩ := cut.alias_member fresh
    obtain ⟨ordinal,ticket,original,below,atTicket,payload,atId,born,owner,_,stored⟩ := alias
    have same : original=packet := Option.some.inj (stored.symm.trans resident)
    subst original
    exact Or.inr ⟨ordinal,ticket,packet,below,atTicket,payload,atId,born,owner,material,resident⟩
  · have oldCell : PacketMaterial.view w skb=some value := by
      simp only [PacketMaterial.view,old,Option.map_some,material]
    obtain ⟨epoch,ticket,batch,ordinal,time,origin,tracked⟩ := cut.entry.core.physical.covered skb value oldCell
    obtain ⟨d,device⟩ := cut.device
    exact Or.inl ⟨epoch,ticket,batch,ordinal,(cut.path.epoch device).trans time,origin,tracked⟩

/-- Native bounds and exact ownership include only the allocated prefix as
an unpublished local batch, alongside the unchanged incoming local owners. -/
theorem Interval.native
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v) :
    NativeReady.Inv (⟨.unpublished,pid,items⟩::locals) v := by
  obtain ⟨d,device⟩ := cut.device
  exact cut.path.native_ready cut.entry.native device pid

theorem Interval.old_backing
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v) :
    Resident history ledger v ∧ DebtsResident history ledger debts v :=
  ⟨cut.path.old_resident cut.entry.core.physical.resident cut.entry.native.1,
   cut.path.old_cleanup cut.entry.core.physical.cleanup cut.entry.native.1⟩

theorem Interval.epoch
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v) :
    Packets.epoch v=some generation := by
  obtain ⟨d,device⟩ := cut.device
  exact (cut.path.epoch device).trans cut.entry.vacant.1

/-- Transient cells cannot alias any cell already resident at this selected
entry. Freshness follows from the actual native frontier and packet bounds. -/
theorem Interval.new_not_old
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v)
    (alias : Alias history ledger generation pid peer.internalId position packets n items v skb value)
    (packet : DataPacket) : TxDisposition.txPackets w skb≠some packet := by
  obtain ⟨ordinal,_,_,_,_,_,atId,_⟩ := alias
  intro old
  exact (cut.path.fresh cut.entry.native.1 old).1
    (List.mem_iff_getElem?.mpr ⟨ordinal,atId⟩)

/-- A prefix cell has a unique selected ordinal, independent of packet-value
equality. Thus its transient alias cannot count two selected obligations. -/
theorem Interval.ordinal_unique
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v)
    {left right : Nat} {skb : SkbId} (first : items[left]?=some skb) (second : items[right]?=some skb) :
    left=right := by
  obtain ⟨d,device⟩ := cut.device
  exact nodup_ordinal (cut.path.distinct device) first second

theorem Interval.ticket_unique
    (cut : Interval history ledger debts locals generation pid peer position kid packets w a n items v)
    {left right : Nat} {skb : SkbId} (first : items[left]?=some skb) (second : items[right]?=some skb)
    (atFirst : (pendingAt (.selected position) ledger)[left]?=some ticket)
    (atSecond : (pendingAt (.selected position) ledger)[right]?=some other) : ticket=other := by
  have same := cut.ordinal_unique first second
  subst right
  exact Option.some.inj (atFirst.symm.trans atSecond)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
