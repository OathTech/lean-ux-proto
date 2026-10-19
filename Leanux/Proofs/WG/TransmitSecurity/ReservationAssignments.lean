import Leanux.Proofs.WG.TransmitSecurity.ReservationInitialized

/-! Positional credits for assigning each native reservation to one packet.
The interval after the preceding allocation prevents reuse by a later batch. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Use where
  packet : DataPacket
  position : Nat
  token : Nonce.Allocation
  reservation : WGRunWitness Nat

variable {u : Use} {h suffix : List Journal.Event}

def Use.Valid (h : List Journal.Event) (u : Use) : Prop :=
  h[u.position]? = some (.nonce u.token) ∧
  ReservationReceipts.Token u.packet.keypair u.reservation u.token ∧
  u.reservation.value = u.packet.nonce

def Available (h : List Journal.Event) (position : Nat) : Prop :=
  ∀ index packets r, h[index]? = some (.allocated packets r) → index < position

def Packets (h : List Journal.Event) (packets : List DataPacket) : Prop :=
  ∃ uses : List Use, uses.map Use.packet = packets ∧
    (uses.map Use.position).Pairwise (· < ·) ∧
    ∀ u ∈ uses, u.Valid h ∧ Available h u.position

def Checked (pre : List Journal.Event) : Journal.Event → Prop
  | .allocated packets r => r.Valid (packets.mapM newTxSkb) ∧ Packets pre packets
  | _ => True

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked pre event

theorem Use.Valid.bound (valid : u.Valid h) : u.position < h.length :=
  (List.getElem?_eq_some_iff.mp valid.1).choose

theorem Use.Valid.append (valid : u.Valid h) : u.Valid (h ++ suffix) :=
  ⟨(List.getElem?_append_left valid.bound).trans valid.1,valid.2⟩

theorem Available.append (before : Available h position)
    (quiet : ∀ event ∈ suffix, ReservationHistory.allocation? event = none) :
    Available (h ++ suffix) position := by
  intro index packets r found
  by_cases old : index < h.length
  · rw [List.getElem?_append_left old] at found
    exact before index packets r found
  · rw [List.getElem?_append_right (by omega)] at found
    have excluded := quiet (.allocated packets r) (List.mem_of_getElem? found)
    cases excluded

theorem Available.fresh (quiet : ∀ event ∈ suffix, ReservationHistory.allocation? event = none) :
    Available (h ++ suffix) h.length := by
  intro index packets r found
  by_cases old : index < h.length
  · exact old
  · rw [List.getElem?_append_right (by omega)] at found
    have excluded := quiet (.allocated packets r) (List.mem_of_getElem? found)
    cases excluded

theorem Packets.empty : Packets h [] :=
  ⟨[],rfl,by simp,by intro u member; cases member⟩

theorem Packets.append_history (before : Packets h packets)
    (quiet : ∀ event ∈ suffix, ReservationHistory.allocation? event = none) :
    Packets (h ++ suffix) packets := by
  obtain ⟨uses,packets,ordered,valid⟩ := before
  exact ⟨uses,packets,ordered,fun u member =>
    ⟨(valid u member).1.append,(valid u member).2.append quiet⟩⟩

theorem Packets.append_fresh (before : Packets h packets)
    (quiet : ∀ event ∈ suffix, ReservationHistory.allocation? event = none)
    (valid : u.Valid (h ++ suffix)) (fresh : u.position = h.length) :
    Packets (h ++ suffix) (packets ++ [u.packet]) := by
  obtain ⟨uses,packets,ordered,entries⟩ := before
  refine ⟨uses ++ [u],by simp only [List.map_append,List.map_cons,List.map_nil,packets],?_,?_⟩
  · rw [List.map_append,List.pairwise_append]
    refine ⟨ordered,by simp,?_⟩
    intro index member other singleton
    have equal : other = u.position := by simpa using singleton
    obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
    rw [equal,fresh]
    exact (entries entry inside).1.bound
  · intro entry member
    rcases List.mem_append.mp member with old | new
    · exact ⟨(entries entry old).1.append,(entries entry old).2.append quiet⟩
    · have equal := List.mem_singleton.mp new
      subst entry
      exact ⟨valid,by rw [fresh]; exact Available.fresh quiet⟩

end Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
