import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentBank
import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentEncryption

/-! Material-certified assignments can use the same initialized packet-origin
and encryption-identity facts, with one fixed assignment bank per history. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments.Bank
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {h : List Journal.Event} {bank : Bank}
  {r s : WorkerEncryption.Receipt} {token : Nonce.Allocation}

def Assigned (bank : Bank) (h : List Journal.Event) (r : WorkerEncryption.Receipt) (token : Nonce.Allocation) : Prop :=
  ∃ (index : Nat) (packets : List DataPacket) (allocation : WGRunWitness (List SkbId))
    (packetIndex : Nat) (u : Use),
    h[index]? = some (.allocated packets allocation) ∧
    (bank index)[packetIndex]? = some u ∧
    allocation.value[packetIndex]? = some r.id ∧
    PacketOrigins.epoch allocation.after = PacketOrigins.epoch r.read.before.wg ∧
    PacketMaterial.material u.packet = PacketMaterial.material r.read.value ∧ u.token = token

theorem Assigned.nonce (safe : BankValid h bank) (assigned : Assigned bank h r token) :
    token.nonce = r.read.value.nonce := by
  obtain ⟨index,packets,allocation,n,u,found,used,_,_,material,rfl⟩ := assigned
  have equal : u.packet.nonce = r.read.value.nonce :=
    by simpa only [PacketMaterial.material] using congrArg DataPacket.nonce material
  exact (credit_nonce (credit_valid safe found used)).trans equal

theorem Assigned.identity (safe : BankValid h bank) (nonces : (h.filterMap Journal.nonce?).Nodup)
    (left : Assigned bank h r token) (right : Assigned bank h s token) :
    WorkerEpochs.identity r = WorkerEpochs.identity s := by
  obtain ⟨i,ps,a,n,u,first,left,ri,re,_,rt⟩ := left
  obtain ⟨j,qs,b,m,v,second,right,si,se,_,st⟩ := right
  obtain ⟨batch,packet⟩ := credit_token_injective safe nonces first second left right (rt.trans st.symm)
  subst j
  subst m
  rw [first] at second
  cases second
  have ids : r.id = s.id := Option.some.inj (ri.symm.trans si)
  exact Prod.ext (re.symm.trans se) ids

theorem assigned_of_origin (safe : BankValid h bank) (origin : PacketOrigins.ReadOrigin h r.id r.read) :
    ∃ token, Assigned bank h r token := by
  obtain ⟨generation,epoch,packets,allocation,member,_,allocationEpoch,n,packet,atPacket,atId,material⟩ := origin
  obtain ⟨before,after,position⟩ := List.mem_iff_append.mp member
  have found : h[before.length]? = some (.allocated packets allocation) := by
    rw [position]
    simp
  have map := (safe _ _ _ found).1
  rw [←map,List.getElem?_map] at atPacket
  cases atUse : (bank before.length)[n]? with
  | none => simp [atUse] at atPacket
  | some u =>
    rw [atUse] at atPacket
    have same : u.packet = packet := Option.some.inj atPacket
    exact ⟨u.token,before.length,packets,allocation,n,u,found,atUse,atId,
      allocationEpoch.trans epoch.symm,by rw [same]; exact material,rfl⟩

def Exclusive (bank : Bank) (h : List Journal.Event) : Prop :=
  (∀ r ∈ h.filterMap Journal.encryption?, ∃ token, Assigned bank h r token ∧ token.nonce = r.read.value.nonce) ∧
  (h.filterMap Journal.encryption?).Pairwise
    (fun r s => ∀ token, Assigned bank h r token → Assigned bank h s token → False)

theorem exclusive (safe : BankValid h bank) (nonces : (h.filterMap Journal.nonce?).Nodup)
    (origins : PacketOrigins.Safe h) (encryptions : EncryptionHistory.Safe h) : Exclusive bank h := by
  constructor
  · intro r member
    obtain ⟨token,assigned⟩ := assigned_of_origin safe (origins.worker r member).2
    exact ⟨token,assigned,assigned.nonce safe⟩
  · have different := List.pairwise_map.mp encryptions
    exact different.imp (fun unequal token left right => unequal (left.identity safe nonces right))

end Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments.Bank
