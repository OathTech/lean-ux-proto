import Leanux.Proofs.WG.TransmitSecurity.StagedTransferFrames

/-! Staged overflow removes an ordered prefix and charges precisely its length.
The invariant records positions rather than treating equal payloads as one
packet. The existing native finite loop is unchanged. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def Trimmed (pid : PeerId) (stamp : Nat) (packets : List Packet) (count : Nat)
    (prior : PeerId → Option (Nat × List Packet)) (w : WGWorld) : Prop :=
  ∃ n, n ≤ packets.length ∧ stagedAt w pid = some (stamp,packets.drop n) ∧
    dropped w = some (count+n) ∧ ∀ q, pid ≠ q → stagedAt w q = prior q

def trimBody (pid : PeerId) : WG.M (ForInStep Unit) := do
  let p ← getPeer pid
  if ← branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS) then
    setPeer pid {p with staged := p.staged.drop 1}
    modifyDev fun d => {d with txDropped := d.txDropped + 1}
    pure (.yield ())
  else pure (.done ())

theorem trim_body (pid stamp : Nat) (packets : List Packet) (count : Nat)
    (prior : PeerId → Option (Nat × List Packet)) :
    Preserves (Trimmed pid stamp packets count prior) (trimBody pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  unfold trimBody at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,middle,clock,read,tail⟩ := run
  obtain ⟨rfl,rfl,d,device,resident⟩ := Origins.getPeer_return pid w middle p a clock read
  obtain ⟨n,bound,slot,charged,others⟩ := before
  have identity : p.internalId = stamp ∧ p.staged = packets.drop n := by
    simpa only [stagedAt,device,Option.bind_some,resident,Option.map_some,
      Option.some.injEq,Prod.mk.injEq] using slot
  have counter : d.txDropped = count+n := by
    simpa only [dropped,device,Option.map_some,Option.some.injEq] using charged
  by_cases excess : p.staged.length > MAX_STAGED_PACKETS
  · simp [branch,AmbientM.branch,excess,setPeer,modifyDev,device] at tail
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := tail
    have nonempty : 0 < (packets.drop n).length := by rw [← identity.2]; omega
    refine ⟨n+1,?_,?_,?_,?_⟩
    · simp only [List.length_drop] at nonempty; omega
    · simp [stagedAt,identity]
    · simp only [dropped,Option.map_some,counter,Nat.add_assoc]
    · intro q different
      simpa only [stagedAt,device,Option.bind_some,Std.TreeMap.getElem?_insert,
        Std.LawfulEqOrd.compare_eq_iff_eq,different,↓reduceIte] using others q different
  · simp [branch,AmbientM.branch,excess] at tail
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := tail
    exact ⟨n,bound,slot,charged,others⟩

theorem trim_preserves (pid stamp : Nat) (packets : List Packet) (count : Nat)
    (prior : PeerId → Option (Nat × List Packet)) :
    Preserves (Trimmed pid stamp packets count prior) (xmitTrim pid) := by
  unfold xmitTrim
  have read : Preserves (Trimmed pid stamp packets count prior) (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    rw [(getPeer_normal pid w v p a b run).1]
    exact hi
  apply preserves_bind read
  intro peer
  apply preserves_bind
  · rw [Std.Legacy.Range.forIn_eq_forIn_range']
    apply list_view_spec id (Trimmed pid stamp packets count prior)
    intro index acc
    exact trim_body pid stamp packets count prior
  · intro result
    exact preserves_pure _

/-- Every successful native overflow pass partitions the old staged list into
an initial discarded prefix and an ordered retained suffix. Each discarded
position contributes exactly one to tx_dropped; other peers' queues are fixed. -/
theorem trim_exact (pid : PeerId) (r : WGRunWitness Unit)
    (valid : r.Valid (xmitTrim pid)) :
    ∀ d p, r.before.dev = some d → d.peers[pid]? = some p →
      ∃ n, n ≤ p.staged.length ∧
        stagedAt r.after pid = some (p.internalId,p.staged.drop n) ∧
        dropped r.after = some (d.txDropped+n) ∧
        (∀ q, pid ≠ q → stagedAt r.after q = stagedAt r.before q) ∧
        p.staged.take n ++ p.staged.drop n = p.staged := by
  intro d p device resident
  have initial : Trimmed pid p.internalId p.staged d.txDropped (stagedAt r.before) r.before := by
    exact ⟨0,by omega,by simp [stagedAt,device,resident],by simp [dropped,device],fun _ _ => rfl⟩
  obtain ⟨n,bound,slot,count,others⟩ := (hoare_iff_run_ambient _ _ _).mp
    (trim_preserves pid p.internalId p.staged d.txDropped (stagedAt r.before))
    r.before r.ambientBefore r.value r.after r.ambientAfter initial valid
  exact ⟨n,bound,slot,count,others,List.take_append_drop n p.staged⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged
