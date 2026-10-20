import PairAllowedipsFrame
import PairCountUpdate

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem mapM_project {xs : List α} {ys : List β}
    {f : α → Except ε β} {g : α → Except ε γ} (project : β → γ)
    (run : xs.mapM f = .ok ys)
    (step : ∀ x y, f x = .ok y → g x = .ok (project y)) :
    xs.mapM g = .ok (ys.map project) := by
  induction xs generalizing ys with
  | nil => cases run; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at run ⊢
    obtain ⟨y,head,run⟩ := bind_ok run
    obtain ⟨tail,rest,run⟩ := bind_ok run
    cases Except.ok.inj run
    rw [step x y head]
    rw [ih rest]
    rfl

theorem word_path {m : DataMem} {a size value : Nat} {sourcePath : String}
    (to : String) (read : word m sourcePath a size = .ok value) :
    word m to a size = .ok value := by
  unfold word at read ⊢
  split at read
  · split
    · cases bytes : m.loadBytes (.ofNat 64 a) size with
      | none => simp only [bytes] at read; cases read
      | some bytes => simpa only [bytes] using read
    · contradiction
  · cases read

def trieState (s : State) : Trie.State :=
  ⟨s.nodes.map (fun (id,n) => (id,Trie.targetNode n)),
    s.peers.map (fun (id,count,_) => (id,count))⟩

/-- The stronger executable decoder entails the old lookup decoder. No second
interpretation or successful reconstruction is assumed at the call boundary. -/
theorem reconstruct_trie {names o m s}
    (run : reconstruct names o m = .ok s) :
    Trie.reconstruct names.trie o m = .ok (trieState s) := by
  unfold reconstruct at run
  obtain ⟨_,valid,run⟩ := bind_ok run
  obtain ⟨r4,root4,run⟩ := bind_ok run
  obtain ⟨root4,root4Decoded,run⟩ := bind_ok run
  obtain ⟨r6,root6,run⟩ := bind_ok run
  obtain ⟨root6,root6Decoded,run⟩ := bind_ok run
  obtain ⟨seq,seqRead,run⟩ := bind_ok run
  obtain ⟨nodes,nodeReads,run⟩ := bind_ok run
  obtain ⟨peers,peerReads,run⟩ := bind_ok run
  cases Except.ok.inj run
  unfold validate at valid
  obtain ⟨_,baseValid,_⟩ := bind_ok valid
  have ns := mapM_project (fun (id,n) => (id,Trie.targetNode n)) nodeReads (g :=
    fun (id,a) => do return (id,← Trie.decodeNode names.trie o m a)) (by
      rintro ⟨id,a⟩ ⟨id',n⟩ decoded
      unfold decodeNode at decoded
      obtain ⟨core,coreRead,decoded⟩ := bind_ok decoded
      obtain ⟨raw,rawRead,decoded⟩ := bind_ok decoded
      obtain ⟨slot,parentRead,decoded⟩ := bind_ok decoded
      cases Except.ok.inj decoded
      simp only [coreRead]
      cases core
      rfl)
  have ps := mapM_project (fun (id,count,_) => (id,count)) peerReads (g :=
    fun (id,a) => do return (id,← word m s!"peer[{id}].refcount" (a+o.peerRefcount) 4)) (by
      rintro ⟨id,a⟩ ⟨id',count,list⟩ decoded
      unfold decodePeer at decoded
      obtain ⟨value,read,decoded⟩ := bind_ok decoded
      obtain ⟨first,firstRead,decoded⟩ := bind_ok decoded
      obtain ⟨list,listRead,decoded⟩ := bind_ok decoded
      cases Except.ok.inj decoded
      simp only [word_path s!"peer[{id}].refcount" read]
      rfl)
  simp only [Trie.reconstruct,baseValid,ns,ps,trieState]
  rfl

theorem trieState_target (d : Device) : trieState (target d) = Trie.target d := by
  simp only [trieState,target,Trie.target,List.map_map]
  rfl

theorem Corresponds.trie {names o m d} (related : Corresponds names o m d) :
    Trie.Corresponds names.trie o m d := by
  change Trie.reconstruct names.trie o m = .ok (Trie.target d)
  simpa only [trieState_target] using reconstruct_trie related

#print axioms reconstruct_trie
end Binary.Pair.Allowedips
