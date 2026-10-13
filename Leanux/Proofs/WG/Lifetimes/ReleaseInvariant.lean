import Leanux.Proofs.WG.Lifetimes.KeypairAccess

/-! Release-only strengthening of mixed access safety. No allocation frontier
or device-epoch order is assumed. Existing access contracts carry uniqueness
through their arbitrary identity-view predicate. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def ResidentUnique (resident : ι → Option κ) : Prop :=
  ∀ i j stamp, resident i = some stamp → resident j = some stamp → i = j

def eraseResident [DecidableEq ι] (resident : ι → Option κ) (i : ι) : ι → Option κ :=
  fun j => if j = i then none else resident j

theorem ResidentUnique.erase [DecidableEq ι] (hu : ResidentUnique resident) (i : ι) :
    ResidentUnique (eraseResident resident i) := by
  intro j k stamp hj hk
  have hj' : resident j = some stamp := by
    by_cases h : j = i <;> simp_all [eraseResident]
  have hk' : resident k = some stamp := by
    by_cases h : k = i <;> simp_all [eraseResident]
  exact hu j k stamp hj' hk'

theorem ResidentUnique.erase_absent {resident : ι → Option κ} {i : ι} {stamp : κ}
    [DecidableEq ι] (hu : ResidentUnique resident)
    (hl : resident i = some stamp) : ∀ j, eraseResident resident i j ≠ some stamp := by
  intro j hj
  by_cases he : j = i
  · simp [eraseResident, he] at hj
  · have live : resident j = some stamp := by simpa [eraseResident, he] using hj
    exact he (hu j i stamp live hl)

theorem ResidentSafe.erase {resident : ι → Option κ} {i : ι} {stamp : κ}
    {h : List (AccessEvent ι κ)} [DecidableEq ι] (hi : ResidentSafe h resident)
    (hu : ResidentUnique resident) (hl : resident i = some stamp) :
    ResidentSafe (h ++ [.release i stamp]) (eraseResident resident i) := by
  refine ⟨AccessEvent.safe_append_release hi.1, ?_⟩
  intro s hs j hj
  rcases AccessEvent.released_append_release.mp hs with old | new
  · by_cases he : j = i
    · simp [eraseResident, he] at hj
    · exact hi.2 s old j (by simpa [eraseResident, he] using hj)
  · subst s
    exact hu.erase_absent hl j hj

def ReleaseUnique (s : IdentityView) : Prop :=
  ResidentUnique s.2.1 ∧ ResidentUnique s.2.2

def ReleaseInv (h : List LifetimeEvent) (w : World) : Prop :=
  MixedInv h w ∧ ReleaseUnique (identityView w)

theorem ReleaseInv.safe (hi : ReleaseInv h w) : LifetimeEvent.Safe h := hi.1.safe

theorem ReleaseInv.keyRelease (hi : ReleaseInv h w)
    (hl : keypairResidents w i = some stamp)
    (hp : Peers.snapshot v = Peers.snapshot w)
    (hk : keypairResidents v = eraseResident (keypairResidents w) i)
    (ht : packetResidents v = packetResidents w) :
    ReleaseInv (h ++ [.keypair (.release i stamp)]) v := by
  constructor
  · constructor
    · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?, Peers.AccessInv, hp] using hi.1.peer
    · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?, hk] using
        hi.1.keypair.erase hi.2.1 hl
    · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?, ht] using hi.1.packet
  · exact ⟨by simpa only [identityView, hk] using hi.2.1.erase i,
      by simpa only [identityView, ht] using hi.2.2⟩

theorem ReleaseInv.packetRelease (hi : ReleaseInv h w)
    (hl : packetResidents w i = some stamp)
    (hp : Peers.snapshot v = Peers.snapshot w)
    (hk : keypairResidents v = keypairResidents w)
    (ht : packetResidents v = eraseResident (packetResidents w) i) :
    ReleaseInv (h ++ [.packet (.release i stamp)]) v := by
  constructor
  · constructor
    · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?, Peers.AccessInv, hp] using hi.1.peer
    · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?, hk] using hi.1.keypair
    · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?, ht] using
        hi.1.packet.erase hi.2.2 hl
  · exact ⟨by simpa only [identityView, hk] using hi.2.1,
      by simpa only [identityView, ht] using hi.2.2.erase i⟩

end Leanux.Proofs.WG.Lifetimes
