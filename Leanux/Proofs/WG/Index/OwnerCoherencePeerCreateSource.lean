import Leanux.Proofs.WG.Index.OwnerCoherencePeerCreateFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Exact normal result boundary of peer creation. Numeric errors precede
mutation; success records the actual initialized replacement, including cursor
aliases. Missing inputs and other Stops remain stopped. -/
theorem peerCreate_owner_fields (publicKey : Key) (psk : Option Key) (before : Device) :
    Ensures (peerCreate publicKey psk) (fun g => g.dev = some before)
      (fun result g => match result with
        | .error _ => g.dev = some before
        | .ok pid => PeerCreateAt before pid (some pid) g) := by
  have hpure {α : Type} (P : WGWorld → Prop) (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a r out after pre run; cases run; exact pre
  have hambient {α : Type} (P : WGWorld → Prop) (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient P (AmbientM.branch site value)
  have hcache (pid : PeerId) (word : Option PeerId) :
      Ensures (dstCacheReset pid) (PeerCreateAt before pid word)
        (fun _ => PeerCreateAt before pid word) := by
    let P := PeerCreateAt before pid word
    unfold dstCacheReset
    refine ensures_bind _ _ (hambient P (get : AmbientM Ambient)) ?_
    intro ambient
    have hget : Ensures (get : WG.M WGWorld) P (fun _ => P) := by
      intro g a r out after pre run; cases run; exact pre
    refine ensures_bind _ _ hget ?_
    intro g
    split
    · exact hpure P ()
    · refine ensures_bind _ _ (hambient P (AmbientM.hiddenJiffies .dstCacheResetTs)) ?_
      intro ts
      exact modifyPeer_createAt before pid word word
        (fun p => {p with dstCache := {p.dstCache with resetTs := ts}})
        (fun _ old => old) (fun _ => rfl)
  have hinit (pid : PeerId) :
      Ensures (handshakeInit pid psk) (PeerCreateAt before pid none)
        (fun _ => PeerCreateAt before pid (some pid)) := by
    unfold handshakeInit
    refine ensures_bind _ _ (modifyPeer_createAt before pid none (some pid)
      (fun p => {p with handshakeEntryPeer := some pid})
      (fun _ _ => rfl) (fun _ => rfl)) ?_
    intro _
    refine ensures_bind _ _ (hbranch (PeerCreateAt before pid (some pid)) _ _) ?_
    intro hasPsk
    cases hasPsk
    · exact precompute_createAt before pid (some pid)
    · simp only [ite_true]
      rw [← bind_assoc]
      refine ensures_bind _ _ (modifyPeer_createAt before pid (some pid) (some pid)
        (fun p => {p with presharedKey := psk.getD p.presharedKey})
        (fun _ old => old) (fun _ => rfl)) ?_
      intro _
      exact precompute_createAt before pid (some pid)
  have hreset (pid : PeerId) :
      Ensures (resetLastSentHandshake pid) (PeerCreateAt before pid (some pid))
        (fun _ => PeerCreateAt before pid (some pid)) := by
    unfold resetLastSentHandshake
    refine ensures_bind _ _ (hambient (PeerCreateAt before pid (some pid))
      (AmbientM.hiddenClock64 .resetLastSent)) ?_
    intro now
    exact modifyPeer_createAt before pid (some pid) (some pid)
      (fun p => {p with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64})
      (fun _ old => old) (fun _ => rfl)
  let tail (pid : PeerId) : WG.M (Except Int PeerId) := do
    dstCacheReset pid
    handshakeInit pid psk
    resetLastSentHandshake pid
    modifyDev fun d => {d with
      peerList := d.peerList ++ [pid]
      peerHashtable := (publicKey,pid) :: d.peerHashtable
      numPeers := d.numPeers + 1}
    return .ok pid
  have htail (pid : PeerId) : Ensures (tail pid) (PeerCreateAt before pid none)
      (fun result g => match result with
        | .error _ => g.dev = some before
        | .ok id => PeerCreateAt before id (some id) g) := by
    unfold tail
    refine ensures_bind _ _ (hcache pid none) ?_
    intro _
    refine ensures_bind _ _ (hinit pid) ?_
    intro _
    refine ensures_bind _ _ (hreset pid) ?_
    intro _ g ambient result final after pre run
    obtain ⟨current,p,device,footprint,resident,unit,self⟩ := pre
    simp [modifyDev, device] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact ⟨_,p,rfl,footprint,resident,unit,self⟩
  intro g ambient result final after device run
  let newborn : Peer := {
    remoteStatic := publicKey
    presharedKey := List.replicate 32 0
    precomputedStaticStatic := List.replicate 32 0
    internalId := g.peerCounter + 1
    cookieDecryptionKey := blake2s 32 [] ("cookie--".toUTF8.toList ++ publicKey)
    cookieMac1Key := blake2s 32 [] ("mac1----".toUTF8.toList ++ publicKey)}
  by_cases full : before.numPeers ≥ MAX_PEERS_PER_DEVICE
  · simp [peerCreate, getDev, device, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, full] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact device
  · simp [peerCreate, getDev, device, branch, branchCmp, AmbientM.branch,
      AmbientM.branchCmp, full, hiddenAlloc] at run
    generalize allocation : (AmbientM.hiddenAlloc .kmemCacheZallocPeer).run _ = choice at run
    cases choice with
    | error stop => cases run
    | ok choice =>
      obtain ⟨allocated,next⟩ := choice
      cases allocated
      · rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
        exact device
      · simp [modifyDev, setPeer] at run
        refine htail before.nextPeer _ _ result final after ?_ run
        refine ⟨{before with
          nextPeer := before.nextPeer + 1
          peers := before.peers.insert before.nextPeer newborn},newborn,?_,?_,?_,rfl,rfl⟩
        · simp [device, newborn]
        · refine ⟨rfl,rfl,?_⟩
          intro other different
          simp [Std.TreeMap.getElem?_insert, Ne.symm different]
        · simp [newborn]

end Leanux.Proofs.WG.Index
