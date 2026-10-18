import Leanux.Proofs.WG.RetirementSecurity.Put

/-! Retention frames for retirement. The projection keeps every key field
except its reference count, so sending material and the nonce frontier are
retained without confusing reference payment with key reinitialization. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

def keyCore (k : Keypair) : Keypair := {k with refcount := 0}

structure Retains (before after : WGWorld) : Prop where
  counter : after.keypairCounter = before.keypairCounter
  keys : ∀ id k, keyAt after id = some k →
    ∃ old, keyAt before id = some old ∧ keyCore k = keyCore old

theorem Retains.refl (w : WGWorld) : Retains w w :=
  ⟨rfl, fun _ k found => ⟨k,found,rfl⟩⟩

theorem Retains.trans (first : Retains w u) (second : Retains u v) : Retains w v := by
  refine ⟨second.counter.trans first.counter,?_⟩
  intro id k found
  obtain ⟨middle,hm,eq⟩ := second.keys id k found
  obtain ⟨old,ho,eq'⟩ := first.keys id middle hm
  exact ⟨old,ho,eq.trans eq'⟩

theorem PutEffect.retains {id : KeypairId} (effect : PutEffect id now k w v)
    (resident : keyAt w id = some k) : Retains w v := by
  refine ⟨effect.frontier,?_⟩
  intro other current found
  by_cases same : other = id
  · subst other
    rw [effect.selected,keyAfterPut] at found
    split at found
    · cases found
    · cases found
      exact ⟨k,resident,rfl⟩
  · exact ⟨current,(effect.others other same).symm.trans found,rfl⟩

theorem put_retains (kp : Option KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient)
    (run : ((keypairPut kp now).run w).run a = .ok (((),v),b)) : Retains w v := by
  cases kp with
  | none =>
    simp [keypairPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact Retains.refl w
  | some id =>
    cases device : w.dev with
    | none =>
      simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.keypairs[id]? with
      | none =>
        simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,resident,
          invariant,AmbientM.invariant] at run
        cases run
      | some k =>
        exact (put_effect id now w v a b d k device resident run).retains
          (by simp [keyAt,device,resident])

theorem put_preserves (kp : Option KeypairId) (now : Bool) (initial : WGWorld) :
    Preserves (Retains initial) (keypairPut kp now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  exact hi.trans (put_retains kp now w v a b run)

theorem put_nonce_projection (kp : Option KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient)
    (run : ((keypairPut kp now).run w).run a = .ok (((),v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ id k, keyAt v id = some k → ∃ old, keyAt w id = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter := by
  have kept := put_retains kp now w v a b run
  refine ⟨kept.counter,?_⟩
  intro id k found
  obtain ⟨old,ho,eq⟩ := kept.keys id k found
  exact ⟨old,ho,by simpa only [keyCore] using congrArg Keypair.internalId eq,
    by simpa only [keyCore] using congrArg Keypair.sendingCounter eq⟩

theorem put_peers (kp : Option KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient)
    (run : ((keypairPut kp now).run w).run a = .ok (((),v),b)) :
    peersAt v = peersAt w := by
  cases kp with
  | none =>
    simp [keypairPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    rfl
  | some id =>
    cases device : w.dev with
    | none =>
      simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.keypairs[id]? with
      | none =>
        simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,resident,
          invariant,AmbientM.invariant] at run
        cases run
      | some k => exact (put_effect id now w v a b d k device resident run).peers

theorem getPeer_preserves (pid : PeerId) (P : WGWorld → Prop) : Preserves P (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (Peers.getPeer_current pid w v p a b run).1 ▸ hi

theorem setPeer_preserves (pid : PeerId) (p : Peer) (initial : WGWorld) :
    Preserves (Retains initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases run
  apply hi.trans
  refine ⟨rfl,?_⟩
  intro id k found
  exact ⟨k,by simpa only [keyAt,Option.bind_map,Function.comp_def] using found,rfl⟩

theorem clear_preserves (pid : PeerId) (initial : WGWorld) :
    Preserves (Retains initial) (keypairsClear pid) := by
  have update (f : Peer → Peer) : Preserves (Retains initial)
      (do let p ← getPeer pid; setPeer pid (f p)) :=
    preserves_bind (getPeer_preserves pid _) (fun p => setPeer_preserves pid (f p) initial)
  unfold keypairsClear
  apply preserves_bind (getPeer_preserves pid _)
  intro p
  apply preserves_bind (update (fun p => {p with keypairNext := none}))
  intro _
  apply preserves_bind (put_preserves p.keypairNext true initial)
  intro _
  apply preserves_bind (getPeer_preserves pid _)
  intro p
  apply preserves_bind (update (fun p => {p with keypairPrevious := none}))
  intro _
  apply preserves_bind (put_preserves p.keypairPrevious true initial)
  intro _
  apply preserves_bind (getPeer_preserves pid _)
  intro p
  apply preserves_bind (update (fun p => {p with keypairCurrent := none}))
  intro _
  exact put_preserves p.keypairCurrent true initial

theorem clear_retains (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((keypairsClear pid).run w).run a = .ok (((),v),b)) : Retains w v :=
  (hoare_iff_run_ambient _ _ _).mp (clear_preserves pid w) w a () v b (Retains.refl w) run

end Leanux.Proofs.WG.RetirementSecurity
