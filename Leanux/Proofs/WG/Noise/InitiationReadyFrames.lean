import Leanux.Proofs.WG.Noise.InitiationReadySource

/-! Ambient-metadata preservation remains substantive: these actions can access Ambient. -/
set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem bucketHas_metadata (metadata : Bool → List String → Prop) (walk collide : Decision) (index : Nat)
    (table : List IndexEntry) :
    Product.Ensures ((Index.bucketHas walk collide index).run table)
      (fun ambient => metadata ambient.armRecords ambient.allocArmed)
      (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
  have hwalk (entries table : List IndexEntry) :
      Product.Ensures ((Index.bucketWalk walk collide index entries).run table)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed)
        (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    induction entries with
    | nil =>
      intro ambient result after pre run
      simp [Index.bucketWalk, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    | cons e es ih =>
      intro ambient result after pre run
      rw [Index.bucketWalk_cons] at run
      let next := {ambient with steps := (ambient.steps.push {
        decision := walk, outcome := true, netRx := ambient.netRxSection}).push {
        decision := collide, outcome := e.index == index, netRx := ambient.netRxSection}}
      cases matched : e.index == index with
      | true =>
        simp [branch, AmbientM.branch, matched] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
      | false =>
        have tail : ((Index.bucketWalk walk collide index es).run table).run next =
            .ok (result, after) := by
          simpa [branch, AmbientM.branch, matched, StateT.run_bind, Except.bind, next] using run
        exact ih next result after pre tail
  intro ambient result after pre run
  rw [Index.bucketHas_source] at run
  exact hwalk (Index.bucket index table) table ambient result after pre
    (by simpa [indexBucket, Index.bucket, StateT.run_bind] using run)

theorem hidden_metadata (metadata : Bool → List String → Prop) (site : HiddenSite) :
    Product.Ensures (AmbientM.hidden site)
      (fun ambient => metadata ambient.armRecords ambient.allocArmed)
      (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
  intro ambient result after pre run
  have skip : ∃ next, AmbientM.skipAmbient.run ambient = .ok ((), next) ∧
      metadata next.armRecords next.allocArmed := by
    cases records : ambient.hidden with
    | none => exact ⟨ambient, by simp [AmbientM.skipAmbient, records]; rfl, pre⟩
    | some rs =>
      refine ⟨{ambient with hidden := some (rs.dropWhile fun r => HiddenSite.passive r.site)}, ?_, pre⟩
      simp [AmbientM.skipAmbient, records]
      rfl
  obtain ⟨skipped, hskip, skipMode⟩ := skip
  have note : ∃ next, (AmbientM.noteNetRxStart site.info.id).run skipped = .ok ((), next) ∧
      metadata next.armRecords next.allocArmed := by
    unfold AmbientM.noteNetRxStart
    split <;> exact ⟨_, rfl, skipMode⟩
  obtain ⟨noted, hnote, noteMode⟩ := note
  simp only [AmbientM.hidden, StateT.run_bind, hskip] at run
  dsimp only [Bind.bind, Except.bind, StateT.run] at run
  change AmbientM.noteNetRxStart site.info.id skipped = .ok ((), noted) at hnote
  rw [hnote] at run
  dsimp only [Bind.bind, Except.bind] at run
  split at run
  all_goals
    dsimp only [StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
      StateT.bind, StateT.pure, StateT.get, StateT.set, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, Except.pure, Except.bind] at run
    cases recordState : noted.hidden with
    | none =>
      simp only [recordState] at run
      cases placeholders : noted.hiddenPlaceholders <;>
        simp [placeholders] at run
      all_goals
        repeat' first
          | (solve | cases run; exact noteMode)
          | (solve | contradiction)
          | (split at run)
    | some rs =>
      cases rs with
      | nil =>
        simp only [recordState] at run
        cases run
      | cons record rest =>
        simp only [recordState] at run
        repeat' first
          | (solve | cases run; exact noteMode)
          | (solve | contradiction)
          | split at run


private theorem metadata_bind {σ α β : Type} (metadata : Bool → List String → Prop)
    (action : StateT σ AmbientM α) (next : α → StateT σ AmbientM β)
    (first : ∀ state, Product.Ensures (action.run state)
      (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed))
    (rest : ∀ value state, Product.Ensures ((next value).run state)
      (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed))
    (state : σ) :
    Product.Ensures ((action >>= next).run state)
      (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
  change Product.Ensures (action.run state >>= fun (value, current) => (next value).run current) _ _
  exact Product.ensures_bind _ _ (first state) (fun (value, current) => rest value current)

private theorem metadata_lift {σ α : Type} (metadata : Bool → List String → Prop) (action : AmbientM α)
    (preserves : Product.Ensures action
      (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed))
    (state : σ) :
    Product.Ensures ((StateT.lift action : StateT σ AmbientM α).run state)
      (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
  intro ambient result after pre run
  change (action.run ambient >>= fun (value, current) => .ok ((value, state), current)) =
    .ok (result, after) at run
  cases first : action.run ambient with
  | error err => rw [first] at run; cases run
  | ok pair =>
    obtain ⟨value, current⟩ := pair
    rw [first] at run
    have preserved := preserves ambient value current pre first
    cases run
    exact preserved

theorem indexInsert_metadata (metadata : Bool → List String → Prop) (owner : IndexOwner) (table : List IndexEntry) :
    Product.Ensures ((indexInsert owner).run table)
      (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
  have step (turn : Nat) (state : Index.InsertState) (table : List IndexEntry) :
      Product.Ensures ((Index.insertStep owner turn state).run table)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    unfold Index.insertStep
    apply metadata_bind metadata
    · exact metadata_lift metadata (AmbientM.hidden .indexDraw) (hidden_metadata metadata .indexDraw)
    · intro draw
      apply metadata_bind metadata
      · exact bucketHas_metadata metadata .idxInsWalk1 .idxInsCollide1 _
      · intro first
        cases first with
        | true => intro table ambient result after pre run; cases run; exact pre
        | false =>
          apply metadata_bind metadata
          · exact bucketHas_metadata metadata .idxInsWalk2 .idxInsCollide2 _
          · intro second table ambient result after pre run
            cases second with
            | true =>
              simp [unsupported, AmbientM.unsupported] at run
              cases run
            | false => cases run; exact pre
  have loop (turns : List Nat) (state : Index.InsertState) (table : List IndexEntry) :
      Product.Ensures ((forIn turns state (Index.insertStep owner) : IndexM _).run table)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    induction turns generalizing state table with
    | nil => intro ambient result after pre run; cases run; exact pre
    | cons turn turns ih =>
      intro ambient result after pre run
      simp only [List.forIn_cons, StateT.run_bind] at run
      cases first : ((Index.insertStep owner turn state).run table).run ambient with
      | error err => rw [first] at run; cases run
      | ok pair =>
        obtain ⟨⟨out, middle⟩, current⟩ := pair
        have preserved := step turn state table ambient (out, middle) current pre first
        rw [first] at run
        cases out with
        | done value => cases run; exact preserved
        | yield value => exact ih value middle current result after preserved run
  rw [Index.indexInsert_source]
  apply metadata_bind metadata
  · intro table ambient result after pre run
    simp [Index.unhashEntry] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  · intro _
    apply metadata_bind metadata
    · intro table ambient result after pre run
      simp [recordBudget, AmbientM.recordBudget] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    · intro budget
      apply metadata_bind metadata
      · intro table
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        exact loop _ _ table
      · intro state table ambient result after pre run
        cases value : state.1 with
        | some index =>
          simp [Index.insertFinish, value] at run
          rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
          exact pre
        | none =>
          simp [Index.insertFinish, value, budgetExhausted, AmbientM.budgetExhausted,
            AmbientM.invariant, AmbientM.unsupported] at run
          split at run <;> cases run


theorem createInitiation_metadata (metadata : Bool → List String → Prop) (pid : PeerId) (state : WGWorld) :
    Product.Ensures ((createInitiation pid).run state)
      (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
  have hpure {α : Type} (value : α) (g : WGWorld) :
      Product.Ensures ((pure value : WG.M α).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after pre run
    cases run
    exact pre
  have hbranch (site : Decision) (value : Bool) (g : WGWorld) :
      Product.Ensures ((branch site value : WG.M Bool).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    exact metadata_lift metadata (AmbientM.branch site value) (by
      intro ambient result after pre run
      cases run
      exact pre) g
  have hhidden (site : HiddenSite) (g : WGWorld) :
      Product.Ensures ((hidden site : WG.M (List UInt8)).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) :=
    metadata_lift metadata (AmbientM.hidden site) (hidden_metadata metadata site) g
  have hinvariant {α : Type} (message : String) (g : WGWorld) :
      Product.Ensures ((invariant message : WG.M α).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after _ run
    cases run
  have hunsupported {α : Type} (message : String) (g : WGWorld) :
      Product.Ensures ((unsupported message : WG.M α).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after _ run
    cases run
  have hdev (g : WGWorld) :
      Product.Ensures (getDev.run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after pre run
    cases device : g.dev with
    | none =>
      simp [getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hpeer (id : PeerId) (g : WGWorld) :
      Product.Ensures ((getPeer id).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    unfold getPeer
    apply metadata_bind metadata
    · exact hdev
    · intro d
      cases found : d.peers.get? id with
      | none => simpa only [found] using hinvariant (toString "dangling peer " ++ toString id)
      | some p => simpa only [found] using hpure p
  have hset (id : PeerId) (p : Peer) (g : WGWorld) :
      Product.Ensures ((setPeer id p).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after pre run
    cases run
    exact pre
  have hpublic (secret : Key) (g : WGWorld) :
      Product.Ensures ((generatePublic secret).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after pre run
    simp [generatePublic, branch, AmbientM.branch] at run
    split at run <;> cases run <;> exact pre

  have hk (second third : Bool) (ck data : List UInt8) (g : WGWorld) :
      Product.Ensures ((kdf second third ck data).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after pre run
    cases second <;> cases third <;>
      simp [kdf, WG.orM, branch, AmbientM.branch, StateT.run] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact pre
  have ho (outs : List (List UInt8)) (i : Nat) (g : WGWorld) :
      Product.Ensures ((kdfOut outs i).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after pre run
    cases found : outs[i]? with
    | none =>
      simp [kdfOut, found, invariant, AmbientM.invariant, StateT.run] at run
      cases run
    | some o =>
      simp [kdfOut, found, StateT.run] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have he (copy : Bool) (e ck hash : List UInt8) (g : WGWorld) :
      Product.Ensures ((messageEphemeral copy e ck hash).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    unfold messageEphemeral
    apply metadata_bind metadata
    · exact hbranch _ _
    · intro _
      apply metadata_bind metadata
      · exact hk _ _ _ _
      · intro outs
        apply metadata_bind metadata
        · exact ho _ _
        · intro value; exact hpure _
  have hd (key : Bool) (ck priv pub : List UInt8) (g : WGWorld) :
      Product.Ensures ((mixDh key ck priv pub).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    dsimp only [mixDh]
    apply metadata_bind metadata
    · exact hbranch _ _
    · intro null
      cases null with
      | true => exact hpure _
      | false =>
        apply metadata_bind metadata
        · exact hk _ _ _ _
        · intro outs
          apply metadata_bind metadata
          · exact ho _ _
          · intro first
            cases key with
            | false => exact hpure _
            | true =>
              apply metadata_bind metadata
              · exact ho _ _
              · intro second; exact hpure _
  have hs (ck precomputed : List UInt8) (g : WGWorld) :
      Product.Ensures ((mixPrecomputedDh ck precomputed).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    unfold mixPrecomputedDh
    apply metadata_bind metadata
    · exact hbranch _ _
    · intro null
      cases null with
      | true => exact hpure _
      | false =>
        apply metadata_bind metadata
        · exact hk _ _ _ _
        · intro outs
          apply metadata_bind metadata
          · exact ho _ _
          · intro first
            apply metadata_bind metadata
            · exact ho _ _
            · intro second; exact hpure _
  have hi (owner : IndexOwner) (g : WGWorld) :
      Product.Ensures ((liftIndex (indexInsert owner)).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    intro ambient result after pre run
    rw [liftIndex_run_variant] at run
    cases device : g.dev with
    | none => simp [device] at run
    | some d =>
      simp only [device] at run
      cases inserted : ((indexInsert owner).run d.indexTable).run ambient with
      | error err => simp [inserted, Except.map] at run
      | ok pair =>
        obtain ⟨⟨value, table⟩, next⟩ := pair
        have preserved := indexInsert_metadata metadata owner d.indexTable ambient (value, table) next pre inserted
        simp [inserted, Except.map] at run
        rcases run with ⟨rfl, rfl⟩
        exact preserved

  have hchain (ck hash : List UInt8) (g : WGWorld) :
      Product.Ensures ((setChain pid ck hash).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    change Product.Ensures ((getPeer pid >>= fun p => setPeer pid {p with chainingKey := ck, hash := hash}).run g) _ _
    apply metadata_bind metadata
    · exact hpeer _
    · intro p; exact hset _ _
  have hderef (g : WGWorld) :
      Product.Ensures ((IndexOwner.peerDeref (.handshake pid)).run g)
        (fun ambient => metadata ambient.armRecords ambient.allocArmed) (fun _ ambient => metadata ambient.armRecords ambient.allocArmed) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    apply metadata_bind metadata
    · intro g
      apply metadata_bind metadata
      · exact hpeer _
      · intro p; exact hpure _
    · intro word
      cases word with
      | none => exact hunsupported _
      | some value => exact hpure _
  unfold createInitiation
  apply metadata_bind metadata
  · exact hdev
  · intro device
    apply metadata_bind metadata
    · exact hbranch _ _
    · intro noIdentity
      cases noIdentity with
      | true => exact hpure _
      | false =>
        apply metadata_bind metadata
        · exact hpeer _
        · intro p
          apply metadata_bind metadata
          · exact hchain _ _
          · intro _
            apply metadata_bind metadata
            · exact hhidden _
            · intro random
              apply metadata_bind metadata
              · exact hpeer _
              · intro p
                apply metadata_bind metadata
                · exact hset _ _
                · intro _
                  apply metadata_bind metadata
                  · exact hpublic _
                  · intro generated
                    obtain ⟨publicKey, publicOk⟩ := generated
                    apply metadata_bind metadata
                    · exact hbranch _ _
                    · intro noEphemeral
                      cases noEphemeral with
                      | true => exact hpure _
                      | false =>
                        cases publicKey with
                        | none => simpa using hinvariant (α := Option (List UInt8)) "unreachable"
                        | some e =>
                          apply metadata_bind metadata
                          · exact he _ _ _ _
                          · intro pair
                            obtain ⟨ephemeralChain, ephemeralHash⟩ := pair
                            apply metadata_bind metadata
                            · exact hchain _ _
                            · intro _
                              apply metadata_bind metadata
                              · exact hd _ _ _ _
                              · intro es
                                apply metadata_bind metadata
                                · exact hbranch _ _
                                · intro esFailed
                                  cases esFailed with
                                  | true => exact hpure _
                                  | false =>
                                    cases es with
                                    | none => exact hinvariant _
                                    | some pair =>
                                      obtain ⟨ck, key⟩ := pair
                                      apply metadata_bind metadata
                                      · exact hchain _ _
                                      · intro _
                                        apply metadata_bind metadata
                                        · exact hs _ _
                                        · intro ss
                                          apply metadata_bind metadata
                                          · exact hbranch _ _
                                          · intro ssFailed
                                            cases ssFailed with
                                            | true => exact hpure _
                                            | false =>
                                              cases ss with
                                              | none => exact hinvariant _
                                              | some pair =>
                                                obtain ⟨ck, key⟩ := pair
                                                apply metadata_bind metadata
                                                · exact hhidden _
                                                · intro clock
                                                  apply metadata_bind metadata
                                                  · exact hchain _ _
                                                  · intro _
                                                    apply metadata_bind metadata
                                                    · exact hderef
                                                    · intro _
                                                      apply metadata_bind metadata
                                                      · exact hi _
                                                      · intro index
                                                        apply metadata_bind metadata
                                                        · exact hpeer _
                                                        · intro p
                                                          apply metadata_bind metadata
                                                          · exact hset _ _
                                                          · intro _; exact hpure _


theorem bucketHas_mode (mode : Bool) (walk collide : Decision) (index : Nat)
    (table : List IndexEntry) :
    Product.Ensures ((Index.bucketHas walk collide index).run table)
      (fun ambient => ambient.armRecords = mode)
      (fun _ ambient => ambient.armRecords = mode) :=
  bucketHas_metadata (fun recorded _ => recorded = mode) walk collide index table

theorem hidden_mode (mode : Bool) (site : HiddenSite) :
    Product.Ensures (AmbientM.hidden site)
      (fun ambient => ambient.armRecords = mode)
      (fun _ ambient => ambient.armRecords = mode) :=
  hidden_metadata (fun recorded _ => recorded = mode) site

theorem indexInsert_mode (mode : Bool) (owner : IndexOwner) (table : List IndexEntry) :
    Product.Ensures ((indexInsert owner).run table)
      (fun ambient => ambient.armRecords = mode) (fun _ ambient => ambient.armRecords = mode) :=
  indexInsert_metadata (fun recorded _ => recorded = mode) owner table

theorem createInitiation_mode (mode : Bool) (pid : PeerId) (state : WGWorld) :
    Product.Ensures ((createInitiation pid).run state)
      (fun ambient => ambient.armRecords = mode) (fun _ ambient => ambient.armRecords = mode) :=
  createInitiation_metadata (fun recorded _ => recorded = mode) pid state

end Leanux.Proofs.WG.Noise.InitiationReady
