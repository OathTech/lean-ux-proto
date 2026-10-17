import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.WGOwned
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Receive

/-! Canonical original cookie frames. The projection omits only the device
cookie secret/birthdate and both ratelimiter tables. It retains device presence,
complete resident stores, every allocation frontier, and all eleven WG-owned
observations outside that mask. Source inspection establishes that these four helpers do
not dereference resident peers, keypairs or packets. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def cookieDevice (d : Device) : Device :=
  {d with cookieSecret := [], cookieSecretBirthdate := 0}

def cookieView (g : WGWorld) : WGOwnedView :=
  {wgOwnedView g with
    dev := g.dev.map cookieDevice
    ratelimiter := {g.ratelimiter with table := [], table6 := []}}

abbrev SameCookie (a : WG.M α) := SameView cookieView a

theorem modifyDev_cookie_spec (P : WGOwnedView → Prop) (f : Device → Device)
    (hf : ∀ d, cookieDevice (f d) = cookieDevice d) :
    ⦃fun w => ⌜P (cookieView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (cookieView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [cookieView, wgOwnedView, wgStoreView, modifyDev,
    Option.map_map, Function.comp_def, hf] using hp

theorem makeCookie_sameCookie (src : SkbSource) : SameCookie (makeCookie src) := by
  have ambient {α : Type} (a : AmbientM α) : SameCookie (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => cookieView w = initial)
  have read : SameCookie getDev := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · cases hr
      rfl
  have edit (f : Device → Device) (hf : ∀ d, cookieDevice (f d) = cookieDevice d) :
      SameCookie (modifyDev f) :=
    fun initial => modifyDev_cookie_spec (fun s => s = initial) f hf
  have tail : SameCookie (do
      let secret := (← getDev).cookieSecret
      let addr ← do
        if ← branch .cookieProtoIp (src.family == 4) then pure (netBytes src.saddr 4)
        else if ← branch .cookieProtoIpv6 (src.family == 6) then pure (netBytes src.saddr 16)
        else pure []
      return blake2s 16 secret (addr ++ netBytes src.sport 2) : WG.M (List UInt8)) := by
    apply SameView.bind read
    intro d
    apply SameView.bind (ambient (AmbientM.branch _ _))
    intro ip
    split
    · exact SameView.pure _ _
    · apply SameView.bind (ambient (AmbientM.branch _ _))
      intro ip6
      split <;> exact SameView.pure _ _
  unfold makeCookie
  apply SameView.bind read
  intro d
  apply SameView.bind ((branchExpired_sameWGWorld _ _ _).factor cookieView)
  intro expired
  split
  · apply SameView.bind (ambient (AmbientM.hiddenClock64 .cookieSecretRotateNow))
    intro birthday
    apply SameView.bind (ambient (AmbientM.hidden .cookieSecretRotated))
    intro secret
    exact SameView.bind (edit _ (fun _ => rfl)) (fun _ => tail)
  · exact tail

theorem ratelimiterAllow_sameCookie (src : SkbSource) : SameCookie (ratelimiterAllow src) := by
  have ambient {α : Type} (a : AmbientM α) : SameCookie (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => cookieView w = initial)
  have read : SameCookie (get : WG.M WGWorld) :=
    fun initial => hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have edit (f : WGWorld → WGWorld) (hf : ∀ g, cookieView (f g) = cookieView g) :
      SameCookie (modify f) := by
    intro initial
    apply hoare_modify
    intro g h
    simpa only [hf] using h
  have tail (v6 : Bool) (ip : Nat) : SameCookie (do
      let table (k : WGWorld) : List (Nat × Int × Int) := if v6 then k.ratelimiter.table6 else k.ratelimiter.table
      let setTable (k : WGWorld) (t : List (Nat × Int × Int)) : WGWorld :=
        if v6 then { k with ratelimiter := { k.ratelimiter with table6 := t } }
        else { k with ratelimiter := { k.ratelimiter with table := t } }
      match (table (← get)).find? (·.1 == ip) with
      | some (_, tokens, lastTime) =>
        _ ← branch .rlEntryMatch true
        let now ← hiddenClock .ratelimiterNow
        let newTokens := min TOKEN_MAX (tokens + now - lastTime)
        let ret ← branchCmp .rlAllow (newTokens ≥ PACKET_COST) newTokens PACKET_COST
        let tokens' := if ret then newTokens - PACKET_COST else newTokens
        modify fun k => setTable k ((table k).map fun e => if e.1 == ip then (ip, tokens', now) else e)
        return ret
      | none =>
        -- `atomic_inc_return(&total_entries) > max_entries` (:135): one counter
        -- over both tables
        let k ← get
        let total := k.ratelimiter.table.length + k.ratelimiter.table6.length + 1
        if ← branchCmp .rlOverLimit (total > RL_MAX_ENTRIES) (Int.ofNat total) (Int.ofNat RL_MAX_ENTRIES) then
          unsupported "the ratelimiter table limit (16384 distinct source IPs — out of reach)"
        -- `kmem_cache_alloc(entry_cache, GFP_KERNEL)` (:138): an allocation
        -- outcome, kind 305, at this consumer frame (the hook is generic; the site
        -- is `AllocSite.kmemCacheAllocRlEntry`, armed by the ratelimiter traces'
        -- `draw` entries; B4, the receive audit's F13). On NULL, `err_oom`
        -- (:153-155): `atomic_dec(&total_entries)` (the mirror's count is the
        -- tables' size, so nothing to undo) and `return false`, which
        -- wg_cookie_validate_packet turns into VALID_MAC_WITH_COOKIE_BUT_RATELIMITED
        -- (cookie.c:146-148): the packet is dropped. The arm is reached only by
        -- steering, and the kworker class is not steerable (harness/steer.py
        -- ENABLED_CLASSES): declared, never taken on this host.
        if ← branch .rlAllocFail !(← hiddenAlloc .kmemCacheAllocRlEntry) then
          return false
        let now ← hiddenClock .ratelimiterInsertNow
        modify fun k => setTable k ((ip, TOKEN_MAX - PACKET_COST, now) :: table k)
        return true
      : WG.M Bool) := by
    dsimp only
    apply SameView.bind read
    intro g
    split
    · apply SameView.bind (ambient (AmbientM.branch _ _))
      intro _
      apply SameView.bind (ambient (AmbientM.hiddenClock .ratelimiterNow))
      intro now
      apply SameView.bind (ambient (AmbientM.branchCmp _ _ _ _))
      intro ret
      apply SameView.bind (edit _ (by intro g; cases v6 <;> rfl))
      intro _
      exact SameView.pure _ _
    · apply SameView.bind read
      intro current
      apply SameView.bind (ambient (AmbientM.branchCmp _ _ _ _))
      intro over
      have tail : SameCookie (do
          if ← branch .rlAllocFail !(← hiddenAlloc .kmemCacheAllocRlEntry) then return false
          let now ← hiddenClock .ratelimiterInsertNow
          modify fun k => if v6 then
            {k with ratelimiter := {k.ratelimiter with
              table6 := (ip, TOKEN_MAX - PACKET_COST, now) ::
                (if v6 then k.ratelimiter.table6 else k.ratelimiter.table)}}
            else {k with ratelimiter := {k.ratelimiter with
              table := (ip, TOKEN_MAX - PACKET_COST, now) ::
                (if v6 then k.ratelimiter.table6 else k.ratelimiter.table)}}
          return true : WG.M Bool) := by
        apply SameView.bind (ambient (AmbientM.hiddenAlloc .kmemCacheAllocRlEntry))
        intro allocated
        apply SameView.bind (ambient (AmbientM.branch _ _))
        intro failed
        split
        · exact SameView.pure _ _
        · apply SameView.bind (ambient (AmbientM.hiddenClock .ratelimiterInsertNow))
          intro now
          apply SameView.bind (edit _ (by intro g; cases v6 <;> rfl))
          intro _
          exact SameView.pure _ _
      split
      · exact SameView.bind (ambient (AmbientM.unsupported _)) (fun _ => tail)
      · exact tail
  unfold ratelimiterAllow
  apply SameView.bind (ambient (AmbientM.branch _ _))
  intro ip
  split
  · exact tail false src.saddr
  · apply SameView.bind (ambient (AmbientM.branch _ _))
    intro ip6
    split
    · exact tail true (src.saddr / 2 ^ 64)
    · exact ambient (AmbientM.invariant _)

theorem cookieMessageCreate_sameCookie (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    SameCookie (cookieMessageCreate index src mac1) := by
  have ambient {α : Type} (a : AmbientM α) : SameCookie (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => cookieView w = initial)
  have read : SameCookie getDev := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · cases hr
      rfl
  unfold cookieMessageCreate
  apply SameView.bind (ambient (AmbientM.hidden .cookieNonce))
  intro nonce
  apply SameView.bind (makeCookie_sameCookie src)
  intro cookie
  apply SameView.bind read
  intro d
  exact SameView.pure _ _

theorem cookieValidatePacket_sameCookie (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    SameCookie (cookieValidatePacket msg src checkCookie) := by
  have ambient {α : Type} (a : AmbientM α) : SameCookie (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => cookieView w = initial)
  have read : SameCookie getDev := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v ambient' hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · cases hr
      rfl
  unfold cookieValidatePacket
  apply SameView.bind read
  intro d
  dsimp only
  apply SameView.bind (ambient (AmbientM.branch _ _))
  intro invalid
  split
  · exact SameView.pure _ _
  · apply SameView.bind (ambient (AmbientM.branch _ _))
    intro noCheck
    split
    · exact SameView.pure _ _
    · apply SameView.bind (makeCookie_sameCookie src)
      intro cookie
      apply SameView.bind (ambient (AmbientM.branch _ _))
      intro invalidCookie
      split
      · exact SameView.pure _ _
      · apply SameView.bind (ratelimiterAllow_sameCookie src)
        intro allowed
        apply SameView.bind (ambient (AmbientM.branch _ _))
        intro limited
        split <;> exact SameView.pure _ _

end Leanux.Proofs.Framing
