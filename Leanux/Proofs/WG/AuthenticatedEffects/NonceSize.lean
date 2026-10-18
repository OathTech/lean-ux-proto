import Leanux.Proofs.WG.AuthenticatedEffects.CookieSize

/-! The actual hidden cookie nonce accepts exactly 24 bytes, including the
placeholder and steered domain-filter paths. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

private theorem anyAmbient (action : AmbientM α) : Hoare action (fun _ => True) (fun _ _ => True) := by
  apply (hoare_iff_run _ _ _).mpr
  intros
  trivial

private theorem pure_length (bytes : List UInt8) (length : bytes.length = 24) :
    Hoare (pure bytes : AmbientM (List UInt8)) (fun _ => True) (fun out _ => out.length = 24) := by
  apply hoare_consequence (hoare_pure bytes (fun _ => True)) (fun _ _ => trivial)
  intro out w h
  rcases h with ⟨rfl,_⟩
  exact length

theorem hidden_cookie_nonce_spec : Hoare (AmbientM.hidden .cookieNonce)
    (fun _ => True) (fun bytes _ => bytes.length = 24) := by
  have notJitter : (HiddenSite.cookieNonce == HiddenSite.retransmitJitter) = false := rfl
  unfold AmbientM.hidden
  apply hoare_bind _ _ (anyAmbient _)
  intro skipped
  apply hoare_bind _ _ (anyAmbient _)
  intro noted
  apply hoare_bind _ _ (anyAmbient _)
  intro w
  cases hs : w.hidden with
  | none =>
    dsimp only
    split
    · exact hoare_throw _
    · apply hoare_bind _ _ (anyAmbient _)
      intro setDone
      split
      · apply hoare_bind _ _ (anyAmbient _)
        intro erased
        split
        · split
          · exact hoare_throw _
          · apply pure_length
            rename_i width
            simpa [HiddenSite.info] using width
        · apply pure_length
          simp [HiddenSite.info,notJitter]
      · apply pure_length
        simp [HiddenSite.info,notJitter]
  | some records =>
    cases records with
    | nil => exact hoare_throw _
    | cons r rest =>
      dsimp only
      split
      · exact hoare_throw _
      · split
        · exact hoare_throw _
        · apply hoare_bind _ _ (anyAmbient _)
          intro setDone
          apply pure_length
          rename_i guard
          simp [HiddenSite.info] at guard ⊢
          omega

theorem hidden_cookie_nonce_length (w v : WGWorld) (a b : Ambient) (bytes : List UInt8)
    (run : (((hidden .cookieNonce : WG.M (List UInt8)).run w).run a) = .ok ((bytes,v),b)) :
    bytes.length = 24 := by
  change ((AmbientM.hidden .cookieNonce).run a).map (fun out => ((out.1,w),out.2)) = _ at run
  cases native : (AmbientM.hidden .cookieNonce).run a with
  | error err => simp [native,Except.map] at run
  | ok out =>
    rcases out with ⟨bs,c⟩
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact (hoare_iff_run _ _ _).mp hidden_cookie_nonce_spec a bs c trivial native

theorem cookieMessageCreate_length (index : Nat) (src : SkbSource) (mac1 : List UInt8)
    (w v : WGWorld) (a b : Ambient) (bytes : List UInt8)
    (run : ((cookieMessageCreate index src mac1).run w).run a = .ok ((bytes,v),b)) :
    bytes.length = 64 := by
  unfold cookieMessageCreate at run
  rw [native_bind_run] at run
  cases nonceRun : (((hidden .cookieNonce : WG.M (List UInt8)).run w).run a) with
  | error err => simp [nonceRun] at run
  | ok out =>
    rcases out with ⟨⟨nonce,u⟩,c⟩
    rw [nonceRun] at run
    dsimp only at run
    rw [native_bind_run] at run
    have nonceLength := hidden_cookie_nonce_length w u a c nonce nonceRun
    cases cookieRun : ((makeCookie src).run u).run c with
    | error err => simp [cookieRun] at run
    | ok out =>
      rcases out with ⟨⟨cookie,z⟩,d⟩
      rw [cookieRun] at run
      dsimp only at run
      rw [native_bind_run] at run
      have cookieLength := makeCookie_length src u z c d cookie cookieRun
      cases devRun : (getDev.run z).run d with
      | error err => simp [devRun] at run
      | ok out =>
        rcases out with ⟨⟨dev,q⟩,f⟩
        rw [devRun] at run
        cases run
        simp [le32,nonceLength,xchacha_sixteen_length _ _ _ _ cookieLength]

end Leanux.Proofs.WG.AuthenticatedEffects
