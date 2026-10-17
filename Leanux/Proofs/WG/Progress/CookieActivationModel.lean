import Leanux.Proofs.WG.Progress.CookieActivationCompositionModel

/-! Physical-consumption composition support. The former
`cookieActivationSnapshot_drained` is retired as refuted, not deleted by types:
`cookieBadTail_count_not_drained` disproves count-based emptiness, and
`cookieInitialized_retains_slot` shows why even a logical drain cannot replace
all physical metadata with an empty-container value (CookieRingFindings). -/
