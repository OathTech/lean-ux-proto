import Leanux.Proofs.WG.Progress.SeccompPrefillFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompPrefillFinite
open Leanux Leanux.Seccomp

/-- The original closed translation has exactly the finite creator's result,
including both error forms. No successful translation premise is required. -/
theorem original_translation_finite : Prefill.translated = translated :=
  translated_source

/-- The complete prefill initializer agrees on every input with finite
translation and bounded cache/copy evaluation. Its initial count refusal,
filter insertion order, task update and every error remain exact. -/
theorem original_install_finite : Prefill.apply = install := install_source

end Leanux.Proofs.WG.Progress.SeccompPrefillFinite
