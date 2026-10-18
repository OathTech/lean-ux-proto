import Leanux.Proofs.WG.Noise.Statements
import Leanux.Proofs.WG.Index.Statements
import Leanux.Proofs.WG.Roaming.Statements
import Leanux.Proofs.WG.Config.Statements
import Leanux.Proofs.WG.Progress.Statements
import Leanux.Proofs.WG.TimerDiscipline.Statements
import Leanux.Proofs.WG.ReplayWindow.Statements
import Leanux.Proofs.WG.ReplayWindow.Counterexamples
import Leanux.Proofs.WG.Queues.RxCleanupFindings
import Leanux.Proofs.WG.AntiReplay.Statements
import Leanux.Proofs.WG.LifetimeSafety.Statements
import Leanux.Proofs.WG.CryptokeyRouting.Statements
import Leanux.Proofs.WG.DeliveryOrder.Statements
import Leanux.Proofs.WG.KeyLifetime.Statements
import Leanux.Proofs.WG.FloodResistance.Statements

/-! The proof tree's root: the terminal statements of every result, one import
per result directory, and the checked counterexamples. `lake build LeanuxProofs`
builds exactly this closure; `scripts/proof-gate` prints the axioms of every
declaration of every `Statements.lean` below. The map of the tree and the
results it holds is `docs/proofs.md`. -/
