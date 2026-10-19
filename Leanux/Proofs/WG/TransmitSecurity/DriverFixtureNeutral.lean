import Leanux.Proofs.WG.TransmitSecurity.JournalSource

/-! The shared journal's local-trigger wrappers preserve the existing driver
exactly; causal decoration may specialize the same wrapper separately. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal

theorem fixture_neutral : Driver.fixtureOps hooks = AuthenticatedEffects.FixtureEffects.neutral := rfl

end Leanux.Proofs.WG.TransmitSecurity.Journal
