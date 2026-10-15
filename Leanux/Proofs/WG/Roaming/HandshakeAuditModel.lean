import Leanux.Proofs.WG.Campaign2.View

namespace Leanux.Proofs.WG.Roaming
open Leanux

/-- Exact prefix and complete-call outcomes from one inspected execution. -/
abbrev HandshakeAudit (C : Type) :=
  Campaign2.Outcome (Option C) × Campaign2.Outcome Unit

/-- Prefix errors are the original error; a rejected no-cut prefix completes
without the setter. A present cut retains its facts even if the suffix fails. -/
def HandshakeAuditFacts {C : Type} (facts : C → Campaign2.Snapshot → Prop)
    (audited : HandshakeAudit C) : Prop :=
  match audited.1 with
  | .error err => audited.2 = .error err
  | .ok (none, atCut) => audited.2 = .ok ((), atCut)
  | .ok (some cut, atCut) => facts cut atCut

end Leanux.Proofs.WG.Roaming
