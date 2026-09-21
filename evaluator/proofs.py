"""Check fixed propositions, definition identities, and actual axiom dependencies."""
import json
from pathlib import Path

from .boundary import ROOT, prepare
from .process import run
from .protocol import loads
from .runner import LEAN_ADDRESS_SPACE, save_execution
from .submission import verify_manifest, ContractViolation, digest


def check_proofs(model, out):
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    contract = json.loads((ROOT / 'contracts/proof-identities-v1.json').read_text())
    try:
        verify_manifest(model.source, contract['protected_definitions'])
    except (ContractViolation, OSError) as exc:
        result = dict(status='fail', outcome='proof_contract_mismatch', detail=str(exc))
        (out / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
        return result
    prefix, env = prepare(model.source, model.scratch, out / 'profile.json', [ROOT / 'evaluator/ProofAudit.lean'])
    build = run(prefix + ['lake', '--no-cache', 'build', 'Leanux.Proofs.All'],
                cwd=model.source, env=env, timeout=900, cpu_seconds=900, address_space=LEAN_ADDRESS_SPACE)
    save_execution(out, 'build', build)
    if build.outcome != 'success':
        result = dict(status='fail', outcome='proof_build_failure', execution=build.summary())
    else:
        audit = run(prefix + ['lake', 'env', 'lean', '-j1', '-t0', ROOT / 'evaluator/ProofAudit.lean'],
                    cwd=model.source, env=env, timeout=900, cpu_seconds=900, address_space=LEAN_ADDRESS_SPACE)
        save_execution(out, 'audit', audit)
        records = [loads(line[len('LEANUX_PROOF '):]) for line in audit.stdout.decode(errors='replace').splitlines()
                   if line.startswith('LEANUX_PROOF ')]
        expected = set(contract['expected_theorems'])
        valid = (audit.outcome == 'success' and len(records) == len(expected) and
                 {record['theorem'] for record in records} == expected and
                 all(set(record['axioms']) <= set(contract['permitted_axioms']) for record in records))
        result = dict(status='pass' if valid else 'fail',
                      outcome='checked' if valid else 'proof_dependency_or_type_mismatch',
                      records=records, kernel_trust_level=0,
                      contract_sha256=digest((ROOT / 'contracts/proof-identities-v1.json').read_bytes()),
                      checker_sha256=digest((ROOT / 'evaluator/ProofAudit.lean').read_bytes()))
    (out / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
