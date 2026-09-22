"""Content identities and an explicit model-source submission allowlist."""
import hashlib
import json
import re
from pathlib import Path, PurePosixPath


class ContractViolation(ValueError):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def file_manifest(root, paths):
    root = Path(root).resolve()
    result = {}
    for name in sorted(paths):
        path = root / name
        if path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ContractViolation('source symlink or path outside snapshot')
        result[name] = digest(path.read_bytes())
    return result


def allowed(name, policy):
    if type(name) is not str or not re.fullmatch(r'[A-Za-z0-9_./-]+', name):
        return False
    path = PurePosixPath(name)
    if path.is_absolute() or '..' in path.parts or str(path) != name:
        return False
    if any(name == p or p.endswith('/') and name.startswith(p) for p in policy['protected_paths']):
        return False
    return name.endswith('.lean') and any(name == p or p.endswith('/') and name.startswith(p)
                                         for p in policy['implementation_roots'])


def validate_submission(submission, expected, policy):
    if type(submission) is not dict or set(submission) != {'version', 'identities', 'files'}:
        raise ContractViolation('submission fields')
    if type(submission['version']) is not int or submission['version'] != 1:
        raise ContractViolation('submission version')
    for identities in (expected, submission['identities']):
        if type(identities) is not dict or set(identities) != set(policy['required_identity_fields']):
            raise ContractViolation('missing required provenance identities')
        for name, value in identities.items():
            length = 40 if name == 'base_commit' else 64
            if type(value) is not str or not re.fullmatch('[0-9a-f]{' + str(length) + '}', value):
                raise ContractViolation('invalid provenance identity')
    if submission['identities'] != expected:
        raise ContractViolation('provenance or dependency mismatch')
    files = submission['files']
    if type(files) is not dict or not files or len(files) > 100:
        raise ContractViolation('empty or oversized submission')
    size = 0
    for name, content in files.items():
        if not allowed(name, policy):
            raise ContractViolation(f'protected or undeclared path: {name}')
        if type(content) is not str:
            raise ContractViolation('source must be text')
        try:
            size += len(content.encode('utf-8', errors='strict'))
        except UnicodeError as exc:
            raise ContractViolation('source must be valid UTF-8') from exc
    if size > 2 * 1024**2:
        raise ContractViolation('submission byte limit')
    return submission


def verify_manifest(root, expected):
    observed = file_manifest(root, expected)
    if observed != expected:
        changed = sorted(name for name in expected if observed[name] != expected[name])
        raise ContractViolation('provenance or dependency mismatch: ' + ', '.join(changed))
    return digest(canonical(observed))
