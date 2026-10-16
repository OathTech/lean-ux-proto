#!/usr/bin/env python3
"""The module-by-field access matrix of the mirror's state (the state-split
design, docs/2026-10-15-design-state-split.md, section 1).

Reads `Leanux/Kernel/Defs.lean` (the `World`, `Kernel` and `Task`
structures) and `Leanux/WG/Types.lean` (`Device`, `Peer`), then every mirror
file, and prints for each module group which fields it reads and which it
writes, from the text alone:

- a write is a field named in a `{ x with f := ... }` update (the mirror's
  only way to change state: `modify`, `modifyK`, `modifyDev`, `modifyPeer`,
  `modifyTask`, `set` all take such a function), attributed to the structure
  whose field set holds `f`;
- a read is a `.f` projection whose `f` is a field of one of the structures,
  attributed the same way.

A name held by two structures is attributed to both and listed as ambiguous
at the end. Fields the mirror never touches (runner-only) show as untouched.
Syntactic, read-only, no build:

    python3 scripts/probes/state-split-access.py [--matrix] [--json]
"""
import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

GROUPS = {
    'WG': ['Leanux/WG'],
    'FS': ['Leanux/FS'],
    'Seccomp': ['Leanux/Seccomp'],
    'Kernel': ['Leanux/Kernel'],
    'Env': ['Leanux/Env.lean', 'Leanux/Env'],
    'Runner': ['Leanux/Runner.lean', 'Leanux/Syscalls.lean', 'Leanux/Main.lean'],
}

STRUCTS = {
    'World': ('Leanux/Kernel/Defs.lean', 'World'),
    'Kernel': ('Leanux/Kernel/Defs.lean', 'Kernel'),
    'Task': ('Leanux/Kernel/Defs.lean', 'Task'),
    'Device': ('Leanux/WG/Types.lean', 'Device'),
    'Peer': ('Leanux/WG/Types.lean', 'Peer'),
}


def fields_of(path, name):
    text = (ROOT / path).read_text()
    m = re.search(rf'^structure {name} where\n(.*?)^(?:  deriving|\S)', text, re.S | re.M)
    if not m:
        raise SystemExit(f'{name} not found in {path}')
    out = []
    for line in m.group(1).splitlines():
        f = re.match(r'  ([a-zA-Z_][A-Za-z0-9_]*)\s*:', line)
        if f:
            out.append(f.group(1))
    return out


def lean_files(prefixes):
    for p in prefixes:
        q = ROOT / p
        if q.is_file():
            yield q
        elif q.is_dir():
            for f in sorted(q.rglob('*.lean')):
                yield f


def strip_comments(text):
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
    return re.sub(r'--[^\n]*', ' ', text)


WITH_RE = re.compile(r'\bwith\b')


def with_fields(text):
    """Field names updated in every `{ x with f := ..., g := ... }` block."""
    out = []
    for m in WITH_RE.finditer(text):
        i = m.end()
        depth = 0
        j = i
        while j < len(text):
            c = text[j]
            if c in '({[':
                depth += 1
            elif c in ')}]':
                if depth == 0:
                    break
                depth -= 1
            j += 1
        block = text[i:j]
        # fields at depth 0 of the block: `name := e`, and the shorthand
        # `name` alone (`{ d with mtu, ifindex }` updates both fields)
        depth = 0
        k = 0
        while k < len(block):
            c = block[k]
            if c in '({[':
                depth += 1
            elif c in ')}]':
                depth -= 1
            elif depth == 0 and (k == 0 or block[k - 1] in ' ,\n'):
                f = re.match(r'\s*([a-zA-Z_][A-Za-z0-9_]*)\s*(:=|,|$)', block[k:])
                if f:
                    out.append(f.group(1))
                    k += f.end() - 1
            k += 1
    return out


# The within-WireGuard field groups (design note section 4): a function's
# footprint is the set of groups its own accesses and its callees' touch.
WG_GROUPS = {
    'config': ['ifindex', 'ifname', 'running', 'sock4', 'sock6', 'creatingNet', 'carrier', 'mtu', 'inet4Dev',
               'inet6Dev', 'incomingPort', 'fwmark', 'deviceUpdateGen', 'staticIdentity', 'numPeers',
               'wg', 'nlSock7', 'nlSock8', 'netIfindexNext', 'pubkeyHashKey'],
    'peers': ['peers', 'peerList', 'peerHashtable', 'nextPeer', 'peerCounter', 'remoteStatic', 'presharedKey',
              'precomputedStaticStatic', 'isDead', 'refcount', 'internalId', 'persistentKeepaliveInterval',
              'endpoint', 'dstCache', 'walltimeLastHandshake'],
    'allowedips': ['peerAllowedips', 'nodes', 'nextNode', 'allowedipsList'],
    'keys': ['keypairs', 'nextKeypairId', 'keypairCounter', 'indexTable', 'keypairCurrent', 'keypairPrevious',
             'keypairNext', 'handshakeState', 'remoteIndex', 'handshakeEntryPeer', 'ephemeralPrivate',
             'remoteEphemeral', 'chainingKey', 'hash', 'latestTimestamp', 'lastSentHandshake',
             'lastInitiationConsumption', 'handshakePending'],
    'queues': ['handshakeQueue', 'handshakeQueueLen', 'handshakeLastCpu', 'sendWorkQueue', 'encryptQueue',
               'txWorkQueue', 'decryptQueue', 'encryptLastCpu', 'decryptLastCpu', 'txSkbs', 'rxSkbs',
               'nextSkb', 'clearWorkQueue', 'staged', 'txQueue', 'rxQueue', 'napiScheduled', 'serialWorkCpu'],
    'timers': ['timerRetransmitHandshake', 'timerSendKeepalive', 'timerNewHandshake', 'timerZeroKeyMaterial',
               'timerPersistentKeepalive', 'timerHandshakeAttempts', 'timerNeedAnotherKeepalive',
               'sentLastminuteHandshake', 'timerUnits', 'jiffiesLast'],
    'cookies': ['cookieSecret', 'cookieSecretBirthdate', 'cookieEncryptionKey', 'mac1Key', 'cookieMac1Key',
                'lastMac1Sent', 'haveSentMac1', 'cookieDecryptionKey', 'cookie', 'cookieBirthdate',
                'cookieIsValid', 'ratelimiter', 'lastUnderLoad'],
    'stats': ['rxPackets', 'rxBytes', 'txPackets', 'txBytes', 'txErrors', 'txDropped', 'rxErrors',
              'rxFrameErrors', 'rxLengthErrors'],
}
AMBIENT = {'hidden', 'steps', 'emitted', 'netRxSection', 'netRxSections', 'netRxRaised', 'queuedThisCall',
           'suspended', 'unitPeers', 'pendingWork', 'sent', 'senderInbox', 'listenerV4', 'listenerV6',
           'armRecords', 'dstCacheRecords', 'fired', 'placeholderCount', 'hiddenPlaceholders', 'steerValues',
           'allocArmed', 'allocSteered', 'envCalls', 'env', 'timing', 'extraOut', 'userOut', 'userFds',
           'translatedLen', 'napiBeforePut', 'napiAmbiguous', 'floodExact', 'foreignCreator', 'netnsCHolders',
           'addrs4', 'addrs6', 'defaultRoute4', 'defaultRoute6', 'defaultRoute4Accessed', 'ipv4Gen',
           'ipv6Gen', 'routesPending', 'routes', 'portBound', 'fixtureNetDevices', 'k'}

METHOD_NAMES = {'insert', 'erase', 'find', 'filter', 'push', 'contains', 'foldl', 'foldr', 'length', 'toList',
                'getD', 'isSome', 'isNone', 'modify', 'pure', 'return', 'take', 'drop', 'head', 'tail', 'append',
                'reverse', 'zip', 'range', 'size', 'empty', 'isEmpty', 'count', 'sum', 'max', 'min', 'toNat',
                'toUInt64', 'toArray', 'join', 'replicate', 'lookup', 'remove', 'update', 'keys', 'values'}


def signature_of(body):
    """The text of a definition up to its first `:=` outside brackets
    (default arguments like `(jc? : Option UInt64 := none)` are inside)."""
    depth = 0
    for i, c in enumerate(body):
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0 and body.startswith(':=', i):
            return body[:i]
    return body


DEF_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*def\s+([A-Za-z_][A-Za-z0-9_.]*)', re.M)
IDENT_RE = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')


def functions_mode():
    """Per WireGuard definition: the field groups it touches itself and
    transitively through the WireGuard functions it calls (a fixpoint over
    the call graph, names matched syntactically; `Env` and `Runner` are not
    walked, so a function that calls into them is marked `env`)."""
    group_of = {}
    for g, fs in WG_GROUPS.items():
        for f in fs:
            group_of[f] = g
    defs = {}      # name -> (file, own groups, called names, ambient, env, monadic)
    files = list(lean_files(['Leanux/WG', 'Leanux/Net', 'Leanux/Kernel/Defs.lean', 'Leanux/Kernel/TimerWheel.lean']))
    for path in files:
        text = strip_comments(path.read_text())
        spans = [(m.start(), m.group(1)) for m in DEF_RE.finditer(text)]
        for i, (start, name) in enumerate(spans):
            end = spans[i + 1][0] if i + 1 < len(spans) else len(text)
            body = text[start:end]
            own = set()
            for f in with_fields(body):
                if f in group_of:
                    own.add(group_of[f])
            for m in re.finditer(r'\.([a-zA-Z_][A-Za-z0-9_]*)\b', body):
                if m.group(1) in group_of:
                    own.add(group_of[m.group(1)])
            amb = {m.group(1) for m in re.finditer(r'\.([a-zA-Z_][A-Za-z0-9_]*)\b', body) if m.group(1) in AMBIENT}
            calls = set(IDENT_RE.findall(body))
            env = bool(re.search(r'\bEnv\.|\bRunner\.', body))
            sig = signature_of(body)
            monadic = bool(re.search(r'\b(M|StateT)\b', sig))
            defs[name.split('.')[-1]] = (str(path.relative_to(ROOT)), own if monadic else set(), calls, amb, env, monadic)
    # call edges only to monadic definitions whose names are not field names
    # or short common words (the match is syntactic)
    names = {n for n, d in defs.items() if d[5] and n not in group_of and len(n) > 3 and n not in METHOD_NAMES}
    foot = {n: set(d[1]) for n, d in defs.items()}
    changed = True
    while changed:
        changed = False
        for n, d in defs.items():
            for c in d[2] & names:
                if c != n and not foot[n] >= foot[c]:
                    foot[n] |= foot[c]
                    changed = True
    hist = defaultdict(int)
    multi = []
    for n, d in defs.items():
        if not d[5] or not d[0].startswith('Leanux/WG'):
            continue
        k = len(foot[n])
        hist[k] += 1
        if k >= 3:
            multi.append((k, n, d[0], sorted(foot[n]), d[4]))
    print('LEXICAL CANDIDATES: footprints from accessor text and name-matched calls, not a sound dependency analysis')
    print(f'definitions walked: {len(defs)} in {len(files)} files (WG, Net, Kernel/Defs, TimerWheel), monadic {sum(1 for d in defs.values() if d[5])}')
    print('transitive footprint size (groups) -> definitions:',
          ', '.join(f'{k}: {hist[k]}' for k in sorted(hist)))
    print(f'definitions calling into Env/Runner: {sum(1 for d in defs.values() if d[4])}')
    if '--leaves' in sys.argv:
        print('definitions touching one or two groups (name, file, groups, own groups):')
        for n, d in sorted(defs.items(), key=lambda x: (len(foot[x[0]]), x[0])):
            if d[5] and d[0].startswith('Leanux/WG') and 1 <= len(foot[n]) <= 2:
                print(f'  {len(foot[n])} {n:36s} {d[0]:30s} {" ".join(sorted(foot[n])):22s} own: {" ".join(sorted(d[1]))}')
        return
    print('definitions touching three or more groups (name, file, groups):')
    for k, n, f, gs, env in sorted(multi, key=lambda x: (-x[0], x[1])):
        print(f'  {k} {n:36s} {f:30s} {" ".join(gs)}{" +env" if env else ""}')


def main():
    if '--functions' in sys.argv:
        functions_mode()
        return
    want_json = '--json' in sys.argv
    fields = {s: fields_of(*spec) for s, spec in STRUCTS.items()}
    owner = defaultdict(list)
    for s, fs in fields.items():
        for f in fs:
            owner[f].append(s)
    ambiguous = sorted(f for f, ss in owner.items() if len(ss) > 1)

    reads = defaultdict(lambda: defaultdict(int))   # (struct, field) -> group -> n
    writes = defaultdict(lambda: defaultdict(int))
    per_file = {}
    for group, prefixes in GROUPS.items():
        for path in lean_files(prefixes):
            text = strip_comments(path.read_text())
            rel = str(path.relative_to(ROOT))
            fw = defaultdict(int)
            fr = defaultdict(int)
            for f in with_fields(text):
                for s in owner.get(f, []):
                    writes[(s, f)][group] += 1
                    fw[(s, f)] += 1
            for m in re.finditer(r'\.([a-zA-Z_][A-Za-z0-9_]*)\b', text):
                f = m.group(1)
                for s in owner.get(f, []):
                    reads[(s, f)][group] += 1
                    fr[(s, f)] += 1
            per_file[rel] = dict(group=group,
                                 writes=sorted({f'{s}.{f}' for (s, f) in fw}),
                                 reads=sorted({f'{s}.{f}' for (s, f) in fr}))

    groups = list(GROUPS)
    if want_json:
        out = dict(fields=fields, ambiguous=ambiguous, per_file=per_file,
                   matrix={f'{s}.{f}': {g: ('w' if writes[(s, f)][g] else '') + ('r' if reads[(s, f)][g] else '')
                                        for g in groups}
                           for s in fields for f in fields[s]})
        print(json.dumps(out, indent=1))
        return

    print('LEXICAL CANDIDATES: writes are `with`-updated field names, reads are `.f` projections; names held by two structures are attributed to both')
    print(f'{"field":34s}' + ''.join(f'{g:>9s}' for g in groups))
    for s in fields:
        print(f'-- {s} ({len(fields[s])} fields)')
        for f in fields[s]:
            cells = []
            for g in groups:
                w = writes[(s, f)][g]
                r = reads[(s, f)][g]
                cells.append(('w' if w else '') + ('r' if r else '') or '.')
            flag = ' *' if f in ambiguous else ''
            print(f'{s + "." + f:34s}' + ''.join(f'{c:>9s}' for c in cells) + flag)
    print()
    print('* a field name held by more than one structure (attributed to each):', ', '.join(ambiguous) or 'none')
    # summary per group
    print()
    for s in fields:
        for g in groups:
            touched = sorted(f for f in fields[s] if writes[(s, f)][g] or reads[(s, f)][g])
            written = sorted(f for f in fields[s] if writes[(s, f)][g])
            if touched:
                print(f'{g:8s} {s:7s} touched {len(touched):3d} written {len(written):3d} of {len(fields[s])}')


if __name__ == '__main__':
    main()
