"""Stable device components of R, with offsets and widths read from DWARF."""


def generate_device_scalars(root, layouts):
    device = layouts['wg_device']
    records = [
        ('wg_device', 0, [
            ('handshakeQueueLen', 'handshake_queue_len', 'nat', 4),
            ('numPeers', 'num_peers', 'nat', 4),
            ('deviceUpdateGen', 'device_update_gen', 'nat', 4),
            ('fwmark', 'fwmark', 'nat', 4),
            ('incomingPort', 'incoming_port', 'nat', 2),
        ]),
        ('noise_static_identity', device['members']['static_identity'], [
            ('staticIdentity.staticPublic', 'static_public', 'bytes', 32),
            ('staticIdentity.staticPrivate', 'static_private', 'bytes', 32),
            ('staticIdentity.hasIdentity', 'has_identity', 'bool', 1),
        ]),
        ('cookie_checker', device['members']['cookie_checker'], [
            ('cookieEncryptionKey', 'cookie_encryption_key', 'bytes', 32),
            ('mac1Key', 'message_mac1_key', 'bytes', 32),
        ]),
    ] + [('crypt_queue', device['members'][queue + '_queue'], [
        (queue + 'LastCpu', 'last_cpu', 'signed', 4)
    ]) for queue in ['encrypt', 'decrypt', 'handshake']]
    fields = []
    for record, base, rows in records:
        for mirror, member, kind, width in rows:
            actual = layouts[record]['member_sizes'][member]
            if actual != width:
                raise ValueError(f'{record}.{member}: DWARF width {actual}, expected {width}')
            offset = base + layouts[record]['members'][member]
            if offset + width > device['size']:
                raise ValueError(f'{record}.{member}: outside owning device')
            fields.append((mirror, mirror.replace('.', '_'), offset, width, kind))
    text = ['import Layouts', 'import Memory', 'set_option maxRecDepth 4096', 'namespace Binary',
            '-- Generated from the pinned image by binary/device_layouts.py.',
            '/-- Stable device words and exact non-placeholder keys. Pointer, ring,',
            '    netdevice and ownership components remain separate. Signed CPU',
            '    words use two\'s-complement decoding, never unbounded modular equality. -/',
            'structure DeviceStableFields (m : Mem 64) (a : BitVec 64)',
            '    (d : Leanux.WG.Device) : Prop where']
    for mirror, name, offset, width, kind in fields:
        addr = f'(a + .ofNat 64 {offset})'
        if kind == 'bytes':
            eq = f'm.loadBytes {addr} {width} = some d.{mirror}'
        elif kind == 'signed':
            eq = f'∃ raw : BitVec 32, m.loadInt {addr} 4 = some (raw.toNat : Int) ∧ raw.toInt = d.{mirror}'
        else:
            value = f'(d.{mirror} : Int)' if kind == 'nat' else f'(if d.{mirror} then 1 else 0)'
            eq = f'm.loadInt {addr} {width} = some {value}'
        text.append(f'  {name} : {eq}')
    text += ['', 'def deviceStableOffsets : List (Nat × Nat) :=',
             '  [' + ', '.join(f'({o}, {w})' for _, _, o, w, _ in fields) + ']', '',
             'def deviceStableLocations (a : BitVec 64) : List (BitVec 64 × Nat) :=',
             '  deviceStableOffsets.map (fun cell => (a + .ofNat 64 cell.1, cell.2))', '']
    for read in ['loadInt', 'loadBytes']:
        text += [f'private theorem device_{read} {{before after : Mem 64}} {{writes : BitVec 64 → Prop}}',
                 '    (a : BitVec 64) (same : EqualOutside writes before after)',
                 '    (apart : ∀ location ∈ deviceStableLocations a, ∀ i < location.2,',
                 '      ¬writes (location.1 + .ofNat 64 i))',
                 '    (off size : Nat) (member : (off, size) ∈ deviceStableOffsets) :',
                 f'    before.{read} (a + .ofNat 64 off) size = after.{read} (a + .ofNat 64 off) size := by',
                 f'  apply EqualOutside.{read} same',
                 '  exact apart _ (List.mem_map_of_mem (f := fun cell : Nat × Nat =>',
                 '    (a + .ofNat 64 cell.1, cell.2)) member)', '']
    text += [
             'theorem DeviceStableFields.frame {before after : Mem 64} {writes : BitVec 64 → Prop}',
             '    {a : BitVec 64} {d : Leanux.WG.Device}',
             '    (same : EqualOutside writes before after)',
             '    (apart : ∀ location ∈ deviceStableLocations a, ∀ i < location.2,',
             '      ¬writes (location.1 + .ofNat 64 i))',
             '    (h : DeviceStableFields before a d) : DeviceStableFields after a d := by',
             '  refine {' + ', '.join(n + ' := ?_' for _, n, _, _, _ in fields) + '}']
    for _, name, offset, width, kind in fields:
        read = 'loadBytes' if kind == 'bytes' else 'loadInt'
        frame = f'(device_{read} a same apart {offset} {width} (by decide))'
        if kind == 'signed':
            text += [f'  · obtain ⟨raw, loaded, decoded⟩ := h.{name}',
                     f'    exact ⟨raw, {frame}.symm.trans loaded, decoded⟩']
        else:
            text.append(f'  · exact {frame}.symm.trans h.{name}')
    text += ['', '#print axioms DeviceStableFields.frame', 'end Binary', '']
    (root / 'binary/DeviceScalars.lean').write_text('\n'.join(text))
