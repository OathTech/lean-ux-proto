#!/usr/bin/env python3
"""Pinned DWARF task scalar and pointed-to credential/limit locations."""
import hashlib
from elftools.elf.elffile import ELFFile
from census import ORACLE, ROOT
from layouts import type_bytes

FIELDS = {
    'task_struct': ('task', [('flags', 4), ('atomic_flags', 8), ('blocked', 8),
        ('pending.signal', 8), ('thread_info.flags', 8), ('cred', 8), ('signal', 8),
        ('seccomp.mode', 4), ('seccomp.filter_count', 4), ('seccomp.filter', 8)]),
    'cred': ('cred', [('cap_effective', 8)]),
    'signal_struct': ('signal', [('rlim', 256)]),
    'rlimit': ('rlimit', [('rlim_cur', 8)]),
}

def unqualified(die):
    while die.tag in {'DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type'}:
        die = die.get_DIE_from_attribute('DW_AT_type')
    return die

def member(record, path):
    offset = 0
    for name in path.split('.'):
        matches = [d for d in record.iter_children() if d.tag == 'DW_TAG_member'
                   and d.attributes.get('DW_AT_name') and d.attributes['DW_AT_name'].value.decode() == name]
        if len(matches) != 1:
            raise ValueError(f'expected one member {path}: {name}')
        field = matches[0]
        loc = field.attributes.get('DW_AT_data_member_location')
        if not loc or not isinstance(loc.value, int):
            raise ValueError(f'nonconstant member offset: {path}')
        offset += loc.value
        record = unqualified(field.get_DIE_from_attribute('DW_AT_type'))
    return offset, field

def main():
    if hashlib.sha256(ORACLE.read_bytes()).hexdigest() != '16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774':
        raise ValueError('wrong ELF')
    found = {}
    with ORACLE.open('rb') as stream:
        dwarf = ELFFile(stream).get_dwarf_info()
        for cu in dwarf.iter_CUs():
            name = cu.get_top_DIE().attributes.get('DW_AT_name')
            if not name or not name.value.decode().endswith(('/linux/fs/file.c', '/linux/fs/file_table.c')):
                continue
            for die in cu.iter_DIEs():
                name = die.attributes.get('DW_AT_name')
                if die.tag != 'DW_TAG_structure_type' or not name or 'DW_AT_byte_size' not in die.attributes:
                    continue
                name = name.value.decode()
                if name not in FIELDS:
                    continue
                prefix, requested = FIELDS[name]
                row = [f'def {prefix}Size : Nat := {die.attributes["DW_AT_byte_size"].value}']
                for field, width in requested:
                    offset, child = member(die, field)
                    actual = type_bytes(child.get_DIE_from_attribute('DW_AT_type'))
                    if actual != width:
                        raise ValueError(f'width {name}.{field}: {actual}, expected {width}')
                    row.append(f'def {prefix}_{field.replace(".", "_")} : Nat := {offset}')
                if name == 'task_struct':
                    offset, field = member(die, 'in_eventfd')
                    attrs = field.attributes
                    size = attrs['DW_AT_bit_size'].value
                    width = attrs['DW_AT_byte_size'].value
                    shift = width * 8 - attrs['DW_AT_bit_offset'].value - size
                    if size != 1 or width != 4 or not 0 <= shift < 32:
                        raise ValueError('unexpected in_eventfd bitfield shape')
                    row += [f'def task_in_eventfd : Nat := {offset}',
                            f'def task_in_eventfd_bit : Nat := {shift}']
                if name in found and found[name] != row:
                    raise ValueError(f'inconsistent layout: {name}')
                found[name] = row
    if found.keys() != FIELDS.keys():
        raise ValueError(f'missing layouts: {FIELDS.keys() - found.keys()}')
    text = ['namespace Binary.TaskLayouts', '-- Generated from the pinned fs/file{,_table}.c DWARF CUs.']
    for name in FIELDS:
        text += found[name]
    text += ['end Binary.TaskLayouts', '']
    (ROOT / 'binary/TaskLayouts.lean').write_text('\n'.join(text))

if __name__ == '__main__':
    main()
