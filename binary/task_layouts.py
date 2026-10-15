#!/usr/bin/env python3
"""Pinned DWARF task scalar and pointed-to credential/limit locations."""
import hashlib
from elftools.elf.elffile import ELFFile
from census import ORACLE, ROOT
from layouts import type_bytes

FIELDS = {
    'task_struct': ('task', [('flags', 4), ('atomic_flags', 8), ('blocked', 8),
        ('pending.signal', 8), ('thread_info.flags', 8), ('cred', 8), ('signal', 8),
        ('seccomp.mode', 4), ('seccomp.filter_count', 4), ('seccomp.filter', 8), ('task_works', 8)]),
    'cred': ('cred', [('cap_effective', 8)]),
    'signal_struct': ('signal', [('rlim', 256)]),
    'rlimit': ('rlimit', [('rlim_cur', 8)]),
    'file': ('file', [('f_task_work', 16)]),
    'callback_head': ('callback', [('next', 8), ('func', 8)]),
}

def unqualified(die):
    while die.tag in {'DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type'}:
        die = die.get_DIE_from_attribute('DW_AT_type')
    return die

def member(record, path):
    def candidates(parent, name, base=0):
        result = []
        for field in parent.iter_children():
            if field.tag != 'DW_TAG_member':
                continue
            loc = field.attributes.get('DW_AT_data_member_location')
            if loc is None and parent.tag == 'DW_TAG_union_type':
                delta = 0
            elif loc is not None and isinstance(loc.value, int):
                delta = loc.value
            else:
                raise ValueError(f'nonconstant member offset: {path}')
            field_name = field.attributes.get('DW_AT_name')
            if field_name is None:
                nested = unqualified(field.get_DIE_from_attribute('DW_AT_type'))
                if nested.tag not in {'DW_TAG_structure_type', 'DW_TAG_union_type'}:
                    raise ValueError(f'anonymous non-record member: {path}')
                result.extend(candidates(nested, name, base + delta))
            elif field_name.value.decode() == name:
                result.append((base + delta, field))
        return result

    offset = 0
    for name in path.split('.'):
        matches = candidates(record, name)
        if len(matches) != 1:
            raise ValueError(f'expected one member {path}: {name}')
        delta, field = matches[0]
        offset += delta
        record = unqualified(field.get_DIE_from_attribute('DW_AT_type'))
    return offset, field

def main():
    if hashlib.sha256(ORACLE.read_bytes()).hexdigest() != '16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774':
        raise ValueError('wrong ELF')
    found = {}
    with ORACLE.open('rb') as stream:
        elf = ELFFile(stream)
        dwarf = elf.get_dwarf_info()
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
        symbols = {}
        for name, kind, size in [('____fput', 'STT_FUNC', None), ('work_exited', 'STT_OBJECT', 16)]:
            entries = elf.get_section_by_name('.symtab').get_symbol_by_name(name)
            if not entries or len(entries) != 1 or entries[0]['st_info']['type'] != kind:
                raise ValueError(f'unexpected symbol: {name}')
            if size is not None and entries[0]['st_size'] != size:
                raise ValueError(f'unexpected symbol size: {name}')
            symbols[name] = entries[0]['st_value']
    if found.keys() != FIELDS.keys():
        raise ValueError(f'missing layouts: {FIELDS.keys() - found.keys()}')
    text = ['namespace Binary.TaskLayouts', '-- Generated from the pinned fs/file{,_table}.c DWARF CUs.']
    for name in FIELDS:
        text += found[name]
    text += [f'def fputCallbackAddress : BitVec 64 := .ofNat 64 {symbols["____fput"]}',
             f'def workExitedAddress : BitVec 64 := .ofNat 64 {symbols["work_exited"]}']
    text += ['end Binary.TaskLayouts', '']
    (ROOT / 'binary/TaskLayouts.lean').write_text('\n'.join(text))

if __name__ == '__main__':
    main()
