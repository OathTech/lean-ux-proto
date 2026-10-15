#!/usr/bin/env python3
"""Pinned DWARF locations for the task/files/fdtable relation."""
import hashlib
from elftools.elf.elffile import ELFFile
from census import ORACLE, ROOT
from layouts import type_bytes

FIELDS = {
    'task_struct': ('task', [('files', 8)]),
    'files_struct': ('files', [('count', 4), ('resize_in_progress', 1), ('fdt', 8), ('next_fd', 4)]),
    'fdtable': ('fdtable', [('max_fds', 4), ('fd', 8), ('close_on_exec', 8), ('open_fds', 8), ('full_fds_bits', 8)]),
}

def main():
    if hashlib.sha256(ORACLE.read_bytes()).hexdigest() != '16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774':
        raise ValueError('wrong ELF')
    found = {}
    with ORACLE.open('rb') as stream:
        dwarf = ELFFile(stream).get_dwarf_info()
        for cu in dwarf.iter_CUs():
            name = cu.get_top_DIE().attributes.get('DW_AT_name')
            if not name or not name.value.decode().endswith('/linux/fs/file.c'):
                continue
            for die in cu.iter_DIEs():
                name = die.attributes.get('DW_AT_name')
                if die.tag != 'DW_TAG_structure_type' or not name or 'DW_AT_byte_size' not in die.attributes:
                    continue
                name = name.value.decode()
                if name not in FIELDS:
                    continue
                prefix, requested = FIELDS[name]
                members = {d.attributes['DW_AT_name'].value.decode(): d for d in die.iter_children()
                           if d.tag == 'DW_TAG_member' and 'DW_AT_name' in d.attributes}
                row = [f'def {prefix}Size : Nat := {die.attributes["DW_AT_byte_size"].value}']
                for field, width in requested:
                    child = members[field]
                    offset = child.attributes['DW_AT_data_member_location'].value
                    if not isinstance(offset, int):
                        raise ValueError(f'nonconstant field: {name}.{field}')
                    actual = type_bytes(child.get_DIE_from_attribute('DW_AT_type'))
                    if actual != width:
                        raise ValueError(f'width {name}.{field}: {actual}, expected {width}')
                    row.append(f'def {prefix}_{field} : Nat := {offset}')
                if name in found and found[name] != row:
                    raise ValueError(f'inconsistent layout: {name}')
                found[name] = row
    if found.keys() != FIELDS.keys():
        raise ValueError(f'missing layouts: {FIELDS.keys() - found.keys()}')
    text = ['namespace Binary.FdLayouts', '-- Generated from the pinned fs/file.c DWARF CU.']
    for name in FIELDS:
        text += found[name]
    text += ['end Binary.FdLayouts', '']
    (ROOT / 'binary/FdLayouts.lean').write_text('\n'.join(text))

if __name__ == '__main__':
    main()
