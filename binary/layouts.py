"""Extract layouts from the relevant CU, without treating C headers as evidence."""
from elftools.elf.elffile import ELFFile


def layouts(kernel):
    wanted = {'index_hashtable', 'index_hashtable_entry', 'hlist_node', 'hlist_head',
              'allowedips_node', 'allowedips', 'pcpu_hot', 'wg_peer', 'kref', 'refcount_struct',
              'noise_keypair', 'noise_keypairs', 'noise_replay_counter', 'noise_symmetric_key', 'noise_handshake'}
    result = {}
    with open(kernel, 'rb') as stream:
        dwarf = ELFFile(stream).get_dwarf_info()
        for cu in dwarf.iter_CUs():
            name = cu.get_top_DIE().attributes.get('DW_AT_name')
            if not name or not name.value.decode().endswith(('wireguard/peerlookup.c', 'wireguard/allowedips.c')):
                continue
            for die in cu.iter_DIEs():
                name = die.attributes.get('DW_AT_name')
                if die.tag != 'DW_TAG_structure_type' or not name or name.value.decode() not in wanted:
                    continue
                if 'DW_AT_byte_size' not in die.attributes:
                    continue
                name = name.value.decode()
                members = {}
                arrays = {}
                def visit(parent, base):
                    for child in parent.iter_children():
                        if child.tag != 'DW_TAG_member':
                            continue
                        loc = child.attributes.get('DW_AT_data_member_location')
                        offset = loc.value if loc else 0
                        if not isinstance(offset, int):
                            raise ValueError(f'nonconstant DWARF member offset: {name}')
                        if 'DW_AT_name' in child.attributes:
                            field = child.attributes['DW_AT_name'].value.decode()
                            members[field] = base + offset
                            if name == 'noise_replay_counter' and field == 'backtrack':
                                typ = child.get_DIE_from_attribute('DW_AT_type')
                                while typ.tag in {'DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type'}:
                                    typ = typ.get_DIE_from_attribute('DW_AT_type')
                                if typ.tag != 'DW_TAG_array_type':
                                    raise ValueError('replay bitmap is not a DWARF array')
                                bounds = [d for d in typ.iter_children() if d.tag == 'DW_TAG_subrange_type']
                                if len(bounds) != 1 or 'DW_AT_upper_bound' not in bounds[0].attributes:
                                    raise ValueError('replay bitmap has no fixed one-dimensional bound')
                                count = bounds[0].attributes['DW_AT_upper_bound'].value + 1
                                lower = bounds[0].attributes.get('DW_AT_lower_bound')
                                if lower and lower.value != 0:
                                    raise ValueError('replay bitmap has a nonzero lower bound')
                                elem = typ.get_DIE_from_attribute('DW_AT_type')
                                while elem.tag in {'DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type'}:
                                    elem = elem.get_DIE_from_attribute('DW_AT_type')
                                arrays[field] = dict(count=count, element_size=elem.attributes['DW_AT_byte_size'].value)
                        else:
                            visit(child.get_DIE_from_attribute('DW_AT_type'), base + offset)
                visit(die, 0)
                row = dict(size=die.attributes['DW_AT_byte_size'].value, members=members)
                if arrays:
                    row['arrays'] = arrays
                if name in result and result[name] != row:
                    raise ValueError(f'inconsistent DWARF layouts: {name}')
                result[name] = row
    if not {'index_hashtable', 'index_hashtable_entry', 'hlist_node', 'hlist_head', 'allowedips_node'} <= result.keys():
        raise ValueError(f'missing DWARF layouts: {wanted - result.keys()}')
    return result
