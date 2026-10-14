"""Extract layouts from the relevant CU, without treating C headers as evidence."""
from elftools.elf.elffile import ELFFile


def layouts(kernel):
    wanted = {'index_hashtable', 'index_hashtable_entry', 'hlist_node', 'hlist_head',
              'allowedips_node', 'allowedips', 'pcpu_hot', 'wg_peer', 'kref', 'refcount_struct'}
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
                def visit(parent, base):
                    for child in parent.iter_children():
                        if child.tag != 'DW_TAG_member':
                            continue
                        loc = child.attributes.get('DW_AT_data_member_location')
                        offset = loc.value if loc else 0
                        if not isinstance(offset, int):
                            raise ValueError(f'nonconstant DWARF member offset: {name}')
                        if 'DW_AT_name' in child.attributes:
                            members[child.attributes['DW_AT_name'].value.decode()] = base + offset
                        else:
                            visit(child.get_DIE_from_attribute('DW_AT_type'), base + offset)
                visit(die, 0)
                row = dict(size=die.attributes['DW_AT_byte_size'].value, members=members)
                if name in result and result[name] != row:
                    raise ValueError(f'inconsistent DWARF layouts: {name}')
                result[name] = row
    if not {'index_hashtable', 'index_hashtable_entry', 'hlist_node', 'hlist_head', 'allowedips_node'} <= result.keys():
        raise ValueError(f'missing DWARF layouts: {wanted - result.keys()}')
    return result
