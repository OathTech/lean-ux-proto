"""Small controls for native RAM observation; no theorem acceptance here."""
from pathlib import Path
import struct
import tempfile
import unittest
import zlib

from c2_memory import DIRECT_MAP, IMAGE_BASE, PAGE, Writer, changed_runs, images, read, translate
from c2_capture import ENTRY, DONE, PREEMPT, WINDOW_OFFSET, WINDOW_BYTES
from c2_check import check_visit


class MemoryTests(unittest.TestCase):
    def test_deltas_keep_unchanged_bytes_and_reject_incomplete_base(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'ram'
            writer = Writer(path, 2 * PAGE)
            before = bytes(2 * PAGE)
            after = bytearray(before)
            after[PAGE + 17] = 91
            writer.add(before)
            writer.add(bytes(after))
            self.assertEqual(list(images(path, 2 * PAGE, 2)), [before, bytes(after)])
            self.assertEqual(list(changed_runs(before, after)), [(PAGE + 17, 1)])
            (path / '000000.z').write_bytes(zlib.compress(struct.pack('<II', 1, 0) + bytes(PAGE)))
            with self.assertRaisesRegex(ValueError, 'not complete'):
                list(images(path, 2 * PAGE, 2))

    def test_kernel_aliases_read_the_same_changed_physical_byte(self):
        # Two real four-level mappings of physical page 7, at distinct VAs.
        memory = bytearray(9 * PAGE)
        def word(address, value):
            struct.pack_into('<Q', memory, address, value)
        aliases = [IMAGE_BASE + 0x7000, DIRECT_MAP + 0x7000]
        for branch, virtual in enumerate(aliases):
            p3, p2, p1 = (1 + 3 * branch) * PAGE, (2 + 3 * branch) * PAGE, (3 + 3 * branch) * PAGE
            word(((virtual >> 39) & 511) * 8, p3 | 3)
            word(p3 + ((virtual >> 30) & 511) * 8, p2 | 3)
            word(p2 + ((virtual >> 21) & 511) * 8, p1 | 3)
            word(p1 + ((virtual >> 12) & 511) * 8, 7 * PAGE | 3)
        for virtual in aliases:
            self.assertEqual(translate(memory, 0, virtual), 7 * PAGE)
        memory[7 * PAGE] = 7
        self.assertEqual([read(memory, 0, virtual, 1) for virtual in aliases], [b'\x07', b'\x07'])

    def test_unmapped_or_outside_ram_is_not_zero_filled(self):
        with self.assertRaisesRegex(ValueError, 'unmapped'):
            read(bytes(PAGE), 0, DIRECT_MAP, 1)
        memory = bytearray(PAGE)
        struct.pack_into('<Q', memory, ((DIRECT_MAP >> 39) & 511) * 8, 20 * PAGE | 3)
        with self.assertRaisesRegex(ValueError, 'outside captured RAM'):
            read(memory, 0, DIRECT_MAP, 1)

    def example_visit(self, outside=False, rescheduled=False):
        before = bytearray(32 * 2**20)
        top = PAGE
        for virtual, p3, p2 in [(IMAGE_BASE, 2 * PAGE, 3 * PAGE),
                                 (DIRECT_MAP, 4 * PAGE, 5 * PAGE)]:
            struct.pack_into('<Q', before, top + ((virtual >> 39) & 511) * 8, p3 | 3)
            struct.pack_into('<Q', before, p3 + ((virtual >> 30) & 511) * 8, p2 | 3)
            for i in range(16):
                struct.pack_into('<Q', before, p2 + i * 8, i * 2**21 | 131)
        code = bytes([0x90]) * (DONE - ENTRY)
        before[ENTRY - IMAGE_BASE:DONE - IMAGE_BASE] = code
        struct.pack_into('<I', before, PREEMPT - IMAGE_BASE, 0x80000000)
        after = bytearray(before)
        struct.pack_into('<I', after, PREEMPT - IMAGE_BASE, 0x200 if rescheduled else 0x80000200)
        if outside:
            after[0xa005] = 99
        kp, skb = DIRECT_MAP + 0x8000, DIRECT_MAP + 0x9000
        def side(memory, pc):
            regs = dict(rip=pc, rbx=kp, r15=skb, rsp=DIRECT_MAP + 0xb000, r12=17, rsi=0x200)
            return dict(regs=regs, page_table_root=top,
                        window=read(memory, top, kp + WINDOW_OFFSET, WINDOW_BYTES).hex(),
                        nonce=read(memory, top, skb + 0x28, 8).hex(),
                        preempt=read(memory, top, PREEMPT, 4).hex(),
                        count_alias=dict(address=DIRECT_MAP + PREEMPT - IMAGE_BASE,
                                         bytes=read(memory, top, PREEMPT, 4).hex()))
        row = dict(visit=0, kp=kp, skb=skb, forced=False, entry=side(before, ENTRY), exit=side(after, DONE))
        image = dict(code=code.hex(), symbols={'_text': IMAGE_BASE, '_end': IMAGE_BASE + len(before)})
        return check_visit(row, bytes(before), bytes(after), image)

    def test_physical_pass_does_not_hide_virtual_alias_failure(self):
        report = self.example_visit()
        self.assertEqual(report['physical_frame']['status'], 'pass')
        self.assertEqual(report['native_virtual_frame']['status'], 'fail')
        self.assertTrue(report['native_virtual_frame']['counterexamples'][0]['allowed_physical_alias'])

    def test_write_outside_declared_physical_footprint_is_rejected(self):
        report = self.example_visit(outside=True)
        self.assertEqual(report['physical_frame']['status'], 'fail')
        self.assertEqual(report['physical_frame']['outside_bytes'], 1)

    def test_cleared_reschedule_bit_is_an_exact_count_failure(self):
        report = self.example_visit(rescheduled=True)
        self.assertEqual(report['count']['status'], 'fail')
        self.assertEqual(report['count']['expected'], '0x80000200')
        self.assertEqual(report['count']['actual'], '0x200')


if __name__ == '__main__':
    unittest.main()
