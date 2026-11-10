/* C2 statement packet: the proposed semantics of `bts %r15,(%rax)` (bytes 4c 0f ab 38,
 * as in the pinned image) against the processor this runs on. A test of the proposal on
 * one CPU, not a proof of ISA fidelity.
 *   cc -O1 -o "$out"/bts_host binary/packets/c2/bts_host.c && "$out"/bts_host
 * Checks, for bit offsets 0..63 (the proposal's domain): CF is the old bit; the addressed
 * quadword has the bit set; its neighbours are unchanged. Reports, for offsets outside
 * 0..63 (declined by the proposal), which quadword the processor addresses, and which of
 * the flags the manuals leave undefined or unaffected this processor changes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Runs the four bytes with rax = base, r15 = offset, and the status flags first set from
 * `flags_in`; returns RFLAGS afterwards. */
static uint64_t bts(uint64_t *base, int64_t offset, uint64_t flags_in)
{
	register int64_t r15 __asm__("r15") = offset;
	uint64_t flags_out;
	__asm__ volatile("pushq %[in]\n\tpopfq\n\t.byte 0x4c,0x0f,0xab,0x38\n\tpushfq\n\tpopq %[out]"
			 : [out] "=&r"(flags_out)
			 : [in] "r"(flags_in), "a"(base), "r"(r15)
			 : "memory", "cc");
	return flags_out;
}

#define CF 0x001u
#define PF 0x004u
#define AF 0x010u
#define ZF 0x040u
#define SF 0x080u
#define OF 0x800u
#define STATUS (CF | PF | AF | ZF | SF | OF)

int main(void)
{
	static const uint64_t words[] = { 0, ~0ull, 0xa5a5a5a55a5a5a5aull, 1, 0x8000000000000000ull,
					  0x0123456789abcdefull };
	static const uint64_t flag_sets[] = { 0, STATUS, ZF | PF, SF | OF | AF };
	unsigned long failures = 0, runs = 0, changed = 0;
	uint64_t mem[5];

	for (unsigned w = 0; w < sizeof words / sizeof *words; w++)
		for (int bit = 0; bit < 64; bit++)
			for (unsigned f = 0; f < 4; f++) {
				uint64_t in = flag_sets[f] | 0x202, out;
				mem[0] = mem[1] = mem[3] = mem[4] = 0x1111111111111111ull;
				mem[2] = words[w];
				out = bts(&mem[2], bit, in);
				runs++;
				if (!!(out & CF) != !!(words[w] >> bit & 1)) failures++;
				if (mem[2] != (words[w] | 1ull << bit)) failures++;
				if (mem[0] != 0x1111111111111111ull || mem[1] != mem[0] || mem[3] != mem[0] ||
				    mem[4] != mem[0]) failures++;
				changed |= (out ^ in) & (STATUS & ~CF);
			}
	printf("offsets 0..63: %lu runs, %lu disagreements with the proposal\n", runs, failures);
	printf("flags other than CF changed on this processor (mask of PF|AF|ZF|SF|OF): %#lx\n", changed);

	/* Outside the proposal's domain: which quadword does the processor address? */
	static const int64_t far[] = { 64, 127, 128, -1, -64, -65 };
	for (unsigned i = 0; i < sizeof far / sizeof *far; i++) {
		memset(mem, 0, sizeof mem);
		bts(&mem[2], far[i], 0x202);
		int hit = -9;
		for (int j = 0; j < 5; j++) if (mem[j]) hit = j - 2;
		printf("offset %4ld: quadword %+d, bit %d (expected %+ld, %ld)\n", (long)far[i], hit,
		       hit == -9 ? -1 : __builtin_ctzll(mem[hit + 2]),
		       (long)(far[i] >> 6), (long)(far[i] & 63));
		if (hit != (far[i] >> 6) || __builtin_ctzll(mem[hit + 2]) != (far[i] & 63)) failures++;
	}
	return failures != 0;
}
