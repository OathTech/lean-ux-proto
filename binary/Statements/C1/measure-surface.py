#!/usr/bin/env python3
"""Measure the printed size of the C1 statement packet's definitions the way
binary/surface.py prints the landed trust surface (#print at width 110,
universes shown). Run `lake -d binary build` first: the statement modules
are roots of the package library. This measures; it changes no gate file."""
import shutil
import subprocess
import sys
from pathlib import Path

W = str(Path(__file__).resolve().parents[3])
exp=open(W+'/binary/TrustSurface.expected.txt').read()
C='Binary.Statements.C1.'
groups={
 'A1 new premises and contracts':[C+x for x in ['Layout','Layout.fixed','Layout.heap','Layout.Arena','Layout.Heap','allocEntry','freeEntry','cacheWord','allocSites','freeSite','nodeSize','Allocator','Scratch','Kept','ServiceWrites','Separated','ServiceReady','AllocResult','AllocatorContract','Premises']],
 'A2 new caller conditions and starting point':[C+x for x in ['insertWindow','lookupWindow','callerSpans','frameReady','insertReady','lookupReady','armed','emptyTable']],
 'A3 existing definitions the premises draw in':['Binary.Pair.Trie.coverageCheck','Binary.Pair.Trie.coverageDataCheck','Binary.Pair.Trie.callServices','Binary.Pair.Trie.callBuffers','Binary.Pair.Trie.callMetadata','Binary.Pair.Trie.callHeaders','Binary.Pair.Trie.metadataSpans','Binary.Pair.Trie.writeSpans','Binary.Pair.Trie.readSpans','Binary.Pair.Trie.networkKeyCheck','Binary.Pair.spansApart','Binary.Pair.disjointRanges','readNat','Binary.Pair.Trie.address','Binary.Pair.Allowedips.tableFields','Binary.Pair.Allowedips.peerFields','Binary.Pair.Allowedips.Root.nodeOffsets','Binary.CommonBitsCoverage.Context','Binary.CommonBitsCoverage.Context.At','Binary.CommonBitsCoverage.Context.CoverageAt','Binary.CommonBitsCoverage.Context.Needed','Binary.CommonBitsCoverage.Context.writes','Binary.CommonBitsCoverage.Context.bytes','Binary.CommonBitsCoverage.Context.metadataBytes','Binary.CommonBits.Callbacks','Binary.Pair.Span.contains','Binary.Allowedips.swap32','Binary.Allowedips.swap64','Binary.Pair.require','Leanux.liftWG','Binary.Source.lookup'],
 'B1 new claim':[C+x for x in ['Initial','Framed','CountMoved','Referenced','SeqAdvanced','InsertWrites','LookupWrites','InsertStep','LookupStep','Headline']],
 'B2 existing definitions the conclusion draws in':['Binary.AllowedipsEntry.TotalWrites','Binary.EqualOutside','Binary.InRange','Binary.instructionStep'],
 'VAC2 image terms the witness draws in (F1)':['Binary.StatementC1CallbackImage.decoded','Binary.StatementC1CallbackImage.fetch','Binary.TrustBase.ServiceDecoderAgreement'],
 'ALT relation text of HeadlineExplicit (not surface under Headline)':[C+'Related',C+'HeadlineExplicit','Binary.Pair.Allowedips.assertAt','Binary.Pair.Allowedips.reconstruct','Binary.Pair.Allowedips.heap','Binary.Pair.Allowedips.target','Binary.Pair.Allowedips.validate','Binary.Pair.Allowedips.decodeNode','Binary.Pair.Allowedips.decodePeer','Binary.Pair.Allowedips.peerList','Binary.Pair.Allowedips.parent','Binary.Pair.Allowedips.internalListCheck','Binary.Pair.Trie.heap','Binary.Pair.Trie.validate','Binary.Pair.Trie.decodeNode','Binary.Pair.Trie.pointer'],
 'VAC witness and exclusions (signed with the headline)':[C+x for x in ['Ran','HeapSame','outcome','CallbacksFromImage','Executed','ServiceActive','Witness','LookupAfter','MirrorAccepts','InsertThenLookup','FailedInsertInvisible','Signed']],
}
src='import StatementC1Vacuity\nset_option format.width 110\nset_option pp.universes true\n'
order=[]
for g,names in groups.items():
    for n in names:
        src+=f'#print {n}\n#eval IO.println "@@@"\n'; order.append((g,n))
open(W+'/.tmp/c1/Surface.lean','w').write(src)
lp=subprocess.run(['../scripts/in-bundle','lake','env','printenv','LEAN_PATH'],cwd=W+'/binary',capture_output=True,text=True).stdout.strip()
r=subprocess.run((['capped','--'] if shutil.which('capped') else [])+['../scripts/in-bundle','env',f'LEAN_PATH={lp}','lean',W+'/.tmp/c1/Surface.lean'],cwd=W+'/binary',capture_output=True,text=True)
out=r.stdout
chunks=out.split('@@@\n')
errs=[l for l in (r.stdout+r.stderr).splitlines() if ": error" in l]
print("\n".join(errs[:20]))
if len(chunks)!=len(order)+1: print(r.stdout[-3000:],r.stderr[-2000:]); sys.exit(1)
tot={}
for (g,n),c in zip(order,chunks):
    lines=c.rstrip('\n').count('\n')+1
    short=n.split('.')[-1]
    landed = (('def '+n+' ') in exp) or (('structure '+n+' ') in exp) or (('def '+n+'\n') in exp)
    # TrustBase text uses unqualified names
    if not landed and n.startswith('Binary.TrustBase.'): landed=True
    t=tot.setdefault(g,[0,0,[]]); t[1 if landed else 0]+=lines; t[2].append(f'{short}:{lines}{"*" if landed else ""}')
for g,(new,old,items) in tot.items():
    print(f'{g}: {new} lines not in the landed file, {old} lines already printed there (*)\n   '+' '.join(items))
print('landed file lines:',exp.count('\n'))
# the definitional closure by declaring module (the mirror's share is here, not in the printed lines)
r=subprocess.run((['capped','--'] if shutil.which('capped') else [])+['../scripts/in-bundle','env',f'LEAN_PATH={lp}','lean','Statements/C1/Closure.lean'],cwd=W+'/binary',capture_output=True,text=True)
print(r.stdout+r.stderr)
