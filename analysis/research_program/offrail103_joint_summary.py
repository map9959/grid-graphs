"""Count distinct certified joint exclusions; optionally list open pairs."""
from collections import Counter
from itertools import combinations_with_replacement
import json,sys
from pathlib import Path

def report():
    survivors={}
    dest=Path('target/offrail103_joint35')
    inputs=[(dest/'crop_750.json','crop'),(dest/'board_500.json','board')]
    records=[]
    for path,kind in inputs:
        record=json.loads(path.read_text())
        if 'VERIFIED UNSAT' in record.values():
            assert b's VERIFIED' in (dest/f'{kind}_union.check').read_bytes()
        records.append(record)
    for depth,n in ((3,20),(5,18)):
        def pairs(record):
            return {tuple(sorted(key.split(':')[1].split('-'))):v for key,v in record.items()
                    if key.startswith(f'{depth}:')}
        crop,board=map(pairs,records)
        masks=sorted({s for pair in crop for s in pair})
        assert len(masks)==n and set(crop)==set(board)==set(combinations_with_replacement(masks,2))
        eliminated={p for p in crop if 'VERIFIED UNSAT' in (crop[p],board[p])}
        follow=dest/f'followup{depth}.json'
        if follow.exists():
            assert b's VERIFIED' in follow.with_suffix('.check').read_bytes()
            eliminated.update(tuple(sorted(k.split(':')[1].split('-'))) for k in json.loads(follow.read_text()))
        assert b's VERIFIED' in Path('target/offrail_corner_pair_103_2_10_12_bothomit2.check').read_bytes()
        extra={p for p in crop if all('2' not in s for s in p)}-eliminated
        print('extra from group-2 omission proof:',len(extra))
        eliminated.update(extra)
        live=sorted(set(crop)-eliminated)
        survivors[depth]=live
        print('depth',depth,'total',len(crop),'excluded',len(eliminated),'open',len(live))
        print('full-board statuses',Counter(board.values()))
        print('excluded identical pairs',[a for a,b in sorted(eliminated) if a==b])
        print('signatures with no partner',[s for s in masks if not any(s in p for p in live)])
        if '--list-open' in sys.argv:print('open:',','.join('-'.join(p) for p in live))
    return survivors
if __name__=='__main__':report()
