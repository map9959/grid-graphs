"""Cycle of four elbows and four dense sides with variable three-mark cuts."""
from itertools import combinations_with_replacement
from pathlib import Path
import ast
import re
import subprocess

WORDS=(146,145,137,73)
# Unordered pairs in WORDS order. Scores exclude both end masks in an
# elbow and are relative to 3L on a side. -6 is the safe pruning floor.
CORNERS=((36,36,37,38,38,39),(36,36,37,38,38,39),(36,36,37,38,38,38),(35,36,36,37,37,37),
         (35,36,36,37,38,38),(35,36,36,37,37,38),(35,35,36,36,37,37),
         (35,36,36,37,37,37),(35,35,35,36,36,36),(34,34,35,35,35,35))
BACKED=((-4,-2,-1,0,0,0),(-3,-2,-1,0,0,0),(-3,-2,-1,-1,-1,0),(-3,-2,-2,-2,-1,-1),
        (-6,-3,-1,-1,-1,0),(-6,-2,-1,-1,-1,-1),(-6,-3,-2,-2,-2,-2),
        (-6,-3,-2,-1,-1,-1),(-6,-3,-3,-2,-2,-2),(-6,-4,-3,-2,-2,-2))
FREE=((-4,-2,-1,0,0,0),(-3,-2,-1,0,0,0),(-3,-1,-1,-1,0,0),(-3,-2,-2,-1,-1,-1),
      (-3,-1,-1,0,1,0),(-2,-1,0,0,0,0),(-2,-2,-1,-1,-1,-1),
      (-3,-1,-1,0,1,0),(-3,-2,-1,0,-1,-1),(-4,-3,-2,0,-1,-1))
PHYSICAL=((-4,-2,-1,0,0,0),(-3,-2,-1,0,0,0),(-3,-2,-1,-1,0,0),(-3,-2,-2,-2,-1,-1),
          (-3,-1,-1,0,0,0),(-3,-1,-1,-1,-1,0),(-3,-2,-2,-2,-1,-1),
          (-3,-2,-2,0,0,0),(-3,-3,-2,-1,-1,-1),(-4,-3,-2,0,-1,-1))

def cycle(corners,sides,words=WORDS):
    pairs=list(combinations_with_replacement(WORDS,2))
    def get(table,a,b):return table[pairs.index((max(a,b),min(a,b)))]
    top=-10000
    for start in words:
        dp={(start,0):0}
        for i,table in enumerate((corners,sides)*4):
            nd={}
            for (a,k),v in dp.items():
                for b in ((start,) if i==7 else words):
                    for r,z in enumerate(get(table,a,b)):
                        if k+r<=23:nd[b,k+r]=max(nd.get((b,k+r),-10000),v+z)
            dp=nd
        top=max(top,max(dp.values()))
    return top

def replay(table,mode):
    for (a,b),row in zip(combinations_with_replacement(WORDS,2),table):
        cmd=(['collar_bend','dense-ranks','0','0'] if mode=='corner' else
             ['dense_pitch_dominance','3','1',mode])+[str(a),str(b)]
        cmd[0]=str(Path('target')/cmd[0])
        out=subprocess.check_output(cmd,text=True).splitlines()[-1]
        result=ast.literal_eval(re.search(r'\[.*?\]',out)[0])
        assert tuple(max(-6,v) for v in result)==row,(a,b,result,row)

if __name__=='__main__':
    import sys
    if '--replay' in sys.argv:
        replay(CORNERS,'corner');replay(BACKED,'ranks');replay(FREE,'free-ends');replay(PHYSICAL,'physical-ends')
    assert cycle(CORNERS,BACKED)==151
    assert (cycle(CORNERS,FREE),cycle(CORNERS,PHYSICAL))==(152,151)
    print('four backed cut words, largest rank-feasible overhead:',cycle(CORNERS,BACKED))
    print('four free cut words, largest rank-feasible overhead:',cycle(CORNERS,FREE))
    print('four physical cut words, largest rank-feasible overhead:',cycle(CORNERS,PHYSICAL))
