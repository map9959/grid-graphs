"""Replay the unconditional lower theorem using Lean-generated native code.

Run with `python3 -B -m analysis.research_program.residue_two_lower_lean`.
Uses one Lean worker, no external solver, and the checked-in turn regions.
The optional producer and ISL audit are not part of the trusted replay.
"""
import os
from pathlib import Path
import subprocess


def main():
    path=Path(__file__).resolve().parents[2]/'lean'
    prefix='GridGraphs.Constructions.ResidueTwo.'
    env={**os.environ,'LEAN_NUM_THREADS':'1'}

    def run(*args):
        subprocess.run(args,cwd=path,env=env,check=True)

    run('lake','build',prefix+'LowerTurnKernel:dynlib',prefix+'LowerTurnCoverageReplay')
    out=Path('.lake/build/lib/lean')
    lib=out/'gridgraphs_GridGraphs_Constructions_ResidueTwo_LowerTurnKernel.so'
    mod=Path('GridGraphs/Constructions/ResidueTwo/LowerTurnAll')
    run('lake','env','lean','--load-dynlib='+str(lib),'-o',str(out/mod.with_suffix('.olean')),
        str(mod.with_suffix('.lean')))
    result=Path('GridGraphs/Results/ResidueTwoLowerAll')
    run('lake','env','lean','-o',str(out/result.with_suffix('.olean')),str(result.with_suffix('.lean')))


if __name__=='__main__':
    main()
