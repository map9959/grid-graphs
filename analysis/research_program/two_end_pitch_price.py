"""Arbitrary-height two-ended cap with a physical pitch row anywhere inside."""
import os
from subprocess import check_output

def audit():
    env={k:v for k,v in os.environ.items() if not k.startswith('PITCH_')}
    for k,b in [(2,0),(3,1),(11,7)]:
        z=check_output(['target/pitch_endpoint_tariff',str(k),str(b),'350000'],
            env={**env,'PITCH_TWO':'1',**({'PITCH_AUTO':'1'} if k==11 else {})},text=True)
        assert 'state limit' not in z and f'window {k} pitch triples, all heights: min(bill,{b+1})={b+1}' in z
        print(z.splitlines()[-1])

if __name__=='__main__':audit()
