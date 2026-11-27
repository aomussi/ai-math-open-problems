"""Outcome classifier on B664 + k H30 + m H34.

The accompanying verify.py checks all original move conditions.
P_table = exact outcomes for m=0..5,k=0..7; for all other coordinates use
finite boundary/diagonal rules, expressed both numerically and in Presburger
arithmetic for independent verification.
"""
import json
from pathlib import Path
DATA=json.loads(Path(__file__).with_name('outcomes.json').read_text())
P=DATA['p_table']

def reduce_counters(k,m):
    assert k>=0 and m>=0
    if m>=6:
        s=4+m%2
        x=k-m+s
        k=x if x>=1 else (0 if k==0 else 1+(k-1)%2)
        m=s
    if k>=6:k=6+k%2
    return k,m

def outcome(b,k,m):
    k,m=reduce_counters(k,m)
    return bool(P[b][m][k])
