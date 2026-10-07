#!/usr/bin/env python3
"""Auditor's own cycle-minimum bound program (audit report item (d)).

For each K <= KMAX compute, with exact integers and no floats:
  S(K) = least S with 3^K < 2^S            (= bit length of 3^K)
  m(K) = largest m with (3m+1)^K >= 2^S * m^K   (integer binary search)
and report the maximum of m(K), the K that attains it, the first K reaching the
thresholds the project's statement names, plus a decimal cross-check of m(K).
Usage: python3 bounds.py [KMAX]   (default 1635)
"""
import sys
from decimal import Decimal, getcontext

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1635


def largest_m(K, S):
    lo = hi = 1
    while (3 * hi + 1) ** K >= (1 << S) * hi ** K:
        hi *= 4
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if (3 * mid + 1) ** K >= (1 << S) * mid ** K:
            lo = mid
        else:
            hi = mid - 1
    return lo


rows = []
for K in range(1, KMAX + 1):
    S = (3 ** K).bit_length()                 # least S with 3^K < 2^S
    assert 3 ** K < (1 << S) and 3 ** K >= (1 << (S - 1))
    rows.append((K, S, largest_m(K, S)))

best = max(rows, key=lambda r: r[2])
print(f"KMAX={KMAX}  max m = {best[2]} at K = {best[0]} (S = {best[1]})")
for th in (3342, 27113, 99780, 330749):
    hit = [r for r in rows if r[2] >= th]
    print(f"  m >= {th}: first K = {hit[0][0]} (m={hit[0][2]}), last K = {hit[-1][0]} (m={hit[-1][2]})" if hit else f"  m >= {th}: never")

getcontext().prec = 60
print("decimal cross-check 1/(2^(S/K)-3):")
for K in (41, 94, 253, 305, 306, 971, 1635):
    if K <= KMAX:
        S = (3 ** K).bit_length()
        exact = [r[2] for r in rows if r[0] == K][0]
        approx = Decimal(1) / (Decimal(2) ** (Decimal(S) / Decimal(K)) - 3)
        print(f"  K={K:5d} integer m={exact:8d}  1/(2^(S/K)-3)={approx:.4f}")
