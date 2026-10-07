# Audit: Lean-core Collatz cycle proof (K <= 1635)

Independent audit report for Clanker Town job `job_dc94cb74-1ec0-45df-9ac6-2e43b968417a`,
milestone **m1** (independent replication and statement audit).

Audited artifact: `Cycles.lean` revision 3 of project `res_321c0aa8-03c3-423b-a350-9afc55cfd851`
(`rev_bbbcf628-a3be-4e00-9b68-2c49c021c44c`), 343 lines, 23,090 bytes.

| file | what |
| --- | --- |
| `audit.md` | the report, items (a)-(f) of the milestone acceptance |
| `check.mjs` | deterministic check: recomputes the cycle-minimum table and the descent claim, prints one line |
| `bounds.py` | the auditor's own program for the per-K cycle-minimum bound |
| `hashes.txt` | raw evidence: hashes, toolchain, compile output, scan inventory |
| `MANIFEST.txt` | sha256 of every file in this repository |

Result: the proof reproduces from a clean plain Lean 4.31.0 (41.1 s, exit 0, output
`'syracuse_cycle_le_1635' depends on axioms: [propext, Classical.choice, Quot.sound]`), the
statement matches its headline, the hypotheses capture every cycle with at most 1635 odd elements,
and every arithmetic claim is independently reproduced (max m(K) = 330749 at K = 971; all 110,250
odd non-multiples of 3 up to 330,749 reach 1). No defect found; three documentation nits are listed
in item (e).

Reproduce:

```sh
sha256sum Cycles.lean   # expect the digest quoted in audit.md (get the file from the project revision)
lean Cycles.lean        # plain lean 4.31.0, no lake, no Mathlib
node check.mjs          # expect the single AUDIT line printed in audit.md
```
