# Reproducing the PG(7,2) certificate

The release asset `pg72-chromatic6-certificate.zip` contains the checker sources, integer data, enumeration witnesses, CNF and DRAT certificates, and the English argument. The top-level asset checksum and the internal manifest attest to the bytes of the release materials.

Download the asset and its accompanying `SHA256SUMS.txt` into the same writable directory. Verify the outer archive before extracting it, then verify the internal manifest. The verification requires Python 3.12 or later, C and C++20 compilers, zlib headers, and `python-sat==1.9.dev25` to reproduce the older CNF files byte for byte. If a POSIX temporary-directory alias is a symlink, use a real path for `TMPDIR`. This applies on macOS where `/tmp` normally resolves to `/private/tmp`.

```sh
shasum -a 256 -c SHA256SUMS.txt
python3 -m zipfile -e pg72-chromatic6-certificate.zip .
cd pg72_deliverable
shasum -a 256 -c SHA256SUMS.txt
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install python-sat==1.9.dev25
python3 verify_chromatic6.py
```

Full replay executes the following stages. The program launches the component programs in its own tree and saves individual logs.

| Stage | Finite evidence checked |
| --- | --- |
| Elementary cap bound | Direct checks supporting the human proof and six-coloring |
| Sizes 52 and above, older pair proofs | Capacity and extension enumerations, complete-type classification and relevant older DRAT certificates |
| Size 51 | Complete-cap classifications with explicit linear maps and failed six-space intersections |
| Old pair CNF regeneration | Exact reconstruction and validation of the old pair CNFs |
| Nine pair exclusions with sizes 51 and 53 | Geometry and representative coverage, inconsistency certificates, whole kernel enumeration, forced lines, and DRAT |
| Two $A_{51a}$ caps | Independent data regeneration and checking for the remaining disjoint pair case |
| Size 50 | Both circuit branches, including independent searches and linear equivalence witnesses |
| Five pairs with $A_{58}$ | Relative configurations with the intersection limits in the paper |
| Final $A_{58},A_{50}$ pair | The ten normalizations, disjoint quotient maps, lifts, and root-count exclusions |

## Connecting the checks to the proof

For a complete cap meeting every 6-space, its intersection with each hyperplane has a shortest odd circuit of length five or seven. The moment identities in [the cap bound](cap-bound.md) give an upper bound on the smallest hyperplane section at the sizes of interest. In the 5-circuit branch the span has dimension four and contains the circuit. Each of its eight outer cosets contains at most five points. Its allowable subsets are independent sets of the difference graph on the 16 vectors. A saturated outer coset is a translate of the circuit. The classification enumerates the outer subsets according to size and computes all allowable inner points by excluding sums of outer pairs. Capacity rules out a size if too few inner points remain. To test maximality, if the allowable inner set itself fits into the cap, all of it must be taken. Other inner sets are treated by enumerating their admissible subsets. Finite checks compare the complete caps that survive using explicit invertible linear maps.

The 7-circuit branch uses the span of dimension six. In the hyperplane's two inside cosets the largest possible size is seven. The outside cosets are independent in the 64-vertex difference graph of the seven circuit elements and have size at most 22. One fixes the circuit and enumerates the admissible inside/outer size triples and the compatible independent sets. A hyperplane section used to start this branch contains no 5-circuit. This permits further restrictions on same-coset differences within it. The tables test unmatched candidates for failure to meet a specified 6-space.

The size-50 replay covers 33 through 40 outside points in the 5-circuit branch, since the cap has a hyperplane section of size at most 17 by the cubic moment calculation
$\sum_H(h_H-18)(h_H-26)(h_H-27)=-1280$.
The two independent implementations agree on 39 complete candidates. These and four candidates from earlier independent scans map explicitly to $A_{50}$. The 7-circuit branch has 24 size triples. The remaining four complete candidates miss the intersection of the hyperplanes with binary normal vectors 47 and 159. This branch is cross-checked using maximal-clique enumeration and direct independent-set enumeration.

For the pair exclusions, necessary root counts and the six-space intersection condition are applied before representative counting. Explicit changes of basis connect the parametrized geometries to the representatives, and the proof of each obstruction is checked on the same residual set. An $\mathbb F_3$ inconsistency witness is a linear combination of incidence rows with zero left side and nonzero right side. For consistent systems the checker recomputes the kernel. It tests normalized coefficient combinations exhaustively, detects forced monochromatic lines, or constructs and validates a CNF for the remaining color candidates and checks the accompanying DRAT proof. The independent checker parses the ternary addition gates and forbidden-line clauses against the residual geometry. The saved solver search can therefore be omitted from a proof replay.

The disjoint $A_{51a},A_{51a}$ case regenerates 20,917,245 flagged caps from 109,314 core representatives and compares the implied lists. There are 3,107,386 ordered representative pairs, reduced to 1,553,693 by explicit pair interchange. The exclusions cover 1,216,483 inconsistent systems, 329,058 kernel enumerations, 5,617 forced-line cases, and 2,535 CNF and DRAT cases. For $A_{58}$ paired with types $A_{51a},A_{51b},A_{53a},A_{53b},A_{58}$, the representative counts after filtering are 5, 0, 5, 2 and 3. Those 15 representatives give five field inconsistencies, nine direct kernel checks and one DRAT proof. The three representatives of the last type have distinct periods. The common-period argument uses the minimum-intersection bound verified by the nine newer and seven older CNF and DRAT cases in the sizes-52-and-above stage. The older CNFs are also regenerated and checked against the source geometry in a separate stage.

## A quick report audit

Use `python3 verify_chromatic6.py --audit-reports` to audit the supplied component summaries and rerun small direct checks such as the explicit six-coloring. That mode does not rerun the enumerations or DRAT checks. The full command above replays those checks. Interpret older exploratory logs according to the scope of their component.
