Raz's counterexample to the Reimer-condition strengthening
Lean 4.35.0 / bundled Std / no Mathlib dependency

What is proved

There is a nontrivial family of 11 distinct subsets of an 8-element ground set
satisfying Reimer's conditions, while every element occurs in exactly 5 sets.
Thus no element occurs in at least half the members. The family is not
union-closed. This is Abigail Raz's published 2017 construction, not a new
mathematical discovery or a resolution of Frankl's conjecture.

Primary mathematical source
Abigail Raz, Note on the union-closed sets conjecture,
Electronic Journal of Combinatorics 24(3) (2017), P3.53.
https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i3p53/pdf/
Definition 2: printed page 2. Counterexample 9: page 4. Pairing: page 5.
No third-party paper or code archive is redistributed in this package.

Files and review entry points

RazReimer.lean: explicit finite implementation and original certificate.
RazReimerPredicates.lean: arbitrary-subset presentation and transfer proofs.
Audit.lean: named theorem axiom audit.
MAPPING.txt: relation to the mathematical statement and scope limits.
ATTRIBUTION.txt: mathematical and implementation provenance.
reproduce.py: source-integrity check, Lake build, named axiom audit and
independent explicit-set verification. Uses Python's standard library only.
verify_sets.py: direct set enumeration and malformed-data negative controls.
source-manifest.json: exact source hashes, toolchain commit and status.

The principal statement-facing endpoints are
  RazReimerPredicates.counterexample
  RazReimerPredicates.not_strengthening
The condition equivalence is
  RazReimerPredicates.condition_iff
The enumeration-to-bijection justification is
  RazReimerPredicates.shared_index_bijective

Reproduction

Requires Lean 4.35.0 with its bundled Std and Lake, and Python 3.
No Mathlib or other Lake package is required. The pinned Lean source commit is
eb6cafb7290e8bd5f2937522d8d804f58f02bafc.

From this directory, when Lake is on PATH:
  python reproduce.py

An already installed alias with the same exact Lean version/commit may be used:
  python reproduce.py --lake PATH_TO_LAKE --toolchain INSTALLED_ALIAS

The script writes verification/result.json and build/axiom logs. A fresh archive
extraction contains no project .olean files. Lean's bundled standard-library
artifacts are reused; this is not a fresh build of Lean/Std or an independent
kernel-implementation replay. No independent external reviewer has accepted
the result.

Public records and prize status

Matching public mathematical page:
https://mathdb.com/p/363118/gowers-reimer-conditions-abundance-conjecture
Its prose matches the strengthening. The viewed page lists no posted solutions;
that does not prove that no prior formalization exists elsewhere. This page is
not a confirmed JSP-to-MathDB pilot mapping and establishes no prize eligibility.

An authorized eligibility inquiry was published, using renxuhang, at
https://github.com/TheJustinSunPrize/awards/issues/5124
It asks about topic acceptance, the old-result/new-Lean date rules and any
announced reward. It is not an award claim. No JSP ID, first-formalization
priority, committee acceptance or reward amount has been confirmed.

Source publication was authorized by renxuhang on 2026-10-21.
Repository: https://github.com/renxuhang/raz-reimer-lean
This source release is not an award application or an accepted MathDB
submission. No prize-team verification, priority decision or reward is
claimed. The scripts make no submissions, send no messages and collect
no identity or payment information. No separate reuse license is granted
by this README; upstream dependency licenses remain unchanged.
