# Verification

Palomar compared the independent `Challenge.lean` statement with `WOW261.conjecture261_ratio` in the Solution at commit [`551b13e8ce5c1b4b17b18e638cb8d86f27a98718`](https://github.com/liamkinnally/math/tree/551b13e8ce5c1b4b17b18e638cb8d86f27a98718). The official mechanical report records `pass` with zero errors and zero warnings. Lean, nanoda, and con-ron accepted the proof. The permitted axioms were `propext`, `Classical.choice`, and `Quot.sound`. [Mechanical report](https://data.palomar-registry.org/evidence/PALOMAR-2026-11-27-000022-v1/5dfb5ff52d41340a1d561fbff60a4723b332bbd36672887e81010524fb8f19c1/mechanical-report.json)

| Official check | Result |
| --- | --- |
| [Full preflight](https://github.com/liamkinnally/math/actions/runs/45959227360) | Passed at the registered commit |
| [Submission verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45960291320) | Passed the proof and Challenge provenance checks |
| [Challenge rendering](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45961523614) | Passed and produced the formatted statement |

The [version 1 registry entry](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000022&version=1) links to the rendered Challenge and the public evidence. The [PalomarArchive copy](https://github.com/PalomarArchive/liamkinnally--math--ce378b283a07/tree/551b13e8ce5c1b4b17b18e638cb8d86f27a98718) preserves the registered source.

## Reproduce the check

The project pins Lean `4.35.0` in `lean-toolchain` and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`. With Git and Elan installed, build the registered snapshot as follows.

```bash
git clone https://github.com/liamkinnally/math.git
cd math
git checkout --detach 551b13e8ce5c1b4b17b18e638cb8d86f27a98718
lean --version
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Acyclic \
  Mathlib.Combinatorics.SimpleGraph.Star \
  Mathlib.Algebra.Order.Field.Basic Mathlib.Algebra.Order.Field.Rat
lake build
```

On Linux with a working Bubblewrap sandbox, run the statement comparison.

```bash
lake comparator
```

The build may warn about the deliberate comparison hole in `Challenge.lean`. `Solution.lean` imports the completed proof. To audit the quotient theorem’s axioms directly, run the following.

```bash
lake env lean --stdin <<'LEAN'
import Solution

#print axioms WOW261.conjecture261_ratio
LEAN
```

The [proof checksum manifest](../verification/statement-and-proof.sha256) covers the statement, proof, and build configuration. Run `sha256sum -c verification/statement-and-proof.sha256` from the repository root. The [full manifest](../SHA256SUMS) also covers the documentation in the same checkout.

## Historical local replay

Before the official runs, Bubblewrap could not start inside the local runner. An advisory local check compared prebuilt exports and replayed the proof with Lean, nanoda, and con-ron, with Comparator’s nested sandbox disabled. The official runs above used Palomar’s pinned sandbox. [Sandbox startup error](../verification/standard-comparator-environment-error.log) · [Advisory replay log](../verification/local-comparator.log)
