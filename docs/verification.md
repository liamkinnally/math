# Local verification and required Palomar preflight

## Checked locally on November 27, 2026

The eight submitted Lean source modules build with Lean 4.35.0 and pinned Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. The six-module mathematical proof from the earlier Lean 4.33.1 package was ported using module/public headers and a replacement for a deprecated simp call; the graph statement and hypotheses are unchanged.

The separate Challenge fixes the actual graph definitions and the exact rational quotient. Its one deliberate theorem hole is the comparison target. No proof-development file or Solution contains an admitted proof. The three completed headline declarations have only propext, Classical.choice and Quot.sound as transitive axioms.

Comparator matched the exact local exports of Challenge and Solution. The solution replay was accepted by Lean, NanoDa, and the Palomar-pinned con-ron checker in verified mode. All checker hashes and the export hashes are recorded in `../verification/local-comparator.log`.

## Environment limitation

The standard nested Bubblewrap launch failed in this execution environment with `bwrap: Can't create file /root: Read-only file system`. Its error is preserved in `../verification/standard-comparator-environment-error.log`. A supported local preexport mode then performed the comparison and kernel replays without that nested sandbox. Comparator explicitly warns that its sandbox-disabled run is not trustworthy as an adversarial verification boundary. The local result is advisory and is **not a passing official Palomar mechanical report**.

Before intake, the full official reusable workflow must pass at the exact public GitHub source commit. `.github/workflows/palomar.yml` supplies that workflow with the approved GitHub-hosted execution profile and an immutable pipeline pin. No CI pass, submission acceptance, or registry entry is claimed by these local logs.

## Integrity

From the repository root, run `sha256sum -c verification/statement-and-proof.sha256` to compare the build and statement sources with the locally audited versions. `SHA256SUMS` additionally covers the complete packaged source snapshot.
