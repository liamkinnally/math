# Palomar submission procedure

The root project is prepared for an ordinary new submission of Written on the Wall II #261. The selected result is `WOW261.conjecture261_ratio`; the intended responsible author and maintainer is Liam Kinnally. The file `formalization.yaml` discloses GPT-6 Astra Pro and Gemini 4 Hydrogen assistance and pending independent human expert review.

## Before intake

Publish this complete source project at the root of [liamkinnally/math](https://github.com/liamkinnally/math). Use the full 40-character commit returned by `git rev-parse HEAD`. The normal settings are:

- Repository `liamkinnally/math`.
- Project directory: repository root (leave blank).
- Comparator configuration: `comparator.json`.
- Formalization metadata: `formalization.yaml` (default).
- Existing Palomar ID: blank for this new result.
- Relationship: responsible author or maintainer, as authorized by Liam Kinnally.

The included GitHub Actions workflow runs Palomar's complete reusable verification with `mode: full` and `execution_profile: palomar-standard-v1`. The workflow reference and `pipeline_commit` both pin `046554302064b2c83c2b924bea6db87fc5900c68`. Inspect the `mechanical-report-preflight001` artifact and require `status: pass` for the exact source commit before submission. A local Lean build or local Comparator run does not replace this full preflight.

## Submit and retain the result

The submission host is https://submit.palomar-registry.org/. Palomar's published agent protocol is https://submit.palomar-registry.org/llms.txt. A human can use the browser form and perform GitHub authorization themselves. An agent must use the documented repository-tag plus secret-gist verification protocol with the required authenticated access; it must not perform Palomar's human OAuth authorization. The temporary proof tag and gist are deleted after successful access verification.

The submission access token is a credential. Keep it out of Git, this repository, logs, and public messages. Preserve the private status link or token securely so the review can be retrieved. When verification completes, read the automated review before deciding whether to register.

Registration publishes the immutable repository revision, metadata, and review. The author should read that review and make the final registration decision. Submitting for verification and being registered are distinct outcomes. This repository does not claim either until the corresponding service result is available.

## Current local verification

See `docs/verification.md` for the exact local checks and their limits. The submitted theorem is fully proved. The deliberate `sorry` in `Challenge.lean` is the independent comparison target, and the Solution must contain none.
