# Written on the Wall II Conjecture 261 is true

This repository contains a proof and Lean formalization of [Graffiti.pc Conjecture 261](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html), from Ermelinda DeLaViña’s *Written on the Wall II*.

Liam Kinnally (2026). [*A proof of Written on the Wall II Conjecture 261*](https://doi.org/10.5281/zenodo.24607995). Zenodo preprint.

The formalization is registered as **[PALOMAR-2026-11-27-000022, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-27-000022&version=1)**. The entry records the exact source snapshot and its verification evidence.

## Statement

Let $G$ be a finite simple connected graph with at least two vertices, and let

```math
S=\{v\in V(G):\deg_G(v)=2\}.
```

Then

```math
\gamma_t(G)\ge\frac{2\,|N_G(S)\setminus S|}{L_s(G)},
```

where:

- $\gamma_t(G)$ is the total domination number: the smallest size of a set $D$ such that every vertex, including each vertex in $D$, has a neighbor in $D$.
- $N_G(S)$ is the set of vertices adjacent to at least one vertex in $S$, so $N_G(S)\setminus S$ counts distinct neighbors outside $S$.
- $L_s(G)$ is the maximum number of leaves over all spanning trees of $G$, with degrees measured in each tree. This is the invariant denoted by $L(G)$ in the catalog entry.

The order condition makes both sides well-defined: a singleton has no total dominating set, and its spanning tree has no degree-one leaves.

## Proof

Write

```math
a=|N_G(S)\setminus S|,\qquad n=|V(G)|,\qquad
g=\gamma_t(G),\qquad L=L_s(G).
```

Since $G$ is connected and $n\ge2$, both $g$ and $L$ are at least two. It suffices to prove $2a\le gL$.

### 1. Count the external neighbors

Each vertex of $S$ has two neighbors, so $a\le2|S|$. The external neighbors lie outside $S$, so $a+|S|\le n$. Combining these bounds gives

```math
3a\le2n.
```

### 2. Preserve total domination in a spanning tree

Let $D$ be a minimum total dominating set, with $|D|=g$. Every component of the induced graph $G[D]$ has at least two vertices. Choose a spanning tree of each component, then attach each vertex outside $D$ to one of its neighbors in $D$. Finally, join the resulting forest using edges of $G$ to obtain a spanning tree $T$.

Every vertex still has a neighbor in $D$, so $D$ totally dominates $T$. Consequently,

```math
\sum_{v\in D}\deg_T(v)\ge n.
```

If $b$ vertices outside $D$ are leaves of $T$, the remaining vertices outside $D$ have degree at least two. Thus

```math
\sum_{v\notin D}\deg_T(v)\ge2(n-g)-b.
```

The total degree sum of $T$ is $2(n-1)$. Adding the two inequalities and using $b\le L$ gives

```math
n+2\le b+2g\le L+2g.
```

This supporting bound also follows from Lemma 2 of [DeLaViña, Liu, Pepper, Waller, and West (2007)](https://www.uhd.edu/documents/academics/sciences/total-dom-2007.pdf), which preserves the total domination number in a spanning tree, together with the tree leaf bound of [Chellali and Haynes (2006)](https://combinatorialpress.com/jcmcc-articles/volume-058/a-note-on-the-total-domination-number-of-a-tree/). The degree count above gives a direct proof.

### 3. Handle the case $L=2$

If a vertex had degree at least three, a three-edge star at that vertex could be extended to a spanning tree with at least three leaves. Therefore every vertex has degree at most two.

Each vertex in $N_G(S)\setminus S$ has positive degree and is outside the degree-two set, so it has degree one. Its edge belongs to every spanning tree. Hence $a\le L$, and

```math
2a\le2L\le gL.
```

### 4. Handle the cases $L\ge3$

**If $g=2$**, the spanning-tree bound gives $n\le L+2$. When $|S|\ge2$, we have $a\le n-|S|\le L$. When $|S|<2$, we have $a\le2|S|\le2\le L$. Either way, $2a\le2L=gL$.

**If $g=3$ and $L=3$**, then $n\le7$. Since $3a\le2n\le14$ and $a$ is an integer, $a\le4$, giving $2a\le8<9=gL$.

**If $g=3$ and $L\ge4$**, then

```math
6a\le4n\le4(L+4)\le9L=3gL.
```

**If $g\ge4$ and $L\ge3$**, then

```math
6a\le4n\le4(L+2g-2)\le3gL,
```

where the last inequality follows from

```math
3gL-4(L+2g-2)=(3g-4)(L-3)+(g-4)\ge0.
```

These cases exhaust the possibilities and prove $2a\le gL$.

## Sharpness

The path $P_3$ attains equality. Its middle vertex is the only member of $S$, and its two endpoints are the external neighbors. Thus

```math
|N_G(S)\setminus S|=2,\qquad L_s(P_3)=2,\qquad\gamma_t(P_3)=2,
```

so both sides of the conjectured inequality equal two.

## Formal verification

The compared theorem is `WOW261.conjecture261_ratio`. [Challenge.lean](Challenge.lean) states the quotient inequality over $\mathbb Q$ with explicit graph definitions; [Solution.lean](Solution.lean) imports the completed proof. [Main.lean](Main.lean) also proves the cross-multiplied bound for any total dominating set and specializes it to a minimum set.

Palomar registered commit [`551b13e8ce5c1b4b17b18e638cb8d86f27a98718`](https://github.com/liamkinnally/math/tree/551b13e8ce5c1b4b17b18e638cb8d86f27a98718). Its [official mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45960291320) passed with Lean, nanoda, and con-ron, using only `propext`, `Classical.choice`, and `Quot.sound`. The proof contains no `sorry`; the independent Challenge has the deliberate statement hole required for comparison.

The registered snapshot remains available separately from later documentation changes on `main`. See the [registration record](docs/submission.md) and [verification details](docs/verification.md) for the public evidence and reproduction commands.

### Build

The project pins Lean `4.35.0` and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. With Elan and Lake installed, run these commands from the repository root:

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Acyclic \
  Mathlib.Combinatorics.SimpleGraph.Star \
  Mathlib.Algebra.Order.Field.Basic Mathlib.Algebra.Order.Field.Rat
lake build
```

## Prior work and scope

The supporting spanning-tree and leaf bounds above are known results. This proof combines them with the degree-two neighborhood count and the small cases to establish Conjecture 261.

Earlier computational exploration of the exact inequality appears in the [AI Village Graffiti verification toolkit](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/commit/a2c26dca5a4c7a2c41586551790207329e685f63), dated August 25, 2026. The located material screens #261 on finite graphs; the [accompanying report](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj37-310-true-feb2007-block-closed) discusses proofs of #37 and #310.

A scoped search found no earlier general proof of #261. That does not establish historical priority. Palomar registration records formal verification and automated review. No independent human expert review has been recorded.

## Credits

Liam Kinnally directed the project and continues to maintain it. As the sole human author of the preprint, he checked its claims against the mathematical argument, the cited sources, and the formal verification reports.

Under his direction, ChatGPT agents using GPT-6 Astra Pro developed the argument, researched prior work, wrote the Lean formalization and manuscript, and ran the verification checks. Kinnally consulted Gemini 4 Hydrogen on prior work and publication. Opus 5.5 later reviewed the manuscript.

[Provenance](formalization.yaml) · [Apache-2.0 license](LICENSE)
