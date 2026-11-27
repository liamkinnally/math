# A proof of Written on the Wall II Conjecture 261

This repository gives a Lean proof of the total domination inequality recorded as Graffiti.pc Conjecture 261 in Ermelinda DeLaViña’s *Written on the Wall II*. The catalog records its announcement on February 23, 2007. [UHD catalog](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalog source data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

The source project is at the root of [liamkinnally/math](https://github.com/liamkinnally/math).

## Statement

Let $G$ be a finite simple connected graph of order at least two, let $S=\{v\in V(G):\deg_G(v)=2\}$, and let $N_G(S)$ be the set of vertices adjacent to at least one vertex in $S$. Then

$$
\gamma_t(G)\ \ge\ \frac{2\,|N_G(S)\setminus S|}{L(G)}.
$$

Here $\gamma_t(G)$ is the smallest size of a set $D$ such that every vertex of $G$, including each member of $D$, has a neighbor in $D$. The invariant $L(G)$ is the maximum number of leaves over all spanning trees of $G$, with degrees measured in each tree. The one-vertex graph has no total dominating set and its spanning tree has zero degree-one vertices. On the stated domain the total domination number exists, and the Lean proof establishes that $L(G)>0$.

The compared declaration is `WOW261.conjecture261_ratio` in [Challenge.lean](Challenge.lean) and [Solution.lean](Solution.lean). It states the quotient over $\mathbb Q$ and uses explicit definitions for the degree-two vertices, their distinct external neighbors, degree-one leaves, the maximum over spanning trees, and the minimum total domination size. [Main.lean](Main.lean) also proves the cross-multiplied bound for any total dominating set and specializes it to a minimum set.

## Proof

Write $a=|N_G(S)\setminus S|$, $n=|V(G)|$, $g=\gamma_t(G)$, and $L=L(G)$. The external neighbors are distinct from $S$, and each is incident to an edge from one of the degree-two vertices. Counting these edges gives $a\le 2|S|$ and $a+|S|\le n$, hence $3a\le 2n$.

Start with a spanning tree on each component induced by a minimum total dominating set $D$. Attach each vertex outside $D$ to a chosen neighbor in $D$, then join the resulting forest along edges of $G$ to obtain a spanning tree $T$. The set $D$ still totally dominates $T$, so the degrees of vertices in $D$ sum to at least $n$. If $b$ is the number of leaves outside $D$, the degrees outside $D$ sum to at least $2(n-g)-b$. The full tree degree sum is $2(n-1)$, so $n+2\le b+2g\le L+2g$.

When $L=2$, a three-edge star would extend to a spanning tree with at least three leaves. Thus every degree is at most two, and each external neighbor has degree one and is a leaf of every spanning tree. This gives $2a\le 2L\le gL$. When $L\ge3$ and $g=2$, the bounds $a\le 2|S|$ and $a\le n-|S|$ give $a\le L$ by splitting at $|S|=2$. When $g=3$ and $L=3$, the leaf bound gives $n\le7$, hence $a\le4$ by integrality. When $g=3$ and $L\ge4$, use $6a\le4n\le4(L+4)\le9L$. For $g\ge4$ and $L\ge3$, use $6a\le4n\le4(L+2g-2)\le3gL$. These cases prove $2a\le gL$.

The three-vertex path attains equality. Its degree-two set is the middle vertex, both endpoints are external neighbors, and both $L$ and $\gamma_t$ equal two.

## Provenance and review

The spanning-tree preservation argument has a published antecedent in Lemma 2 of DeLaViña, Liu, Pepper, Waller, and West. Chellali and Haynes proved the tree total-domination lower bound in terms of the order and number of leaves. Together these results imply the supporting estimate $n+2\le L+2g$. This development proves the supporting lemmas in Lean and combines that estimate with the degree-two incidence count to prove the catalog statement. [DeLaViña et al. (2007)](https://www.uhd.edu/documents/academics/sciences/total-dom-2007.pdf) · [Chellali and Haynes (2006)](https://combinatorialpress.com/jcmcc-articles/volume-058/a-note-on-the-total-domination-number-of-a-tree/)

Earlier public computational exploration of the exact #261 inequality appears in Claude Opus 5’s AI Village Graffiti verification toolkit of August 25, 2026. The screening code includes the degree-two external neighborhood and maximum spanning-tree leaf count for #261 and searches for violations on finite graphs. The contemporaneous report names proofs of #37 and #310, and the located material for #261 documents computational screening. A scoped search of related literature and public records located no prior general proof of #261. Priority is unassessed. [AI Village’s pinned toolkit commit](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/commit/a2c26dca5a4c7a2c41586551790207329e685f63) · [AI Village’s August 25 report](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj37-310-true-feb2007-block-closed)

## Build and audit

The project pins Lean `4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. With Elan and Lake available, run the following from the repository root.

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Acyclic \
  Mathlib.Combinatorics.SimpleGraph.Star \
  Mathlib.Algebra.Order.Field.Basic Mathlib.Algebra.Order.Field.Rat
lake build
```

[comparator.json](comparator.json) selects the exact quotient theorem. The Challenge contains one deliberate statement hole for Comparator. The Solution proves the declaration, and the proof development has zero `sorry`. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The ported project passed local Lean compilation and an advisory Comparator replay with Lean, NanoDa, and con-ron. The local nested Bubblewrap launch was unavailable; the full official Palomar workflow at the exact public commit remains required. See [verification details](docs/verification.md) and the [submission procedure](docs/submission.md). The pinned workflow runs automatically on a push to `main` and can also be dispatched manually.

## Credits and license

Liam Kinnally ([liamkinnally](https://github.com/liamkinnally)), a University of Central Florida student, directed and maintains the project in a personal capacity. ChatGPT agents using GPT-6 Astra Pro developed the proof, researched prior work, wrote the Lean formalization and note, and ran verification. Liam also consulted Gemini 4 Hydrogen and shared its prior-work and publication guidance with the ChatGPT agents. Independent human expert review is pending.

The repository is released under [Apache-2.0](LICENSE). [formalization.yaml](formalization.yaml) records the source, scope, review status, and automation details.
