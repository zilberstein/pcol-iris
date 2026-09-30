# Design notes

This development formalizes

> Noam Zilberstein, Alexandra Silva and Joseph Tassarotti.
> *Probabilistic Concurrent Reasoning in Outcome Logic: Independence, Conditioning, and
> Invariants.* POPL 2026. <https://doi.org/10.1145/3776651>

It does not follow the paper literally. This file records the places where the formalization
deliberately departs from the paper, so that they are not mistaken for mistakes.

## Indexed probability spaces

The paper's probability spaces have sample spaces `Ω ⊆ Mem[S]`: the outcomes are memories.
Here, a `ProbSpace` has the fixed sample space `ℕ`, and a separate labelling
`state : ℕ → Mem` assigns a memory to every outcome. This follows indexed-valuation models
such as Amaryllis (Lohse et al., *First Steps Towards Probabilistic Iris*, 2026) and
Oblivious Probabilistic Outcome Logic.

Consequences:

- The summands of an outcome conjunction `⨁` only need disjoint *index* supports, not
  disjoint sets of memories. The branches of a sum are therefore always distinguishable, and
  the partitioning side conditions of the paper (`ψ ⇒ ⌈e ↦ X⌉` in `Split1`, `NSplit1` and
  `Exists`, and in the precision rule for `⨁`) are not needed.
- Outcome conjunctions `⨁[ξ] φ` and `& φ` range over countable index types, so that the
  summands can always be given disjoint sets of outcomes.
- The product `𝓟 ⊗ 𝓠` encodes pairs of outcomes with `Nat.pairEquiv`, so it is commutative
  and associative only up to relabeling. The order `𝓟 ≤ 𝓠` therefore allows a
  measure-preserving relabeling of the outcomes (`ProbSpace.Relabels`), and compares the
  memories only on the support (outcomes of probability zero are irrelevant, as in
  Amaryllis). The laws of `⊗` are in `PcolIris/OProp/ProductLaws.lean`.
- As in the paper, probability spaces are complete, and `⊗` completes its σ-algebra. This
  is what makes `⌈P⌉` agree with the paper's definition (the set of outcomes satisfying `P`
  is measurable with probability 1, `OProp.sure_iff`), so that `P ⊢ Q` implies
  `⌈P⌉ ⊢ ⌈Q⌉`.
- The memory of a product is a left-biased union, so the product is only monotone when
  the factors own disjoint variables. The definitions that combine spaces (`∗`,
  `Framed`) always require this.

## One separating conjunction

The paper has a strong (independent) and a weak separating conjunction `∗w`. Only the strong
one is formalized; the weak one was not useful in practice.

## Weak triples

The paper's weak triples combine the precondition with the frame using the weak combination
`⋄w` (any coupling with the right marginals). Here `wp_weak` instead keeps the independent
product and only quantifies over frames in which every event has probability 0 or 1, i.e.
frames that carry no probabilistic information. This is simpler to work with and suffices for
the `Exists` rule.

## The `Exists` rule

`wp_exists_pure` is the paper's rule: from `&_i ⌈P i⌉ ⊢ wp_weak 𝓘 c ψ` it derives
`⌈∃ i, P i⌉ ⊢ wp_weak 𝓘 c ψ`. The precondition must be a single almost sure assertion. Other
almost sure facts can be merged into it (`⌈P⌉ ∗ ⌈Q⌉ ⊢ ⌈P ∗ Q⌉`), but resources that carry
probabilistic information cannot: as explained in Section 4 of the paper, the case split is
then unsound.

When the postcondition is convex, the outcome conjunction can be eliminated case by case
(`wp_exists_case`, `wp_exists_case_sep`). In the proof mode, the tactic
`iexists_case h [h₁ … hₙ] as i pat using hψ` does all of this. It merges `h : ⌈∃ i, P i⌉` with
the almost sure hypotheses `hⱼ` (`icombine`, through a `CombineSepAs` instance), drops the rest
of the context, and continues with an arbitrary case `i`. In that case, `⌈P i ∗ Q₁ ∗ …⌉` is
destructed with `pat`; an `IntoSep` instance splits it again when the assertions have known
footprints (`MProp.HasFootprint`).

## Weakest preconditions instead of triples

Following Iris, specifications are stated with a weakest-precondition predicate
`wp 𝓘 c ψ : OProp`, and a triple `𝓘 ⊢ ⟨φ⟩ c ⟨ψ⟩` is the entailment `φ ⊢ wp 𝓘 c ψ`
(Definition 5.1). The invariant and the frame are kept as separate factors of the product
that the initial and final distributions refine (`Framed`): the part of the state that
satisfies the invariant is any space `𝓙` with `⌈I⌉ 𝓙`, as in `P ⊨ φ ∗ ⌈I⌉`.

The paper runs programs on memories with a fixed domain. Here memories are partial, so
`wp` states two facts that the paper gets for free:

- the postcondition space owns no variables beyond those of the precondition space
  (`𝓠.dom ⊆ 𝓟.dom`); this is what makes the postconditions of two parallel threads
  independent;
- the program does not deallocate variables (`Distr.Keeps μ ν`: every variable that is
  allocated in all initial memories is allocated in all final memories). The postcondition
  space may be smaller than the precondition space, so without this fact the branches of an
  outcome conjunction could not be brought back to a common domain (`Split`).

## Invariants

Invariants are ordered by factorization (`Inv.LE_Inv`): `𝓘 ≤ 𝓙` when `𝓘` is `𝓙 ∗ 𝓚` for
some invariant `𝓚` on the other variables. This is the order along which
invariant-sensitive execution is monotone (Lemma 5.3, stated in the paper for `I ∗ J`); a
mere projection order would let other threads break the correlations that `𝓘` imposes.

## Mixtures with a lower bound

The paper's `φ ⊕≥p ψ` (`OProp.oplusGe`) is a mixture whose weights are any distribution on
`Bool` giving `φ` probability at least `p`, rather than a Bernoulli distribution with a
rational parameter `q ≥ p`: a countable mixture of such mixtures may give `φ` an irrational
probability, and `⊕≥p` must be convex for the `NSplit2` rule. No partitioning side
condition is needed for convexity (Lemma E.6), since the branches of a sum are
distinguishable.

In `BoundedRank` (`wp_bounded_rank`), the second branch of the premise's postcondition allows
any rank, not only ranks at least `N`. This makes the rule stronger, and it remains sound,
since from any rank the loop exits with probability at least `p ^ (h - ℓ)`. As in the paper,
the rule is stated for weak triples; the strong triple follows with `wp_strengthen`, since
the postcondition is precise.

## Precision

`Precise` follows Definition 4.1: if an assertion is satisfiable, it has a least model.
`⌈P⌉` is precise when `P` has a finite footprint (`MProp.Footprint`); in the paper this is
implicit, since `⌈P⌉` is interpreted over the variables of `P`. Its least model is a space
without probabilistic information (`ProbSpace.trivialOn`).

## Expressions

Expressions are shallowly embedded as functions `Mem → Option Val`, which need not be
monotone in the memory. The atomic assertions `own e`, `e₁ == e₂` and `e₁ <= e₂` are
therefore defined as upward closures (`MProp.upClose`); for monotone expressions
(`Expr.Mono`, e.g. variables and literals) this is the expected pointwise meaning
(`Expr.equals_iff`, `MProp.own_iff`).

Expressions read by the assignment and sampling rules must moreover be *local*
(`Expr.Local`): monotone, and still defined after a variable is assigned. The first
property makes the value known in the precondition survive interference on the invariant's
variables; the second makes `own e` survive the assignment. Both hold of expressions built
from variables, literals and arithmetic.

## Logical variables

Logical variables and the context `Γ` are not modelled syntactically; they are ordinary Lean
variables (a shallow embedding), so substitution lemmas are not needed.

## Iris proof mode

`OProp` and `MProp` are given `Iris.BI` instances so that the Iris proof mode can be used. The
paper has no magic wand, persistence modality or later modality; they are added here only to
satisfy the `BI` interface:

- the wand is the standard one for upward-closed predicates,
  `∀ 𝓟₁ disjoint, φ 𝓟₁ → ψ (𝓟 ⊗ 𝓟₁)`,
- `<pers> φ` holds when `φ` holds of the unit resource (the empty memory, resp. the space
  `ProbSpace.unit` with no variables and no information),
- `▷ φ` is `φ`, and the COFE structure is discrete.
