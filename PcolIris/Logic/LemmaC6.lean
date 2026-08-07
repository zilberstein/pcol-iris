/-
Lemma C.6 of

  Noam Zilberstein, Alexandra Silva and Joseph Tassarotti,
  *Probabilistic Concurrent Reasoning in Outcome Logic: Independence, Conditioning, and
  Invariants*, POPL 2026.

This is the semantic core of the parallel composition rule `wp_par`: if each thread, run on
its own, transforms a precondition space into a postcondition space (while preserving an
arbitrary frame and the invariant), then the parallel composition of the two threads
transforms the product of the preconditions into the product of the postconditions.
-/
import PcolIris.Logic.Par
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.Semantics.Invariant

namespace Pcol

open Linearization

/-- **Lemma C.6.**  Let `p₁` and `p₂` be the pomsets of two threads that run under the
invariant `𝓘`, and let `μ` be an initial distribution refining `𝓟₁ ⊗ 𝓟₂ ⊗ 𝓟fr ⊗ 𝓘`.  If,
for an arbitrary frame `𝓕`, running thread `k` on any distribution refining
`𝓟ₖ ⊗ 𝓕 ⊗ 𝓘` yields a distribution refining `𝓠ₖ ⊗ 𝓕 ⊗ 𝓘`, then running the two threads in
parallel on `μ` yields a distribution refining `𝓠₁ ⊗ 𝓠₂ ⊗ 𝓟fr ⊗ 𝓘`.

The side conditions of the original statement (each thread only acts on the variables it
owns, and only tests its own variables) are replaced here by the requirement that the two
premises hold for *every* frame `𝓕`; this is exactly the information that the definition of
`wp` provides, and it is what makes the two threads independent.

The bracketing of the products is chosen to match the one used by `wp`: `ProbSpace.product`
is not associative on the nose (the order on `ProbSpace` compares the `state` functions
pointwise, and the two bracketings encode pairs of samples differently), so probability
spaces have to be combined in exactly the same order everywhere.

The proof is not yet formalised.  Its main probabilistic ingredient, the multiplicativity of
the worst-case probabilities of two threads (`Pcol.Pom.par_comp`, Lemma C.5), is available in
`PcolIris/Logic/Par.lean`; what is still missing is the transfer between probability spaces
and distributions, which needs the (currently unfinished) definitions of
`ProbSpace.trivial` and `ProbSpace.sum` in `PcolIris/OProp/ProbSpace.lean`. -/
theorem lemma_C6 {𝓘 : Inv} {p₁ p₂ : Pom (Label (WithInv Act) Test)}
    {𝓟₁ 𝓟₂ 𝓠₁ 𝓠₂ 𝓟fr : ProbSpace} {μ : Distr Mem}
    (hμ : ((𝓟₁ ⊗ 𝓟₂ ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ))
    (h₁ : ∀ (𝓕 : ProbSpace) (μ₁ : Distr Mem),
      ((𝓟₁ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ₁) →
      ∀ ν₁ ∈ ConvexPowerset.singleton' μ₁ >>= 𝓛 p₁,
        ((𝓠₁ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν₁))
    (h₂ : ∀ (𝓕 : ProbSpace) (μ₂ : Distr Mem),
      ((𝓟₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ₂) →
      ∀ ν₂ ∈ ConvexPowerset.singleton' μ₂ >>= 𝓛 p₂,
        ((𝓠₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν₂)) :
    ∀ ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 (Pom.Semantics.par p₁ p₂),
      ((𝓠₁ ⊗ 𝓠₂ ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν) := by
  sorry

end Pcol
