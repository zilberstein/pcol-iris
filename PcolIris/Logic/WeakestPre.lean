import PcolIris.Logic.Par
import PcolIris.Logic.LemmaC6
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.Semantics.Invariant
import PcolIris.Semantics.Semantics
import PcolIris.OProp.OProp

namespace Pcol

def wp (𝓘 : Inv) (c : Cmd Act) (ψ : OProp) : OProp :=
  fun 𝓟 ↦
    ∀ (μ : Distr Mem) (𝓟fr : ProbSpace),
      -- The initial distribution `μ` is a refinement of the precondition
      -- `𝓟`, the frame `𝓟fr`, and the invariant `𝓘`
      ((𝓟 ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ) →
      -- Take any `ν` that results from running the program
      ∀ ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 (c.withInv 𝓘).to_pom,
      -- Then `ν` refines some probability space `𝓠`, which satisfies the postcondition `ψ`
        ∃ 𝓠, ((𝓠 ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν) ∧ ψ 𝓠

/-- **The parallel composition rule.**  If the postconditions `ψ₁` and `ψ₂` are precise, then
the weakest preconditions of two threads can be combined with the separating conjunction.

The proof follows the `Par` case of the soundness theorem of the pcOL paper: precision
provides least probability spaces `𝓠₁` and `𝓠₂` satisfying the two postconditions, each
thread is shown to take any frame-respecting refinement of its precondition to a refinement
of `𝓠ₖ`, and the two threads are then combined by `lemma_C6`. -/
lemma wp_par {𝓘 : Inv} {c₁ c₂ : Cmd Act} {ψ₁ ψ₂ : OProp}
    (hψ₁ : ψ₁.Precise) (hψ₂ : ψ₂.Precise) :
    wp 𝓘 c₁ ψ₁ ∗ wp 𝓘 c₂ ψ₂ ⊢ wp 𝓘 (c₁.par c₂) iprop(ψ₁ ∗ ψ₂) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h₁, h₂⟩ μ 𝓟fr hre ν hν
  -- `𝓠₁` and `𝓠₂` are the least probability spaces satisfying `ψ₁` and `ψ₂`
  obtain ⟨𝓠₁, hQ₁⟩ := hψ₁
  obtain ⟨𝓠₂, hQ₂⟩ := hψ₂
  -- We need to somehow prove that `𝓠₁.dom ⊆ 𝓟₁.dom` in order to establish disjointness
  -- of the postconditions
  refine ⟨𝓠₁ ⊗ 𝓠₂, ?_,
    ⟨𝓠₁, 𝓠₂, sorry, le_refl _, (hQ₁ 𝓠₁).mp (le_refl _), (hQ₂ 𝓠₂).mp (le_refl _)⟩⟩
  -- The initial distribution refines the two preconditions, the frame and the invariant
  have hμ : ((𝓟₁ ⊗ 𝓟₂ ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ) :=
    Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left hle)) hre
  -- Each thread, run in isolation with an arbitrary frame, establishes its postcondition;
  -- by precision, the least such postcondition space is `𝓠ₖ`
  have hthread₁ : ∀ (𝓕 : ProbSpace) (μ₁ : Distr Mem),
      ((𝓟₁ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ₁) →
      ∀ ν₁ ∈ ConvexPowerset.singleton' μ₁ >>= 𝓛 (c₁.withInv 𝓘).to_pom,
        ((𝓠₁ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν₁) := by
    intro 𝓕 μ₁ hre₁ ν₁ hν₁
    obtain ⟨𝓠, href, hψ⟩ := h₁ μ₁ 𝓕 hre₁ ν₁ hν₁
    exact Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left ((hQ₁ 𝓠).mpr hψ))) href
  have hthread₂ : ∀ (𝓕 : ProbSpace) (μ₂ : Distr Mem),
      ((𝓟₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ₂) →
      ∀ ν₂ ∈ ConvexPowerset.singleton' μ₂ >>= 𝓛 (c₂.withInv 𝓘).to_pom,
        ((𝓠₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν₂) := by
    intro 𝓕 μ₂ hre₂ ν₂ hν₂
    obtain ⟨𝓠, href, hψ⟩ := h₂ μ₂ 𝓕 hre₂ ν₂ hν₂
    exact Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left ((hQ₂ 𝓠).mpr hψ))) href
  -- The parallel composition is handled by Lemma C.6
  rw [Cmd.withInv, Cmd.to_pom] at hν
  exact lemma_C6 hμ hthread₁ hthread₂ ν hν

end Pcol
