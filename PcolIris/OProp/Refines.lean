/-
Refinement of probability spaces by distributions.

A distribution `ν` refines a space `𝓡` exactly when `𝓡` is below the discrete space of some
representation of `ν` (`ProbSpace.ofPMF`).  This makes it possible to use the laws of the
order on spaces to reason about refinement, e.g. to add to `𝓡` the variables that `ν`
allocates (`Distr.Refines.pad`).
-/
import PcolIris.OProp.TrivialSpace
import PcolIris.OProp.SumLaws

namespace Pcol

open MeasureTheory

/-- Every memory that `ν` gives positive probability owns the variables `D`. -/
def Distr.Owns (ν : Distr Mem) (D : Set Var) : Prop :=
  ∀ m : Mem, ν (m : WithBot Mem) ≠ 0 → D ⊆ m.dom

namespace ProbSpace

/-- The discrete probability space of the distribution `ξ` over outcomes labelled by the
memories `f`, restricted to the variables `D`. -/
noncomputable def ofPMF (ξ : PMF ℕ) (f : ℕ → Mem) (D : Set Var) : ProbSpace where
  mspace := ⊤
  μ := ⟨@PMF.toMeasure ℕ ⊤ ξ, @PMF.toMeasure.isProbabilityMeasure ℕ ⊤ ξ⟩
  dom := D
  state k := open Classical in if D ⊆ (f k).dom then (f k).restrict D else junkMem D
  dom_valid k := by
    classical
    by_cases h : D ⊆ (f k).dom
    · simp only [if_pos h, Mem.restrict_dom]; exact Set.inter_eq_right.mpr h
    · simp only [if_neg h]; exact junkMem_dom D
  complete := ⟨fun _ _ ↦ MeasurableSpace.measurableSet_top⟩

variable {ξ : PMF ℕ} {f : ℕ → Mem} {D : Set Var}

lemma ofPMF_μ (E : Set ℕ) : ((ofPMF ξ f D).μ E : ENNReal) = ξ.toOuterMeasure E := by
  rw [prob_coe]
  exact @PMF.toMeasure_apply_eq_toOuterMeasure_apply ℕ ⊤ ξ E MeasurableSpace.measurableSet_top

lemma support_ofPMF : (ofPMF ξ f D).support = ξ.support := by
  ext n
  rw [mem_support_iff, PMF.mem_support_iff, ← prob_coe, ofPMF_μ,
    PMF.toOuterMeasure_apply_singleton]

lemma ofPMF_state {k : ℕ} (hk : D ⊆ (f k).dom) : (ofPMF ξ f D).state k = (f k).restrict D := by
  classical
  simp only [ofPMF, if_pos hk]

end ProbSpace

namespace Distr

variable {ν : Distr Mem} {𝓡 : ProbSpace} {ξ : PMF ℕ} {f : ℕ → Mem} {D : Set Var}

/-- A refinement, written out with a representation `(ξ, f)` of the distribution and a
relabeling `g`. -/
lemma Refines.le_ofPMF {g : ℕ → ℕ}
    (hμ : ∀ {E}, E ∈ 𝓡 → 𝓡.μ E = ∑' i : ↑(g ⁻¹' E), ξ i)
    (hst : ∀ i ∈ ξ.support, 𝓡.state (g i) ≤ f i)
    (hD : 𝓡.dom ⊆ D) (hf : ∀ k ∈ ξ.support, D ⊆ (f k).dom) :
    𝓡 ≤ ProbSpace.ofPMF ξ f D := by
  refine ⟨g, fun _ _ ↦ MeasurableSpace.measurableSet_top, fun E hE ↦ ?_, hD, fun k hk ↦ ?_⟩
  · refine ENNReal.coe_injective ?_
    rw [ProbSpace.ofPMF_μ, hμ hE, PMF.toOuterMeasure_apply, tsum_subtype]
  · rw [ProbSpace.support_ofPMF] at hk
    rw [ProbSpace.ofPMF_state (hf k hk)]
    exact Mem.le_restrict (hst k hk) ((𝓡.dom_valid _).trans_subset hD)

/-- Conversely, a space below the discrete space of a representation of `ν` is refined by
`ν`. -/
lemma refines_of_le_ofPMF (hle : 𝓡 ≤ ProbSpace.ofPMF ξ f D)
    (hf : ∀ k ∈ ξ.support, D ⊆ (f k).dom) : 𝓡 ≼ ξ.map (some ∘ f) := by
  obtain ⟨g, hg⟩ := hle
  refine ⟨ξ, f, g, fun {E} hE ↦ ?_, fun k hk ↦ ?_, rfl⟩
  · rw [← hg.μ E hE, ProbSpace.ofPMF_μ, PMF.toOuterMeasure_apply, tsum_subtype]
  · have hk' : k ∈ (ProbSpace.ofPMF ξ f D).support := by rwa [ProbSpace.support_ofPMF]
    refine (hg.state k hk').trans ?_
    rw [ProbSpace.ofPMF_state (hf k hk)]
    exact Mem.restrict_le _ _

/-- A distribution that refines `𝓡` allocates the variables of `𝓡`. -/
lemma Refines.owns (h : 𝓡 ≼ ν) : Distr.Owns ν 𝓡.dom := by
  obtain ⟨ξ, f, g, hμ, hst, rfl⟩ := h
  intro m hm
  obtain ⟨k, hk, hkm⟩ : ∃ k ∈ ξ.support, some (f k) = (m : WithBot Mem) := by
    have : (m : WithBot Mem) ∈ (ξ.map (some ∘ f)).support := hm
    rw [PMF.support_map] at this
    exact this
  cases hkm
  rw [← 𝓡.dom_valid (g k)]
  exact Mem.dom_mono (hst k hk)

/-- **Padding.**  If `ν` refines `𝓡` and allocates the variables `U`, then `ν` also refines
`𝓡` together with a space over `U` that carries no probabilistic information (the memories
of `ν`, restricted to `U`). -/
lemma Refines.pad (h : 𝓡 ≼ ν) {U : Set Var} (hU : Distr.Owns ν U) :
    ∃ T : ProbSpace, T.dom = U ∧ ((𝓡 ⊗ T) ≼ ν) := by
  obtain ⟨ξ, f, g, hμ, hst, rfl⟩ := h
  have hf : ∀ k ∈ ξ.support, 𝓡.dom ∪ U ⊆ (f k).dom := by
    intro k hk
    have hk' : (ξ.map (some ∘ f)) (f k : WithBot Mem) ≠ 0 := by
      rw [← PMF.mem_support_iff, PMF.support_map]; exact ⟨k, hk, rfl⟩
    refine Set.union_subset ?_ (hU _ hk')
    rw [← 𝓡.dom_valid (g k)]
    exact Mem.dom_mono (hst k hk)
  have hle := Refines.le_ofPMF hμ hst Set.subset_union_left hf
  have hUZ : U ⊆ (ProbSpace.ofPMF ξ f (𝓡.dom ∪ U)).dom := Set.subset_union_right
  exact ⟨ProbSpace.forget _ U hUZ, rfl,
    refines_of_le_ofPMF (ProbSpace.product_forget_le hle hUZ) hf⟩

end Distr

end Pcol
