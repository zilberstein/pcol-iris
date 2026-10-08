/-
Probability spaces without probabilistic information.

`ProbSpace.trivialOn V f` has the trivial σ-algebra `{∅, ℕ}`: it only records which memories
(over the variables `V`) are possible, not how likely they are.  Every outcome is in its
support.  Such spaces are the least models of almost sure assertions (`Precise.sure`), and
they are independent of every other space.
-/
import PcolIris.OProp.ProductLaws

namespace Pcol

open MeasureTheory

namespace ProbSpace

/-- The probability space with trivial σ-algebra whose outcome `i` has memory `f i`. -/
noncomputable def trivialOn (V : Set Var) (f : ℕ → Mem) (hf : ∀ i, (f i).dom = V) :
    ProbSpace where
  mspace := ⊥
  μ := ⟨@Measure.dirac ℕ ⊥ 0, @Measure.dirac.isProbabilityMeasure ℕ ⊥ 0⟩
  dom := V
  state := f
  dom_valid := hf
  complete := by
    constructor
    intro s hs
    by_cases hne : s = ∅
    · rw [hne]; exact @MeasurableSet.empty ℕ ⊥
    · exfalso
      obtain ⟨n, hn⟩ := Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨t, hst, ht, ht0⟩ := @exists_measurable_superset_of_null ℕ ⊥ _ s hs
      rcases (@MeasurableSpace.measurableSet_bot_iff ℕ t).mp ht with rfl | rfl
      · exact hst hn
      · rw [measure_univ] at ht0; exact one_ne_zero ht0

variable {V : Set Var} {f : ℕ → Mem} {hf : ∀ i, (f i).dom = V}

lemma trivialOn_measurableSet {E : Set ℕ} (hE : (trivialOn V f hf).mspace.MeasurableSet' E) :
    E = ∅ ∨ E = Set.univ :=
  (@MeasurableSpace.measurableSet_bot_iff ℕ E).mp hE

/-- Every outcome of a space without probabilistic information is possible. -/
lemma support_trivialOn : (trivialOn V f hf).support = Set.univ := by
  refine Set.eq_univ_of_forall fun n ↦ Set.mem_sInter.mpr ?_
  rintro E ⟨hE, h1⟩
  rcases trivialOn_measurableSet hE with rfl | rfl
  · exfalso
    have : ((trivialOn V f hf).μ ∅ : ENNReal) = 0 := by rw [prob_coe]; exact measure_empty
    rw [h1] at this; exact one_ne_zero this
  · exact Set.mem_univ n

/-- A space without probabilistic information is below any space that owns its variables and
whose memories (almost surely) extend memories of the space. -/
lemma trivialOn_le {𝓠 : ProbSpace} (hdom : V ⊆ 𝓠.dom) (g : ℕ → ℕ)
    (hg : ∀ i ∈ 𝓠.support, f (g i) ≤ 𝓠.state i) : trivialOn V f hf ≤ 𝓠 := by
  refine ⟨g, fun E hE ↦ ?_, fun E hE ↦ ?_, hdom, hg⟩
  · rcases trivialOn_measurableSet hE with rfl | rfl
    · exact 𝓠.mspace.measurableSet_empty
    · exact @MeasurableSet.univ ℕ 𝓠.mspace
  · refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    rcases trivialOn_measurableSet hE with rfl | rfl
    · rw [Set.preimage_empty, measure_empty, measure_empty]
    · rw [Set.preimage_univ, measure_univ, measure_univ]

end ProbSpace

end Pcol
