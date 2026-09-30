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

/-! ### Independence of spaces without probabilistic information -/

/-- A space without probabilistic information is independent of every other space: if `X` is
below `Z`, and the memories of `T` are (almost surely) restrictions of those of `Z` to other
variables, then `X ⊗ T` is below `Z`. -/
theorem product_trivialOn_le {X Z : ProbSpace} (hX : X ≤ Z) (hU : V ⊆ Z.dom) (t : ℕ → ℕ)
    (ht : ∀ k ∈ Z.support, f (t k) ≤ Z.state k) : (X ⊗ trivialOn V f hf) ≤ Z := by
  obtain ⟨g, hg⟩ := hX
  haveI := isProbabilityMeasure_meas X
  haveI := isProbabilityMeasure_meas (trivialOn V f hf)
  have hgm : @Measurable ℕ ℕ Z.mspace X.mspace g := fun E hE ↦ hg.mspace E hE
  have htm : @Measurable ℕ ℕ Z.mspace (trivialOn V f hf).mspace t := by
    intro s hs
    rcases trivialOn_measurableSet hs with rfl | rfl
    · exact Z.mspace.measurableSet_empty
    · exact @MeasurableSet.univ ℕ Z.mspace
  have hmeas : @Measurable ℕ (ℕ × ℕ) Z.mspace (X.mspace.prod (trivialOn V f hf).mspace)
      (fun k ↦ (g k, t k)) :=
    @Measurable.prodMk ℕ Z.mspace ℕ ℕ X.mspace (trivialOn V f hf).mspace g t hgm htm
  have hmap : MP Z.mspace (X.mspace.prod (trivialOn V f hf).mspace) (fun k ↦ (g k, t k))
      Z.meas (@Measure.prod ℕ ℕ X.mspace (trivialOn V f hf).mspace X.meas
        (trivialOn V f hf).meas) := by
    refine @MeasurePreserving.mk ℕ (ℕ × ℕ) Z.mspace (X.mspace.prod (trivialOn V f hf).mspace)
      _ _ _ hmeas ?_
    symm
    refine @ext_of_generate_finite _ (X.mspace.prod (trivialOn V f hf).mspace) _ _
      (Set.image2 (fun x1 x2 ↦ x1 ×ˢ x2) {s | @MeasurableSet ℕ X.mspace s}
        {t | @MeasurableSet ℕ (trivialOn V f hf).mspace t})
      (@generateFrom_prod ℕ ℕ X.mspace (trivialOn V f hf).mspace).symm
      (@isPiSystem_prod ℕ ℕ X.mspace (trivialOn V f hf).mspace) inferInstance ?_ ?_
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [@Measure.map_apply ℕ (ℕ × ℕ) Z.mspace (X.mspace.prod (trivialOn V f hf).mspace)
        Z.meas _ hmeas _ (@MeasurableSet.prod ℕ ℕ X.mspace (trivialOn V f hf).mspace A B hA hB),
        @Measure.prod_prod ℕ ℕ X.mspace (trivialOn V f hf).mspace X.meas _ _ A B]
      rcases trivialOn_measurableSet (V := V) (f := f) (hf := hf) hB with rfl | rfl
      · simp
      · rw [measure_univ, mul_one, Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]
        exact (hg.measurePreserving.measure_preimage
          (@MeasurableSet.nullMeasurableSet ℕ X.mspace X.meas A hA)).symm
    · rw [@Measure.map_apply ℕ (ℕ × ℕ) Z.mspace (X.mspace.prod (trivialOn V f hf).mspace)
        Z.meas _ hmeas _ MeasurableSet.univ, Set.preimage_univ, measure_univ, measure_univ]
  refine ⟨fun k ↦ Nat.pairEquiv (g k, t k),
    relabels_of_measurePreserving (IsCompletionOf.product X (trivialOn V f hf))
      ((measurePreserving_pair X _).comp hmap) (Set.union_subset hg.dom hU) ?_⟩
  intro k hk
  rw [product_state, Equiv.symm_apply_apply]
  exact Mem.union_le (hg.state k hk) (ht k hk)

/-- The part of `Z` over the variables `U`, forgetting all probabilistic information: its
memories are the (possible) memories of `Z`, restricted to `U`. -/
noncomputable def forget (Z : ProbSpace) (U : Set Var) (hU : U ⊆ Z.dom) : ProbSpace :=
  open Classical in
  trivialOn U
    (fun k ↦ (Z.state (if k ∈ Z.support then k else (support_nonempty Z).some)).restrict U)
    (fun k ↦ by rw [Mem.restrict_dom, Z.dom_valid]; exact Set.inter_eq_right.mpr hU)

lemma forget_state_restrict (Z : ProbSpace) {U : Set Var} (hU : U ⊆ Z.dom) (k : ℕ) :
    ∃ k' ∈ Z.support, (forget Z U hU).state k = (Z.state k').restrict U := by
  classical
  by_cases hk : k ∈ Z.support
  · exact ⟨k, hk, by simp only [forget, trivialOn, if_pos hk]⟩
  · exact ⟨_, (support_nonempty Z).some_mem, by simp only [forget, trivialOn, if_neg hk]⟩

lemma forget_state_of_mem (Z : ProbSpace) {U : Set Var} (hU : U ⊆ Z.dom) {k : ℕ}
    (hk : k ∈ Z.support) : (forget Z U hU).state k = (Z.state k).restrict U := by
  classical
  simp only [forget, trivialOn, if_pos hk]

lemma support_forget (Z : ProbSpace) {U : Set Var} (hU : U ⊆ Z.dom) :
    (forget Z U hU).support = Set.univ := support_trivialOn

lemma forget_le (Z : ProbSpace) {U : Set Var} (hU : U ⊆ Z.dom) : forget Z U hU ≤ Z :=
  trivialOn_le hU id fun k hk ↦ by
    change (forget Z U hU).state k ≤ _
    rw [forget_state_of_mem Z hU hk]; exact Mem.restrict_le _ _

lemma product_forget_le {X Z : ProbSpace} (hX : X ≤ Z) {U : Set Var} (hU : U ⊆ Z.dom) :
    (X ⊗ forget Z U hU) ≤ Z :=
  product_trivialOn_le hX hU id fun k hk ↦ by
    change (forget Z U hU).state k ≤ _
    rw [forget_state_of_mem Z hU hk]; exact Mem.restrict_le _ _

end ProbSpace

end Pcol
