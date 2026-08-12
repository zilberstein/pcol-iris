/-
Basic order-theoretic properties of probability spaces and of the refinement relation
between distributions and probability spaces.

These are the structural ingredients that are needed to combine the two threads of a
parallel composition: refinement is antitone in the probability space, and the product
of probability spaces is monotone in each argument.
-/
import PcolIris.OProp.ProbSpace

namespace Pcol

open MeasureTheory MeasurableSpace

namespace ProbSpace

/-! ### Products of measurable spaces and of measures -/

/-- The product of measurable spaces is monotone in its left argument. -/
lemma prod_le_prod_left {m m' n : MeasurableSpace ℕ} (hle : m ≤ m') :
    (m.prod n) ≤ (m'.prod n) := by
  unfold MeasurableSpace.prod
  exact sup_le_sup_right (comap_mono hle) _

/-- The product of measurable spaces is monotone in its right argument. -/
lemma prod_le_prod_right {m n n' : MeasurableSpace ℕ} (hle : n ≤ n') :
    (m.prod n) ≤ (m.prod n') := by
  unfold MeasurableSpace.prod
  exact sup_le_sup_left (comap_mono hle) _

/-- Two product measures whose left factors agree on a coarser σ-algebra agree on the
product of that σ-algebra with the σ-algebra of the (common) right factor. -/
lemma prod_measure_eq_left {m m' n : MeasurableSpace ℕ} (hle : m ≤ m')
    (μ : @Measure ℕ m) (μ' : @Measure ℕ m') (ν : @Measure ℕ n)
    [hμ : @IsProbabilityMeasure ℕ m μ] [hμ' : @IsProbabilityMeasure ℕ m' μ']
    [hν : @IsProbabilityMeasure ℕ n ν]
    (h : ∀ E, m.MeasurableSet' E → μ E = μ' E) :
    ∀ F, (m.prod n).MeasurableSet' F →
      (@Measure.prod ℕ ℕ m n μ ν) F = (@Measure.prod ℕ ℕ m' n μ' ν) F := by
  have hpr := prod_le_prod_left (n := n) hle
  have hrect : ∀ (s t : Set ℕ), @MeasurableSet ℕ m s → @MeasurableSet ℕ n t →
      @MeasurableSet (ℕ × ℕ) (m.prod n) (s ×ˢ t) :=
    fun s t hs ht ↦ @MeasurableSet.prod ℕ ℕ m n s t hs ht
  have hpp : ∀ (s t : Set ℕ), (@Measure.prod ℕ ℕ m n μ ν) (s ×ˢ t) = μ s * ν t :=
    fun s t ↦ @Measure.prod_prod ℕ ℕ m n μ ν inferInstance s t
  have hpp' : ∀ (s t : Set ℕ), (@Measure.prod ℕ ℕ m' n μ' ν) (s ×ˢ t) = μ' s * ν t :=
    fun s t ↦ @Measure.prod_prod ℕ ℕ m' n μ' ν inferInstance s t
  have key : (@Measure.prod ℕ ℕ m n μ ν) = (@Measure.prod ℕ ℕ m' n μ' ν).trim hpr := by
    refine @ext_of_generate_finite _ (m.prod n) _ _
      (Set.image2 (fun x1 x2 ↦ x1 ×ˢ x2) {s | @MeasurableSet ℕ m s} {t | @MeasurableSet ℕ n t})
      (@generateFrom_prod ℕ ℕ m n).symm (@isPiSystem_prod ℕ ℕ m n) inferInstance ?_ ?_
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      rw [hpp, trim_measurableSet_eq hpr (hrect s t hs ht), hpp', h s hs]
    · rw [trim_measurableSet_eq hpr MeasurableSet.univ, measure_univ, measure_univ]
  intro F hF
  rw [key, trim_measurableSet_eq hpr hF]

/-- Two product measures whose right factors agree on a coarser σ-algebra agree on the
product of the σ-algebra of the (common) left factor with that σ-algebra. -/
lemma prod_measure_eq_right {m n n' : MeasurableSpace ℕ} (hle : n ≤ n')
    (μ : @Measure ℕ m) (ν : @Measure ℕ n) (ν' : @Measure ℕ n')
    [hμ : @IsProbabilityMeasure ℕ m μ] [hν : @IsProbabilityMeasure ℕ n ν]
    [hν' : @IsProbabilityMeasure ℕ n' ν']
    (h : ∀ E, n.MeasurableSet' E → ν E = ν' E) :
    ∀ F, (m.prod n).MeasurableSet' F →
      (@Measure.prod ℕ ℕ m n μ ν) F = (@Measure.prod ℕ ℕ m n' μ ν') F := by
  have hpr := prod_le_prod_right (m := m) hle
  have hrect : ∀ (s t : Set ℕ), @MeasurableSet ℕ m s → @MeasurableSet ℕ n t →
      @MeasurableSet (ℕ × ℕ) (m.prod n) (s ×ˢ t) :=
    fun s t hs ht ↦ @MeasurableSet.prod ℕ ℕ m n s t hs ht
  have hpp : ∀ (s t : Set ℕ), (@Measure.prod ℕ ℕ m n μ ν) (s ×ˢ t) = μ s * ν t :=
    fun s t ↦ @Measure.prod_prod ℕ ℕ m n μ ν inferInstance s t
  have hpp' : ∀ (s t : Set ℕ), (@Measure.prod ℕ ℕ m n' μ ν') (s ×ˢ t) = μ s * ν' t :=
    fun s t ↦ @Measure.prod_prod ℕ ℕ m n' μ ν' inferInstance s t
  have key : (@Measure.prod ℕ ℕ m n μ ν) = (@Measure.prod ℕ ℕ m n' μ ν').trim hpr := by
    refine @ext_of_generate_finite _ (m.prod n) _ _
      (Set.image2 (fun x1 x2 ↦ x1 ×ˢ x2) {s | @MeasurableSet ℕ m s} {t | @MeasurableSet ℕ n t})
      (@generateFrom_prod ℕ ℕ m n).symm (@isPiSystem_prod ℕ ℕ m n) inferInstance ?_ ?_
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      rw [hpp, trim_measurableSet_eq hpr (hrect s t hs ht), hpp', h t ht]
    · rw [trim_measurableSet_eq hpr MeasurableSet.univ, measure_univ, measure_univ]
  intro F hF
  rw [key, trim_measurableSet_eq hpr hF]

/-! ### Application of the product measure -/

lemma pairEquiv_aemeasurable (p q : ProbSpace) :
    @AEMeasurable (ℕ × ℕ) ℕ ((p.mspace.prod q.mspace).map Nat.pairEquiv)
      (p.mspace.prod q.mspace) (⇑Nat.pairEquiv)
      (@ProbabilityMeasure.toMeasure (ℕ × ℕ) (p.mspace.prod q.mspace)
        (@ProbabilityMeasure.prod ℕ p.mspace ℕ q.mspace p.μ q.μ)) := by
  apply @Measurable.aemeasurable _ _
    (p.mspace.prod q.mspace) ((p.mspace.prod q.mspace).map Nat.pairEquiv) _ _
  exact measurable_iff_le_map.mpr fun s a ↦ a

/-- Values of a probability measure, viewed in `ℝ≥0∞`. -/
lemma prob_coe {α : Type*} {m : MeasurableSpace α} (P : @ProbabilityMeasure α m) (s : Set α) :
    ((P s : NNReal) : ENNReal) = @ProbabilityMeasure.toMeasure α m P s :=
  ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P s

lemma prod_coe_apply (p q : ProbSpace) (s : Set (ℕ × ℕ)) :
    (((@ProbabilityMeasure.prod ℕ p.mspace ℕ q.mspace p.μ q.μ) s : NNReal) : ENNReal) =
      (@Measure.prod ℕ ℕ p.mspace q.mspace
        (@ProbabilityMeasure.toMeasure ℕ p.mspace p.μ)
        (@ProbabilityMeasure.toMeasure ℕ q.mspace q.μ)) s :=
  @prob_coe (ℕ × ℕ) (p.mspace.prod q.mspace) _ s

/-- The measure of a product space is the product measure of the preimage under the
pairing bijection.  Since the measure of a product space is the completion of the pushforward
of the product measure, this holds for every set, measurable or not. -/
lemma product_μ_apply (p q : ProbSpace) (E : Set ℕ) :
    (p ⊗ q).μ E =
      (@ProbabilityMeasure.prod ℕ p.mspace ℕ q.mspace p.μ q.μ) (⇑Nat.pairEquiv ⁻¹' E) := by
  refine ENNReal.coe_injective ?_
  rw [prob_coe, prod_coe_apply, ← prodMeasure_apply p q E]
  rfl

/-- Two products whose left factors agree on the coarser σ-algebra have the same underlying
(uncompleted) product measure there. -/
lemma prodMeasure_agree_left {p p' q : ProbSpace} (h : p ≤ p') (E : Set ℕ)
    (hE : (prodMSpace p q).MeasurableSet' E) : prodMeasure p q E = prodMeasure p' q E := by
  rw [prodMeasure_apply, prodMeasure_apply]
  refine prod_measure_eq_left h.mspace _ _ _ (fun F hF ↦ ?_) _ hE
  rw [← @prob_coe ℕ p.mspace p.μ F, ← @prob_coe ℕ p'.mspace p'.μ F, h.μ F hF]

/-- Two products whose right factors agree on the coarser σ-algebra have the same underlying
(uncompleted) product measure there. -/
lemma prodMeasure_agree_right {p q q' : ProbSpace} (h : q ≤ q') (E : Set ℕ)
    (hE : (prodMSpace p q).MeasurableSet' E) : prodMeasure p q E = prodMeasure p q' E := by
  rw [prodMeasure_apply, prodMeasure_apply]
  refine prod_measure_eq_right h.mspace _ _ _ (fun F hF ↦ ?_) _ hE
  rw [← @prob_coe ℕ q.mspace q.μ F, ← @prob_coe ℕ q'.mspace q'.μ F, h.μ F hF]

/-! ### Monotonicity of the product of probability spaces -/

/-! ### The state of a product is not monotone

The two `sorry`s below are unavoidable: the remaining goal, monotonicity of the `state`
component, is false in general, because `Mem.union` is left-biased and hence not monotone in
its left argument.  Enlarging the left factor of a product may make it disagree with the
right factor at a variable that was previously undefined on the left, and there the product
changes its value instead of only becoming more defined.  This is witnessed formally by
`product_not_mono_left` below. -/

/-- The probability space concentrated at `0` whose memory is `σ` at every point. -/
noncomputable def constSpace (σ : Mem) : ProbSpace where
  mspace := ⊤
  μ := ⟨@Measure.dirac ℕ ⊤ 0, @Measure.dirac.isProbabilityMeasure ℕ ⊤ 0⟩
  dom := σ.dom
  state _ := σ
  dom_valid _ := rfl
  complete := ⟨fun _ _ ↦ by trivial⟩

/-- The product of probability spaces is *not* monotone in its left argument. -/
lemma product_not_mono_left :
    ∃ p p' q : ProbSpace, p ≤ p' ∧ ¬ ((p ⊗ q) ≤ (p' ⊗ q)) := by
  refine ⟨constSpace Mem.emp, constSpace (fun _ ↦ some 2), constSpace (fun _ ↦ some 1),
    ⟨le_refl _, fun _ _ ↦ rfl, ?_, fun _ _ ↦ _root_.trivial⟩, ?_⟩
  · intro x hx
    exact absurd rfl hx
  · intro hle
    have hst := hle.state 0
    have hx := hst "x"
    simp [product, constSpace, Mem.union, Mem.emp] at hx

/-- The product of probability spaces is monotone in its left argument. -/
lemma product_mono_left {p p' q : ProbSpace} (h : p ≤ p') : (p ⊗ q) ≤ (p' ⊗ q) := by
  refine ⟨completeMSpace_mono (MeasurableSpace.map_mono (prod_le_prod_left h.mspace))
    (prodMeasure_agree_left h), ?_, ?_, ?_⟩
  · intro E hE
    refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    exact completeMeasure_agree (prodMeasure_agree_left h) hE
  · exact Set.union_subset_union h.dom (Set.Subset.refl _)
  · intro i x
    simp only [product, Nat.pairEquiv_apply, Nat.pairEquiv_symm_apply, Mem.union]
    sorry

/-- The product of probability spaces is monotone in its right argument. -/
lemma product_mono_right {p q q' : ProbSpace} (h : q ≤ q') : (p ⊗ q) ≤ (p ⊗ q') := by
  refine ⟨completeMSpace_mono (MeasurableSpace.map_mono (prod_le_prod_right h.mspace))
    (prodMeasure_agree_right h), ?_, ?_, ?_⟩
  · intro E hE
    refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    exact completeMeasure_agree (prodMeasure_agree_right h) hE
  · exact Set.union_subset_union (Set.Subset.refl _) h.dom
  · intro i x; sorry

/-- The product of probability spaces is monotone. -/
lemma product_mono {p p' q q' : ProbSpace} (h₁ : p ≤ p') (h₂ : q ≤ q') :
    (p ⊗ q) ≤ (p' ⊗ q') :=
  le_trans (product_mono_left h₁) (product_mono_right h₂)

/-! ### Reindexing the summands of a sum -/

/--
Reindexing the summands of a `ProbSpace.sum` along a bijection of the index type that
preserves the weights does not change the sum.

Only the inequality is stated (which is all that is needed downstream, and avoids the
dependent equality of the `μ` fields); the two sums are in fact equal.
-/
lemma sum_reindex_le {ι : Type} (ξ : PMF ι) (e : ι ≃ ι) (hξ : ∀ i, ξ (e i) = ξ i)
    (𝓠 : ι → ProbSpace) (V : Set Var)
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓠 i).support (𝓠 j).support)
    (hdom : ∀ i, (𝓠 i).dom = V)
    (h' : ∀ {i j : ι}, i ≠ j → Disjoint (𝓠 (e.symm i)).support (𝓠 (e.symm j)).support)
    (hdom' : ∀ i, (𝓠 (e.symm i)).dom = V) :
    sum ξ (fun i ↦ 𝓠 (e.symm i)) V h' hdom' ≤ sum ξ 𝓠 V h hdom := by
  classical
  have hmeas : ∀ E : Set ℕ, (sumMSpace ξ fun i ↦ 𝓠 (e.symm i)).MeasurableSet' E →
      (sumMSpace ξ 𝓠).MeasurableSet' E := by
    intro E hE j hj
    have := hE (e j) (by rw [hξ]; exact hj)
    simpa only [Equiv.symm_apply_apply] using this
  refine ⟨hmeas, ?_, Set.Subset.refl _, ?_⟩
  · intro E hE
    refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    change sumMeasure ξ (fun i ↦ 𝓠 (e.symm i)) E = sumMeasure ξ 𝓠 E
    rw [sumMeasure_apply _ _ hE, sumMeasure_apply _ _ (hmeas E hE)]
    refine Eq.trans (Eq.symm (e.tsum_eq (fun i ↦ ξ i *
      (@ProbabilityMeasure.toMeasure ℕ (𝓠 (e.symm i)).mspace (𝓠 (e.symm i)).μ)
        (E ∩ (𝓠 (e.symm i)).support)))) ?_
    exact tsum_congr fun j ↦ by rw [hξ, Equiv.symm_apply_apply]
  · intro n
    change sumState (fun i ↦ 𝓠 (e.symm i)) V n ≤ sumState 𝓠 V n
    unfold sumState
    by_cases hex : ∃ i, n ∈ (𝓠 (e.symm i)).support
    · have hex' : ∃ j, n ∈ (𝓠 j).support := ⟨e.symm hex.choose, hex.choose_spec⟩
      rw [dif_pos hex, dif_pos hex']
      change (𝓠 (e.symm hex.choose)).state n ≤ (𝓠 hex'.choose).state n
      have heq : e.symm hex.choose = hex'.choose := by
        by_contra hne
        exact Set.disjoint_left.mp (h hne) hex.choose_spec hex'.choose_spec
      rw [heq]
    · have hex' : ¬ ∃ j, n ∈ (𝓠 j).support := by
        rintro ⟨j, hj⟩; exact hex ⟨e j, by simpa only [Equiv.symm_apply_apply] using hj⟩
      rw [dif_neg hex, dif_neg hex']

end ProbSpace

namespace Distr

namespace Refines

/-- Refinement is antitone in the probability space: a distribution that refines `q`
also refines every probability space that carries less information than `q`. -/
lemma mono {ξ : Distr Mem} {p q : ProbSpace} (hle : p ≤ q) (h : q ≼ ξ) :
    p ≼ ξ := by
  have ⟨ξ', f, hp, hr, heq⟩ := h;
  refine ⟨ξ', f, ?_, ?_, heq⟩
  · intro E hE; rw [hle.μ E hE]; exact hp (hle.mspace E hE)
  · intro i; exact (hle.state i).trans (hr i)

end Refines

end Distr

end Pcol
