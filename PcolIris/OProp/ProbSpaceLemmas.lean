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

lemma pairEquiv_aemeasurable (p q : ProbSpace Mem) :
    @AEMeasurable (ℕ × ℕ) ℕ ((p.mspace.prod q.mspace).map Nat.pairEquiv)
      (p.mspace.prod q.mspace) (⇑Nat.pairEquiv)
      (@ProbabilityMeasure.toMeasure (ℕ × ℕ) (p.mspace.prod q.mspace)
        (@ProbabilityMeasure.prod ℕ p.mspace ℕ q.mspace p.μ q.μ)) := by
  apply @Measurable.aemeasurable _ _
    (p.mspace.prod q.mspace) ((p.mspace.prod q.mspace).map Nat.pairEquiv) _ _
  exact measurable_iff_le_map.mpr fun s a ↦ a

/-- The measure of a product space is the product measure of the preimage under the
pairing bijection. -/
lemma product_μ_apply (p q : ProbSpace Mem) {E : Set ℕ} (hE : (p ⊗ q).mspace.MeasurableSet' E) :
    (p ⊗ q).μ E =
      (@ProbabilityMeasure.prod ℕ p.mspace ℕ q.mspace p.μ q.μ) (⇑Nat.pairEquiv ⁻¹' E) :=
  @ProbabilityMeasure.map_apply (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) (p ⊗ q).mspace
    (@ProbabilityMeasure.prod ℕ p.mspace ℕ q.mspace p.μ q.μ) (⇑Nat.pairEquiv)
    (pairEquiv_aemeasurable p q) E hE

/-- Values of a probability measure, viewed in `ℝ≥0∞`. -/
lemma prob_coe {α : Type*} {m : MeasurableSpace α} (P : @ProbabilityMeasure α m) (s : Set α) :
    ((P s : NNReal) : ENNReal) = @ProbabilityMeasure.toMeasure α m P s :=
  ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P s

lemma prod_coe_apply (p q : ProbSpace Mem) (s : Set (ℕ × ℕ)) :
    (((@ProbabilityMeasure.prod ℕ p.mspace ℕ q.mspace p.μ q.μ) s : NNReal) : ENNReal) =
      (@Measure.prod ℕ ℕ p.mspace q.mspace
        (@ProbabilityMeasure.toMeasure ℕ p.mspace p.μ)
        (@ProbabilityMeasure.toMeasure ℕ q.mspace q.μ)) s :=
  @prob_coe (ℕ × ℕ) (p.mspace.prod q.mspace) _ s

/-! ### Monotonicity of the product of probability spaces -/

/-- The product of probability spaces is monotone in its left argument. -/
lemma product_mono_left {p p' q : ProbSpace Mem} (h : p ≤ p') : (p ⊗ q) ≤ (p' ⊗ q) := by
  refine ⟨MeasurableSpace.map_mono (prod_le_prod_left h.mspace), ?_, ?_⟩
  · intro E hE
    have hE' : (p' ⊗ q).mspace.MeasurableSet' E :=
      MeasurableSpace.map_mono (prod_le_prod_left h.mspace) E hE
    rw [product_μ_apply p q hE, product_μ_apply p' q hE']
    refine ENNReal.coe_injective ?_
    rw [prod_coe_apply, prod_coe_apply]
    refine prod_measure_eq_left h.mspace _ _ _ (fun F hF ↦ ?_) _ hE
    rw [← @prob_coe ℕ p.mspace p.μ F, ← @prob_coe ℕ p'.mspace p'.μ F, h.μ F hF]
  · intro i
    show Mem.union (p.state _) (q.state _) = Mem.union (p'.state _) (q.state _)
    rw [h.state]

/-- The product of probability spaces is monotone in its right argument. -/
lemma product_mono_right {p q q' : ProbSpace Mem} (h : q ≤ q') : (p ⊗ q) ≤ (p ⊗ q') := by
  refine ⟨MeasurableSpace.map_mono (prod_le_prod_right h.mspace), ?_, ?_⟩
  · intro E hE
    have hE' : (p ⊗ q').mspace.MeasurableSet' E :=
      MeasurableSpace.map_mono (prod_le_prod_right h.mspace) E hE
    rw [product_μ_apply p q hE, product_μ_apply p q' hE']
    refine ENNReal.coe_injective ?_
    rw [prod_coe_apply, prod_coe_apply]
    refine prod_measure_eq_right h.mspace _ _ _ (fun F hF ↦ ?_) _ hE
    rw [← @prob_coe ℕ q.mspace q.μ F, ← @prob_coe ℕ q'.mspace q'.μ F, h.μ F hF]
  · intro i
    change Mem.union (p.state _) (q.state _) = Mem.union (p.state _) (q'.state _)
    rw [h.state]

/-- The product of probability spaces is monotone. -/
lemma product_mono {p p' q q' : ProbSpace Mem} (h₁ : p ≤ p') (h₂ : q ≤ q') :
    (p ⊗ q) ≤ (p' ⊗ q') :=
  le_trans (product_mono_left h₁) (product_mono_right h₂)

end ProbSpace

namespace Distr

namespace Refines

/-- Refinement is antitone in the probability space: a distribution that refines `q`
also refines every probability space that carries less information than `q`. -/
lemma mono {α : Type*} {ξ : Distr α} {p q : ProbSpace α} (hle : p ≤ q) (h : q ≼ ξ) :
    p ≼ ξ := by
  intro E hE
  rw [hle.μ E hE, h (hle.mspace E hE)]
  exact tsum_congr fun i ↦ by rw [hle.state i]

end Refines

end Distr

end Pcol
