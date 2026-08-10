import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

import PcolIris.OProp.MProp
import PcolIris.Semantics.Mem

namespace Pcol

open MeasureTheory

/--
A probability space over the (countable) index set `ℕ`, together with an assignment of a
memory to every index.

The `complete` field states that the measure `μ` is complete for `mspace`, i.e. every set
of outer measure zero is measurable.  (The original version of this field had type
`@MeasureTheory.NullMeasurableSpace _ mspace μ`, which is a type synonym for `ℕ` and hence
carries no information; it has been replaced by the intended completeness statement.)
-/
@[ext]
structure ProbSpace : Type where
  mspace : MeasurableSpace ℕ
  μ : @MeasureTheory.ProbabilityMeasure ℕ mspace
  dom : Set Var
  state : ℕ → Mem
  dom_valid : ∀ i, (state i).dom = dom
  complete :
    @MeasureTheory.Measure.IsComplete ℕ mspace
      (@MeasureTheory.ProbabilityMeasure.toMeasure ℕ mspace μ)

/-! ### Generalities about measures on countable spaces -/

section General
variable {α : Type*} [Countable α] [MeasurableSpace α] (ν : Measure α)

/-- On a countable measurable space there is a largest measurable null set. -/
lemma exists_greatest_null_set :
    ∃ U : Set α, MeasurableSet U ∧ ν U = 0 ∧
      ∀ E : Set α, MeasurableSet E → ν E = 0 → E ⊆ U := by
  classical
  set N : α → Set α := fun n ↦
    if h : ∃ E : Set α, MeasurableSet E ∧ ν E = 0 ∧ n ∈ E then h.choose else ∅ with hN
  have hNm : ∀ n, MeasurableSet (N n) ∧ ν (N n) = 0 := by
    intro n
    by_cases h : ∃ E : Set α, MeasurableSet E ∧ ν E = 0 ∧ n ∈ E
    · rw [hN]; simp only [dif_pos h]; exact ⟨h.choose_spec.1, h.choose_spec.2.1⟩
    · rw [hN]; simp only [dif_neg h]; exact ⟨MeasurableSet.empty, measure_empty⟩
  refine ⟨⋃ n, N n, MeasurableSet.iUnion (fun n ↦ (hNm n).1),
    measure_iUnion_null (fun n ↦ (hNm n).2), ?_⟩
  intro E hE hE0 n hn
  have h : ∃ F : Set α, MeasurableSet F ∧ ν F = 0 ∧ n ∈ F := ⟨E, hE, hE0, hn⟩
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  rw [hN]; simp only [dif_pos h]; exact h.choose_spec.2.2

/-- On a countable space, the intersection of all measurable sets of full measure is
measurable and has full measure. -/
lemma sInter_measure_one [IsProbabilityMeasure ν] :
    MeasurableSet (⋂₀ {E : Set α | MeasurableSet E ∧ ν E = 1}) ∧
      ν (⋂₀ {E : Set α | MeasurableSet E ∧ ν E = 1}) = 1 := by
  obtain ⟨U, hUm, hU0, hUmax⟩ := exists_greatest_null_set ν
  have hcompl : ν Uᶜ = 1 := by
    rw [measure_compl hUm (measure_ne_top _ _), hU0, measure_univ, tsub_zero]
  have heq : (⋂₀ {E : Set α | MeasurableSet E ∧ ν E = 1}) = Uᶜ := by
    apply Set.Subset.antisymm
    · exact Set.sInter_subset_of_mem ⟨hUm.compl, hcompl⟩
    · intro x hx E hE
      by_contra hxE
      have h1 : ν Eᶜ = 0 := by
        rw [measure_compl hE.1 (measure_ne_top _ _), hE.2, measure_univ, tsub_self]
      exact hx (hUmax Eᶜ hE.1.compl h1 hxE)
  rw [heq]
  exact ⟨hUm.compl, hcompl⟩

end General

namespace ProbSpace

/-- The value of the probability measure of a probability space, as an element of `ℝ≥0∞`. -/
lemma μ_eq_one_iff {𝓟 : ProbSpace} {E : Set ℕ} :
    𝓟.μ E = 1 ↔ (@ProbabilityMeasure.toMeasure ℕ 𝓟.mspace 𝓟.μ) E = 1 := by
  rw [← @ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ℕ 𝓟.mspace 𝓟.μ E]
  exact ⟨fun h ↦ by rw [h]; rfl, fun h ↦ by exact_mod_cast h⟩

/-! ### Auxiliary memories -/

/-- A canonical memory with domain exactly `V`: it maps every variable of `V` to `0`. -/
noncomputable def junkMem (V : Set Var) : Mem :=
  open Classical in fun x ↦ if x ∈ V then some 0 else none

lemma junkMem_dom (V : Set Var) : (junkMem V).dom = V := by
  classical
  ext x
  simp only [junkMem, Mem.dom, ne_eq, Set.mem_setOf_eq]
  by_cases hx : x ∈ V <;> simp [hx]

/-! ### The trivial (Dirac) probability space -/

/-- A memory realizing the `MProp` `P` on its domain, if one exists. -/
noncomputable def witness (P : MProp) : Mem :=
  open Classical in
  if h : ∃ σ : Mem, P σ ∧ σ.dom = P.dom then h.choose else junkMem P.dom

lemma witness_spec {P : MProp} (h : ∃ σ : Mem, P σ ∧ σ.dom = P.dom) :
    P (witness P) ∧ (witness P).dom = P.dom := by
  classical
  simpa only [witness, dif_pos h] using h.choose_spec

lemma witness_dom (P : MProp) : (witness P).dom = P.dom := by
  classical
  by_cases h : ∃ σ : Mem, P σ ∧ σ.dom = P.dom
  · exact (witness_spec h).2
  · simp only [witness, dif_neg h]; exact junkMem_dom _

/-- The trivial/dirac measure centered on the set `P` -/
noncomputable def trivial (P : MProp) : ProbSpace where
  mspace := ⊤
  μ := ⟨@Measure.dirac ℕ ⊤ 0, @Measure.dirac.isProbabilityMeasure ℕ ⊤ 0⟩
  dom := P.dom
  state _ := witness P
  dom_valid _ := witness_dom P
  complete := ⟨fun _ _ ↦ by trivial⟩

/-! ### Products -/

/-- The measurable space underlying a product, before completion. -/
@[reducible] def prodMSpace (p q : ProbSpace) : MeasurableSpace ℕ :=
  (p.mspace.prod q.mspace).map Nat.pairEquiv

lemma pairEquiv_measurable (p q : ProbSpace) :
    @Measurable (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) (prodMSpace p q) Nat.pairEquiv :=
  measurable_iff_le_map.mpr fun _ a ↦ a

/-- The measure underlying a product, before completion. -/
noncomputable def prodMeasure (p q : ProbSpace) : @Measure ℕ (prodMSpace p q) :=
  @Measure.map (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) (prodMSpace p q) Nat.pairEquiv
    (@Measure.prod ℕ ℕ p.mspace q.mspace
      (@ProbabilityMeasure.toMeasure ℕ p.mspace p.μ)
      (@ProbabilityMeasure.toMeasure ℕ q.mspace q.μ))

/-- `Nat.pairEquiv` as a measurable equivalence onto the product σ-algebra. -/
def pairMeasurableEquiv (p q : ProbSpace) :
    @MeasurableEquiv (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) (prodMSpace p q) :=
  @MeasurableEquiv.mk (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) (prodMSpace p q) Nat.pairEquiv
    (pairEquiv_measurable p q)
    (by
      intro S _
      change (p.mspace.prod q.mspace).MeasurableSet' (Nat.pairEquiv ⁻¹' (Nat.pairEquiv.symm ⁻¹' S))
      rwa [← Set.preimage_comp, show (Nat.pairEquiv.symm ∘ Nat.pairEquiv) = id from
        funext (fun x ↦ Nat.pairEquiv.left_inv x), Set.preimage_id])

/-- The measure of a product is the product measure of the preimage under the pairing
bijection; since the pairing is a measurable equivalence this holds for *all* sets. -/
lemma prodMeasure_apply (p q : ProbSpace) (E : Set ℕ) :
    prodMeasure p q E =
      (@Measure.prod ℕ ℕ p.mspace q.mspace
        (@ProbabilityMeasure.toMeasure ℕ p.mspace p.μ)
        (@ProbabilityMeasure.toMeasure ℕ q.mspace q.μ)) (Nat.pairEquiv ⁻¹' E) :=
  @MeasurableEquiv.map_apply (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) (prodMSpace p q) _
    (pairMeasurableEquiv p q) E

/-- The σ-algebra of sets that are null-measurable for `ν`; this is the completion of `m`. -/
@[reducible] def completeMSpace (m : MeasurableSpace ℕ) (ν : @Measure ℕ m) : MeasurableSpace ℕ :=
  @MeasureTheory.NullMeasurableSpace.instMeasurableSpace ℕ m ν

/-- The completion of the measure `ν`, as a measure for the σ-algebra `completeMSpace m ν`. -/
noncomputable def completeMeasure (m : MeasurableSpace ℕ) (ν : @Measure ℕ m) :
    @Measure ℕ (completeMSpace m ν) :=
  @Measure.completion ℕ m ν

lemma completeMeasure_apply {m : MeasurableSpace ℕ} (ν : @Measure ℕ m) (s : Set ℕ) :
    completeMeasure m ν s = ν s := rfl

lemma completeMSpace_measurableSet {m : MeasurableSpace ℕ} {ν : @Measure ℕ m} {s : Set ℕ} :
    (completeMSpace m ν).MeasurableSet' s ↔ @NullMeasurableSet ℕ m s ν := Iff.rfl

lemma isComplete_completeMeasure (m : MeasurableSpace ℕ) (ν : @Measure ℕ m) :
    @Measure.IsComplete ℕ (completeMSpace m ν) (completeMeasure m ν) :=
  @Measure.completion.isComplete ℕ m ν

instance isProbabilityMeasure_prodMeasure (p q : ProbSpace) :
    @IsProbabilityMeasure ℕ (prodMSpace p q) (prodMeasure p q) := by
  constructor
  rw [prodMeasure, Measure.map_apply (pairEquiv_measurable p q) MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact @measure_univ _ (p.mspace.prod q.mspace) _
    (@Measure.prod.instIsProbabilityMeasure _ _ p.mspace q.mspace _ _ p.μ.2 q.μ.2)

/-! Transfer of null sets, of the completed σ-algebra and of the completed measure along a
coarsening of the σ-algebra. -/

section Transfer
variable {m m' : MeasurableSpace ℕ}

lemma null_transfer {ν : @Measure ℕ m} {ν' : @Measure ℕ m'}
    (hagree : ∀ E, m.MeasurableSet' E → ν E = ν' E) {N : Set ℕ} (h : ν N = 0) : ν' N = 0 := by
  obtain ⟨G, hNG, hG, hG0⟩ := @exists_measurable_superset_of_null ℕ m ν N h
  exact measure_mono_null hNG (by rw [← hagree G hG, hG0])

lemma ae_eq_transfer {ν : @Measure ℕ m} {ν' : @Measure ℕ m'}
    (hagree : ∀ E, m.MeasurableSet' E → ν E = ν' E) {s t : Set ℕ}
    (hae : @Filter.EventuallyEq ℕ Prop (ae ν) (· ∈ s) (· ∈ t)) :
    @Filter.EventuallyEq ℕ Prop (ae ν') (· ∈ s) (· ∈ t) := by
  rw [Filter.EventuallyEq, ae_iff] at hae ⊢
  exact null_transfer hagree hae

/-- Completing a σ-algebra is monotone, provided the two measures agree on the coarser one. -/
lemma completeMSpace_mono (hle : m ≤ m') {ν : @Measure ℕ m} {ν' : @Measure ℕ m'}
    (hagree : ∀ E, m.MeasurableSet' E → ν E = ν' E) :
    completeMSpace m ν ≤ completeMSpace m' ν' := by
  intro E hE
  obtain ⟨F, hF, hae⟩ := hE
  exact ⟨F, hle F hF, ae_eq_transfer hagree hae⟩

/-- Two measures that agree on a σ-algebra also agree on all sets measurable for its
completion. -/
lemma completeMeasure_agree {ν : @Measure ℕ m} {ν' : @Measure ℕ m'}
    (hagree : ∀ E, m.MeasurableSet' E → ν E = ν' E) {E : Set ℕ}
    (hE : (completeMSpace m ν).MeasurableSet' E) : ν E = ν' E := by
  obtain ⟨F, hF, hae⟩ := hE
  have h1 : ν E = ν F := measure_congr hae
  have h2 : ν' E = ν' F := measure_congr (ae_eq_transfer hagree hae)
  rw [h1, h2, hagree F hF]

end Transfer

lemma isProbabilityMeasure_completeMeasure (m : MeasurableSpace ℕ) (ν : @Measure ℕ m)
    (h : @IsProbabilityMeasure ℕ m ν) :
    @IsProbabilityMeasure ℕ (completeMSpace m ν) (completeMeasure m ν) :=
  ⟨h.measure_univ⟩

/--
The product of two probability spaces.

Compared with the original definition, both the σ-algebra and the measure are *completed*:
this is necessary for the `complete` field, since the product of two complete measures need
not be complete.  Completion changes neither the values of the measure nor the measure of
the sets that were already measurable.
-/
noncomputable def product (p : ProbSpace) (q : ProbSpace) : ProbSpace where
  mspace := completeMSpace (prodMSpace p q) (prodMeasure p q)
  μ := ⟨completeMeasure (prodMSpace p q) (prodMeasure p q),
    isProbabilityMeasure_completeMeasure _ _ (isProbabilityMeasure_prodMeasure p q)⟩
  state k :=
    let ⟨i, j⟩ := Nat.pairEquiv.symm k
    Mem.union (p.state i) (q.state j)
  dom := p.dom ∪ q.dom
  dom_valid := by
    intro n; let ⟨i, j⟩ := Nat.pairEquiv.symm n; simp only
    rw [Mem.dom_union, p.dom_valid i, q.dom_valid j]
  complete := isComplete_completeMeasure _ _

infixl:65 " ⊗ " => product

/-! ### Supports -/

def support (𝓟 : ProbSpace) : Set ℕ :=
  Set.sInter { E | 𝓟.mspace.MeasurableSet' E ∧ 𝓟.μ E = 1 }

lemma support_eq (𝓟 : ProbSpace) :
    𝓟.support =
      ⋂₀ {E : Set ℕ | @MeasurableSet ℕ 𝓟.mspace E ∧
        (@ProbabilityMeasure.toMeasure ℕ 𝓟.mspace 𝓟.μ) E = 1} := by
  have hfam : {E : Set ℕ | 𝓟.mspace.MeasurableSet' E ∧ 𝓟.μ E = 1} =
      {E : Set ℕ | @MeasurableSet ℕ 𝓟.mspace E ∧
        (@ProbabilityMeasure.toMeasure ℕ 𝓟.mspace 𝓟.μ) E = 1} := by
    ext E; exact and_congr_right (fun _ ↦ μ_eq_one_iff)
  rw [support, hfam]

lemma support_measurableSet (𝓟 : ProbSpace) : 𝓟.mspace.MeasurableSet' 𝓟.support := by
  rw [support_eq]
  exact (@sInter_measure_one ℕ _ 𝓟.mspace _ 𝓟.μ.2).1

lemma measure_support (𝓟 : ProbSpace) :
    (@ProbabilityMeasure.toMeasure ℕ 𝓟.mspace 𝓟.μ) 𝓟.support = 1 := by
  rw [support_eq]
  exact (@sInter_measure_one ℕ _ 𝓟.mspace _ 𝓟.μ.2).2

lemma support_subset {𝓟 : ProbSpace} {E : Set ℕ} (hE : 𝓟.mspace.MeasurableSet' E)
    (h1 : (@ProbabilityMeasure.toMeasure ℕ 𝓟.mspace 𝓟.μ) E = 1) : 𝓟.support ⊆ E := by
  rw [support_eq]
  exact Set.sInter_subset_of_mem ⟨hE, h1⟩

/-- A point lies in the support exactly when it is not negligible. -/
lemma mem_support_iff (𝓟 : ProbSpace) (n : ℕ) :
    n ∈ 𝓟.support ↔ (@ProbabilityMeasure.toMeasure ℕ 𝓟.mspace 𝓟.μ) {n} ≠ 0 := by
  constructor
  · intro hn h0
    obtain ⟨G, hnG, hG, hG0⟩ :=
      @exists_measurable_superset_of_null ℕ 𝓟.mspace _ {n} h0
    have h1 : (@ProbabilityMeasure.toMeasure ℕ 𝓟.mspace 𝓟.μ) Gᶜ = 1 := by
      rw [measure_compl hG (measure_ne_top _ _), hG0, measure_univ, tsub_zero]
    exact (support_subset hG.compl h1 hn) (hnG rfl)
  · intro hne
    by_contra hn
    rw [support_eq, Set.mem_sInter] at hn
    push Not at hn
    obtain ⟨E, ⟨hE, hE1⟩, hnE⟩ := hn
    refine hne (measure_mono_null (Set.singleton_subset_iff.mpr (Set.mem_compl hnE)) ?_)
    rw [measure_compl hE (measure_ne_top _ _), hE1, measure_univ, tsub_self]

/-! ### The support of a product -/

/-- The support of a product is contained in the product of the supports. -/
lemma support_product_subset (p q : ProbSpace) :
    (p ⊗ q).support ⊆ Nat.pairEquiv '' (p.support ×ˢ q.support) := by
  set T : Set ℕ := Nat.pairEquiv '' (p.support ×ˢ q.support) with hT
  have hpre : (Nat.pairEquiv ⁻¹' T) = p.support ×ˢ q.support := by
    rw [hT, Set.preimage_image_eq _ Nat.pairEquiv.injective]
  have hmeas0 : (prodMSpace p q).MeasurableSet' T := by
    change (p.mspace.prod q.mspace).MeasurableSet' (Nat.pairEquiv ⁻¹' T)
    rw [hpre]
    exact @MeasurableSet.prod ℕ ℕ p.mspace q.mspace _ _
      (support_measurableSet p) (support_measurableSet q)
  have hmeas : (p ⊗ q).mspace.MeasurableSet' T :=
    @MeasurableSet.nullMeasurableSet ℕ (prodMSpace p q) (prodMeasure p q) T hmeas0
  refine support_subset hmeas ?_
  change prodMeasure p q T = 1
  rw [prodMeasure_apply, hpre,
    @Measure.prod_prod ℕ ℕ p.mspace q.mspace _ _
      (@instSFiniteOfSigmaFinite ℕ q.mspace _ inferInstance),
    measure_support, measure_support, one_mul]

/-- A singleton whose two coordinates are non-negligible is non-negligible for the product
measure. -/
lemma prod_singleton_ne_zero (p q : ProbSpace) (i j : ℕ)
    (hi : (@ProbabilityMeasure.toMeasure ℕ p.mspace p.μ) {i} ≠ 0)
    (hj : (@ProbabilityMeasure.toMeasure ℕ q.mspace q.μ) {j} ≠ 0) :
    (@Measure.prod ℕ ℕ p.mspace q.mspace
      (@ProbabilityMeasure.toMeasure ℕ p.mspace p.μ)
      (@ProbabilityMeasure.toMeasure ℕ q.mspace q.μ)) {(i, j)} ≠ 0 := by
  intro h0
  obtain ⟨F, hsub, hF, hF0⟩ :=
    @exists_measurable_superset_of_null (ℕ × ℕ) (p.mspace.prod q.mspace) _ {(i, j)} h0
  haveI hsf : @SFinite ℕ q.mspace (@ProbabilityMeasure.toMeasure ℕ q.mspace q.μ) :=
    @instSFiniteOfSigmaFinite ℕ q.mspace _ inferInstance
  rw [@Measure.prod_apply ℕ ℕ p.mspace q.mspace _ _ _ _ hF] at hF0
  have hmeas : @Measurable ℕ ENNReal p.mspace _
      (fun x ↦ (@ProbabilityMeasure.toMeasure ℕ q.mspace q.μ) (Prod.mk x ⁻¹' F)) :=
    @measurable_measure_prodMk_left ℕ ℕ p.mspace q.mspace _ hsf _ hF
  rw [lintegral_eq_zero_iff hmeas] at hF0
  refine hi (measure_mono_null (Set.singleton_subset_iff.mpr ?_) (ae_iff.mp hF0))
  simp only [Set.mem_setOf_eq, Pi.zero_apply]
  refine fun hc ↦ hj (measure_mono_null ?_ hc)
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact hsub rfl

/-- The support of a product is the product of the supports. -/
lemma support_product (p q : ProbSpace) :
    (p ⊗ q).support = Nat.pairEquiv '' (p.support ×ˢ q.support) := by
  refine Set.Subset.antisymm (support_product_subset p q) ?_
  rintro _ ⟨⟨i, j⟩, ⟨hi, hj⟩, rfl⟩
  rw [mem_support_iff]
  have hpre : (Nat.pairEquiv ⁻¹' {Nat.pairEquiv (i, j)}) = {(i, j)} := by
    ext x
    constructor
    · intro hx; exact Nat.pairEquiv.injective (by simpa [Set.mem_preimage] using hx)
    · intro hx; simp only [Set.mem_singleton_iff] at hx; subst hx; rfl
  change prodMeasure p q {Nat.pairEquiv (i, j)} ≠ 0
  rw [prodMeasure_apply, hpre]
  exact prod_singleton_ne_zero p q i j ((mem_support_iff p i).mp hi) ((mem_support_iff q j).mp hj)

/-! ### Sums -/

/--
The σ-algebra underlying a sum: a set is measurable when its intersection with the support
of each summand that is given positive weight by `ξ` is measurable there.

(Compared with the original definition, the condition is only imposed for the summands `i`
with `ξ i ≠ 0`; the summands of weight `0` do not contribute to the measure, and ignoring
them is what makes the resulting measure complete.)
-/
@[reducible] def sumMSpace {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) : MeasurableSpace ℕ where
  MeasurableSet' E := ∀ i : ι, ξ i ≠ 0 → (𝓟 i).mspace.MeasurableSet' (E ∩ (𝓟 i).support)
  measurableSet_empty := by
    intro i _; rw [Set.empty_inter]; exact (𝓟 i).mspace.measurableSet_empty
  measurableSet_compl := by
    intro E hE i hi
    have hd : Eᶜ ∩ (𝓟 i).support = (𝓟 i).support \ (E ∩ (𝓟 i).support) := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
    rw [hd]
    exact @MeasurableSet.diff ℕ (𝓟 i).mspace _ _ (support_measurableSet (𝓟 i)) (hE i hi)
  measurableSet_iUnion := by
    intro f hf i hi; rw [Set.iUnion_inter]
    exact (𝓟 i).mspace.measurableSet_iUnion _ (fun n ↦ hf n i hi)

/-- The measure of a sum, as a function of sets: the `ξ`-average of the measures of the
summands, each restricted to its own support. -/
noncomputable def sumMeasureFun {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (E : Set ℕ) :
    ENNReal :=
  ∑' i : ι, ξ i * (@ProbabilityMeasure.toMeasure ℕ (𝓟 i).mspace (𝓟 i).μ) (E ∩ (𝓟 i).support)

/-- The measure underlying a sum. -/
noncomputable def sumMeasure {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) :
    @Measure ℕ (sumMSpace ξ 𝓟) :=
  @Measure.ofMeasurable ℕ (sumMSpace ξ 𝓟) (fun E _ ↦ sumMeasureFun ξ 𝓟 E)
    (by simp only [sumMeasureFun, Set.empty_inter, measure_empty, mul_zero, tsum_zero])
    (by
      intro f hf hdisj
      simp only [sumMeasureFun]
      have key : ∀ i : ι, ξ i * (@ProbabilityMeasure.toMeasure ℕ (𝓟 i).mspace (𝓟 i).μ)
          ((⋃ n, f n) ∩ (𝓟 i).support) =
          ∑' n : ℕ, ξ i * (@ProbabilityMeasure.toMeasure ℕ (𝓟 i).mspace (𝓟 i).μ)
            (f n ∩ (𝓟 i).support) := by
        intro i
        by_cases hi : ξ i = 0
        · simp [hi]
        · rw [Set.iUnion_inter,
            @measure_iUnion ℕ ℕ (𝓟 i).mspace _ _ _
              (fun m n hmn ↦ ((hdisj hmn).mono Set.inter_subset_left Set.inter_subset_left))
              (fun n ↦ hf n i hi),
            ENNReal.tsum_mul_left]
      simp_rw [key]
      exact ENNReal.tsum_comm)

lemma sumMeasure_apply {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) {E : Set ℕ}
    (hE : (sumMSpace ξ 𝓟).MeasurableSet' E) :
    sumMeasure ξ 𝓟 E = sumMeasureFun ξ 𝓟 E :=
  @Measure.ofMeasurable_apply ℕ (sumMSpace ξ 𝓟) _ _ _ E hE

instance isProbabilityMeasure_sumMeasure {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) :
    @IsProbabilityMeasure ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) := by
  constructor
  rw [sumMeasure_apply ξ 𝓟 (@MeasurableSet.univ ℕ (sumMSpace ξ 𝓟))]
  simp only [sumMeasureFun, Set.univ_inter, measure_support, mul_one]
  exact ξ.tsum_coe

lemma isComplete_sumMeasure {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) :
    @Measure.IsComplete ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) := by
  constructor
  intro s hs
  obtain ⟨t, hst, ht, ht0⟩ :=
    @exists_measurable_superset_of_null ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) s hs
  intro i hi
  have h0 : (@ProbabilityMeasure.toMeasure ℕ (𝓟 i).mspace (𝓟 i).μ) (t ∩ (𝓟 i).support) = 0 := by
    rw [sumMeasure_apply ξ 𝓟 ht, sumMeasureFun] at ht0
    rcases mul_eq_zero.mp ((ENNReal.tsum_eq_zero.mp ht0) i) with hz | hz
    · exact absurd hz hi
    · exact hz
  exact (𝓟 i).complete.out _ (measure_mono_null (Set.inter_subset_inter_left _ hst) h0)

/-- The memories of a sum: on the support of the summand `𝓟 i` the memory is the one of
`𝓟 i`; elsewhere (a null set) a canonical memory with domain `V` is used. -/
noncomputable def sumState {ι : Type} (𝓟 : ι → ProbSpace) (V : Set Var) (n : ℕ) : Mem :=
  open Classical in
  if h : ∃ i : ι, n ∈ (𝓟 i).support then (𝓟 h.choose).state n else junkMem V

lemma sumState_dom {ι : Type} {𝓟 : ι → ProbSpace} {V : Set Var}
    (hdom : ∀ i : ι, (𝓟 i).dom = V) (n : ℕ) : (sumState 𝓟 V n).dom = V := by
  classical
  by_cases h : ∃ i : ι, n ∈ (𝓟 i).support
  · rw [sumState, dif_pos h, (𝓟 h.choose).dom_valid n]; exact hdom _
  · rw [sumState, dif_neg h]; exact junkMem_dom V

/--
The `ξ`-average of the family of probability spaces `𝓟`, all of which have domain `V` and
pairwise disjoint supports.

The disjointness hypothesis `_h` is kept because it is part of the intended interface (it is
what makes the memory attached to a point of the support canonical), but the construction
itself does not need it: the memory of a point of the support is read off from *some*
summand containing it.
-/
noncomputable def sum {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (V : Set Var)
    (_h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    (hdom : ∀ i : ι, (𝓟 i).dom = V) :
    ProbSpace where
  mspace := sumMSpace ξ 𝓟
  μ := ⟨sumMeasure ξ 𝓟, isProbabilityMeasure_sumMeasure ξ 𝓟⟩
  dom := V
  state := sumState 𝓟 V
  dom_valid := sumState_dom hdom
  complete := isComplete_sumMeasure ξ 𝓟

/-- The support of a sum is the union of the supports of the summands of positive weight. -/
lemma support_sum {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (V : Set Var)
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    (hdom : ∀ i : ι, (𝓟 i).dom = V) :
    (sum ξ 𝓟 V h hdom).support = ⋃ i ∈ {i : ι | ξ i ≠ 0}, (𝓟 i).support := by
  ext n
  rw [mem_support_iff]
  constructor
  · intro hn
    by_contra hc
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hc
    have hempty : ∀ i : ι, ξ i ≠ 0 → ({n} : Set ℕ) ∩ (𝓟 i).support = ∅ := by
      intro i hi
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hx⟩
      exact (hc i hi hx).elim
    have hmeas : (sumMSpace ξ 𝓟).MeasurableSet' {n} := by
      intro i hi
      rw [hempty i hi]
      exact (𝓟 i).mspace.measurableSet_empty
    refine hn ?_
    change sumMeasure ξ 𝓟 {n} = 0
    rw [sumMeasure_apply ξ 𝓟 hmeas, sumMeasureFun]
    refine ENNReal.tsum_eq_zero.mpr (fun i ↦ ?_)
    by_cases hi : ξ i = 0
    · simp [hi]
    · rw [hempty i hi, measure_empty, mul_zero]
  · intro hn h0
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn
    obtain ⟨i, hi, hni⟩ := hn
    obtain ⟨t, hst, ht, ht0⟩ :=
      @exists_measurable_superset_of_null ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) {n} h0
    rw [sumMeasure_apply ξ 𝓟 ht, sumMeasureFun] at ht0
    rcases mul_eq_zero.mp ((ENNReal.tsum_eq_zero.mp ht0) i) with hz | hz
    · exact hi hz
    · refine (mem_support_iff (𝓟 i) n).mp hni (measure_mono_null ?_ hz)
      exact Set.singleton_subset_iff.mpr ⟨hst rfl, hni⟩

/-- Products with a common right factor of spaces with disjoint supports again have disjoint
supports. -/
lemma disjoint_support_product {p p' q : ProbSpace} (hd : Disjoint p.support p'.support) :
    Disjoint (p ⊗ q).support (p' ⊗ q).support := by
  rw [support_product, support_product]
  rw [Set.disjoint_left]
  rintro _ ⟨⟨i, j⟩, ⟨hi, hj⟩, rfl⟩ hmem
  obtain ⟨⟨i', j'⟩, ⟨hi', hj'⟩, heq⟩ := hmem
  have : (i', j') = (i, j) := Nat.pairEquiv.injective heq
  rw [this] at hi'
  exact Set.disjoint_left.mp hd hi hi'

/-! ### The distributive law of products over sums

The two hypotheses needed to form the right-hand side of the distributive law. -/

/-- The summands of the right-hand side of the distributive law have disjoint supports. -/
lemma sum_prod_disjoint {ι : Type} {𝓟 : ι → ProbSpace} (𝓠 : ProbSpace)
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {i j : ι} (hij : i ≠ j) :
    Disjoint (𝓟 i ⊗ 𝓠).support (𝓟 j ⊗ 𝓠).support :=
  disjoint_support_product (h hij)

/-- The summands of the right-hand side of the distributive law all have domain `V ∪ 𝓠.dom`. -/
lemma sum_prod_dom {ι : Type} {𝓟 : ι → ProbSpace} (𝓠 : ProbSpace) {V : Set Var}
    (hdom : ∀ i : ι, (𝓟 i).dom = V) (i : ι) : (𝓟 i ⊗ 𝓠).dom = V ∪ 𝓠.dom := by
  change (𝓟 i).dom ∪ 𝓠.dom = V ∪ 𝓠.dom
  rw [hdom i]

/--
The right-hand side of the distributive law: the sum of the products `𝓟 i ⊗ 𝓠`.
-/
noncomputable def sumProd {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (𝓠 : ProbSpace)
    (V : Set Var) (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    (hdom : ∀ i : ι, (𝓟 i).dom = V) : ProbSpace :=
  sum ξ (fun i ↦ 𝓟 i ⊗ 𝓠) (V ∪ 𝓠.dom) (sum_prod_disjoint 𝓠 h) (sum_prod_dom 𝓠 hdom)

/-
The distributive law of products over sums, as originally stated:

```
lemma sum_prod_distribute {ι : Type} {ξ : PMF ι} (𝓟 : ι → ProbSpace) (𝓠 : ProbSpace)
    {V : Set Var} {h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support}
    {hdom : ∀ i : ι, (𝓟 i).dom = V} :
    sum ξ 𝓟 V h hdom ⊗ 𝓠 =
    sum ξ (fun i ↦ 𝓟 i ⊗ 𝓠) (V ∪ 𝓠.dom) sorry sorry := sorry
```

(the `𝓘` occurring in the original left-hand side was an auto-bound implicit variable, and
is `𝓠` here).

This equality of `ProbSpace` structures is *false*, because of the `state` field: a
`ProbSpace` assigns a memory to *every* natural number, including the ones outside its
support, and the two sides make incompatible arbitrary choices there.  For a point
`k = ⟨i, j⟩` with `i` in the support of some `𝓟 a` but `j` outside the support of `𝓠`, the
left-hand side has state `(𝓟 a).state i ⊎ 𝓠.state j`, whereas `k` lies outside the support
of every summand of the right-hand side, so the right-hand side uses the canonical memory
with domain `V ∪ 𝓠.dom` there.  These differ as soon as the memories involved take a value
other than `0`.

Everything that is measure-theoretically meaningful does hold, and is proved as
`Pcol.ProbSpace.sum_prod_distribute` in `PcolIris/OProp/SumProd.lean`: the two sides have the
same σ-algebra, the same measure (on all sets), the same domain, the same support, and their
states agree at every point of that support (hence almost everywhere).
-/

structure LE_ProbSpace (p q : ProbSpace) : Prop where
  mspace : p.mspace ≤ q.mspace
  μ : ∀ E, p.mspace.MeasurableSet' E → p.μ E = q.μ E
  dom : p.dom ⊆ q.dom
  state : ∀ i, p.state i ≤ q.state i

instance : LE ProbSpace where
  le p q := LE_ProbSpace p q

instance : Preorder ProbSpace where
  le_refl p := by
    constructor
    · exact le_refl _
    · intro _ _; rfl
    · exact Set.Subset.refl _
    · intro _; exact le_refl _
  le_trans p q r hpq hqr := by
    constructor
    · exact hpq.mspace.trans hqr.mspace
    · intro E hE; apply (hpq.μ E hE).trans
      exact hqr.μ E (hpq.mspace E hE)
    · exact hpq.dom.trans hqr.dom
    · intro i; exact (hpq.state i).trans <| hqr.state i

instance : Membership (Set ℕ) ProbSpace where
  mem 𝓟 := 𝓟.mspace.MeasurableSet'

end ProbSpace

namespace Distr

def Refines (ξ : Distr Mem) (𝓟 : ProbSpace) : Prop :=
  ∃ ξ' : PMF ℕ, ∃ f : ℕ → Mem,
    (∀ {E}, E ∈ 𝓟 → 𝓟.μ E = ∑' i : E, ξ' i) ∧
    (∀ i, 𝓟.state i ≤ f i) ∧
    ξ = ξ'.map (some ∘ f)

namespace Refines

lemma bot_0 {ξ : Distr Mem} {p : ProbSpace}
    (h : Distr.Refines ξ p) : ξ ⊥ = 0 := by
  obtain ⟨ξ', f, -, -, rfl⟩ := h
  change (ξ'.map (some ∘ f) : PMF (WithBot Mem)) ⊥ = 0
  rw [PMF.map_apply]
  simp

end Refines

end Distr

notation:30 p " ≼ " ξ => Distr.Refines ξ p

end Pcol
