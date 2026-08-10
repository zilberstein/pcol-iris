/-
The distributive law of products over sums of probability spaces.

The equality of `ProbSpace` structures that one would like to state is false, because the
`state` field of a `ProbSpace` is defined at *every* natural number, and the two sides of
the law make different (arbitrary) choices outside of the support; see the discussion in
`PcolIris/OProp/ProbSpace.lean`.

Everything that is measure-theoretically meaningful does hold, and is proved here: the two
sides have the same σ-algebra, the same measure, the same domain, and their states agree on
the support.
-/
import PcolIris.OProp.ProbSpaceLemmas

namespace Pcol

open MeasureTheory MeasurableSpace

namespace ProbSpace

/-! ### Traces of the σ-algebra of a sum -/

section Sum

variable {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace)

/-- The support of a summand is measurable for the σ-algebra of the sum. -/
lemma support_mem_sumMSpace
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) (i : ι) :
    (sumMSpace ξ 𝓟).MeasurableSet' (𝓟 i).support := by
  intro j _
  by_cases hij : j = i
  · subst hij
    rw [Set.inter_self]
    exact support_measurableSet _
  · have hemp : (𝓟 i).support ∩ (𝓟 j).support = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (h (fun hc ↦ hij hc.symm))
    rw [hemp]
    exact (𝓟 j).mspace.measurableSet_empty

/-- A set that is measurable for a summand becomes measurable for the sum after
intersecting it with the support of that summand. -/
lemma inter_support_mem_sumMSpace
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {i : ι} {B : Set ℕ}
    (hB : (𝓟 i).mspace.MeasurableSet' B) :
    (sumMSpace ξ 𝓟).MeasurableSet' (B ∩ (𝓟 i).support) := by
  intro j _
  by_cases hij : j = i
  · subst hij
    rw [Set.inter_assoc, Set.inter_self]
    exact @MeasurableSet.inter ℕ (𝓟 j).mspace _ _ hB (support_measurableSet _)
  · have hemp : (𝓟 i).support ∩ (𝓟 j).support = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (h (fun hc ↦ hij hc.symm))
    rw [Set.inter_assoc, hemp, Set.inter_empty]
    exact (𝓟 j).mspace.measurableSet_empty

/-- The measure of a sum on a subset of the support of one summand. -/
lemma sumMeasure_inter_support
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {i : ι} {B : Set ℕ}
    (hB : (𝓟 i).mspace.MeasurableSet' B) :
    sumMeasure ξ 𝓟 (B ∩ (𝓟 i).support) =
      ξ i * (@ProbabilityMeasure.toMeasure ℕ (𝓟 i).mspace (𝓟 i).μ) (B ∩ (𝓟 i).support) := by
  rw [sumMeasure_apply ξ 𝓟 (inter_support_mem_sumMSpace ξ 𝓟 h hB), sumMeasureFun]
  refine tsum_eq_single i ?_ |>.trans ?_
  · intro j hji
    have hemp : (𝓟 i).support ∩ (𝓟 j).support = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (h (fun hc ↦ hji hc.symm))
    rw [Set.inter_assoc, hemp, Set.inter_empty, measure_empty, mul_zero]
  · rw [Set.inter_assoc, Set.inter_self]

end Sum


/-! ### Comparing integrals for a sum and for one of its summands -/

/-- The measure of a probability space, as an `ℝ≥0∞`-valued measure. -/
@[reducible] noncomputable def meas (p : ProbSpace) : @Measure ℕ p.mspace :=
  @ProbabilityMeasure.toMeasure ℕ p.mspace p.μ

lemma isProbabilityMeasure_meas (p : ProbSpace) : @IsProbabilityMeasure ℕ p.mspace p.meas := p.μ.2

lemma support_nonempty (p : ProbSpace) : p.support.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hc
  have h1 : p.meas p.support = 1 := measure_support p
  rw [hc, measure_empty] at h1
  exact zero_ne_one h1

open Classical in
/-- The map that collapses everything outside the support of `p` to `0`. -/
noncomputable def supportProj (p : ProbSpace) (x : ℕ) : ℕ := if x ∈ p.support then x else 0

section Sum2

variable {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace)

lemma measurable_supportProj
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) (i : ι) :
    @Measurable ℕ ℕ (sumMSpace ξ 𝓟) (𝓟 i).mspace (supportProj (𝓟 i)) := by
  classical
  intro B hB
  by_cases hn : (0 : ℕ) ∈ B
  · have hset : supportProj (𝓟 i) ⁻¹' B = (B ∩ (𝓟 i).support) ∪ ((𝓟 i).support)ᶜ := by
      ext x; by_cases hx : x ∈ (𝓟 i).support <;> simp [supportProj, hx, hn]
    rw [hset]
    exact @MeasurableSet.union ℕ (sumMSpace ξ 𝓟) _ _ (inter_support_mem_sumMSpace ξ 𝓟 h hB)
      (@MeasurableSet.compl ℕ _ (sumMSpace ξ 𝓟) (support_mem_sumMSpace ξ 𝓟 h i))
  · have hset : supportProj (𝓟 i) ⁻¹' B = B ∩ (𝓟 i).support := by
      ext x; by_cases hx : x ∈ (𝓟 i).support <;> simp [supportProj, hx, hn]
    rw [hset]
    exact inter_support_mem_sumMSpace ξ 𝓟 h hB

lemma map_supportProj
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) (i : ι) :
    @Measure.map ℕ ℕ (sumMSpace ξ 𝓟) (𝓟 i).mspace (supportProj (𝓟 i))
        (@Measure.restrict ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) (𝓟 i).support) =
      ξ i • (@Measure.restrict ℕ (𝓟 i).mspace (𝓟 i).meas (𝓟 i).support) := by
  classical
  refine @Measure.ext ℕ (𝓟 i).mspace _ _ (fun B hB ↦ ?_)
  have hpre : supportProj (𝓟 i) ⁻¹' B ∩ (𝓟 i).support = B ∩ (𝓟 i).support := by
    ext x; by_cases hx : x ∈ (𝓟 i).support <;> simp [supportProj, hx]
  rw [@Measure.map_apply ℕ ℕ (sumMSpace ξ 𝓟) (𝓟 i).mspace _ _
      (measurable_supportProj ξ 𝓟 h i) B hB,
    @Measure.restrict_apply ℕ (sumMSpace ξ 𝓟) _ _ _
      ((measurable_supportProj ξ 𝓟 h i) hB),
    hpre, sumMeasure_inter_support ξ 𝓟 h hB]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]

/-- Integrating a function supported in the support of the summand `𝓟 i` against the measure
of the sum amounts to integrating it against `ξ i` times the measure of `𝓟 i`. -/
lemma lintegral_sumMeasure_of_support
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {i : ι} {f : ℕ → ENNReal}
    (hfi : @Measurable ℕ ENNReal (𝓟 i).mspace _ f)
    (hf0 : ∀ x, x ∉ (𝓟 i).support → f x = 0) :
    @lintegral ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) f
      = ξ i * @lintegral ℕ (𝓟 i).mspace (𝓟 i).meas f := by
  classical
  set A := (𝓟 i).support with hA
  have hAS : (sumMSpace ξ 𝓟).MeasurableSet' A := support_mem_sumMSpace ξ 𝓟 h i
  have hAi : (𝓟 i).mspace.MeasurableSet' A := support_measurableSet _
  have hzeroS : @lintegral ℕ (sumMSpace ξ 𝓟)
      (@Measure.restrict ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) Aᶜ) f = 0 :=
    @setLIntegral_eq_zero ℕ (sumMSpace ξ 𝓟) _ f Aᶜ
      (@MeasurableSet.compl ℕ _ (sumMSpace ξ 𝓟) hAS) (fun x hx ↦ hf0 x hx)
  have hzeroi : @lintegral ℕ (𝓟 i).mspace
      (@Measure.restrict ℕ (𝓟 i).mspace (𝓟 i).meas Aᶜ) f = 0 :=
    @setLIntegral_eq_zero ℕ (𝓟 i).mspace _ f Aᶜ
      (@MeasurableSet.compl ℕ _ (𝓟 i).mspace hAi) (fun x hx ↦ hf0 x hx)
  have hsplitS := @lintegral_add_compl ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) f A hAS
  have hspliti := @lintegral_add_compl ℕ (𝓟 i).mspace (𝓟 i).meas f A hAi
  rw [hzeroS, add_zero] at hsplitS
  rw [hzeroi, add_zero] at hspliti
  rw [← hsplitS, ← hspliti]
  have hcongr : @lintegral ℕ (sumMSpace ξ 𝓟)
      (@Measure.restrict ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) A) f
      = @lintegral ℕ (sumMSpace ξ 𝓟)
        (@Measure.restrict ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) A)
        (fun x ↦ f (supportProj (𝓟 i) x)) :=
    @setLIntegral_congr_fun ℕ (sumMSpace ξ 𝓟) (sumMeasure ξ 𝓟) f _ A hAS
      (fun x hx ↦ by
        simp only [supportProj, if_pos (show x ∈ (𝓟 i).support from hx)])
  rw [hcongr,
    ← @lintegral_map ℕ ℕ (sumMSpace ξ 𝓟) (𝓟 i).mspace _ f (supportProj (𝓟 i)) hfi
      (measurable_supportProj ξ 𝓟 h i),
    map_supportProj ξ 𝓟 h i,
    @lintegral_smul_measure ℕ (𝓟 i).mspace _ _ _ _ _]
  rfl

end Sum2

/-! ### Products with a fixed second factor -/

/-- The σ-algebra of the sets whose intersection with a fixed measurable set `K` is
measurable. -/
@[reducible] def restrictMSpace {α : Type*} (m : MeasurableSpace α) (K : Set α)
    (hK : m.MeasurableSet' K) : MeasurableSpace α where
  MeasurableSet' G := m.MeasurableSet' (G ∩ K)
  measurableSet_empty := by rw [Set.empty_inter]; exact m.measurableSet_empty
  measurableSet_compl := by
    intro G hG
    have hd : Gᶜ ∩ K = K \ (G ∩ K) := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
    rw [hd]
    exact @MeasurableSet.diff α m _ _ hK hG
  measurableSet_iUnion := by
    intro f hf; rw [Set.iUnion_inter]
    exact m.measurableSet_iUnion _ hf

section SumProdSection

variable {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (𝓠 : ProbSpace)

/-- The "rectangle" cut out by the support of the summand `𝓟 i` and the support of `𝓠`. -/
def sumProdRect (𝓟 : ι → ProbSpace) (𝓠 : ProbSpace) (i : ι) : Set (ℕ × ℕ) :=
  (𝓟 i).support ×ˢ 𝓠.support

lemma sumProdRect_mem_prod_sum
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) (i : ι) :
    ((sumMSpace ξ 𝓟).prod 𝓠.mspace).MeasurableSet' (sumProdRect 𝓟 𝓠 i) :=
  @MeasurableSet.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace _ _
    (support_mem_sumMSpace ξ 𝓟 h i) (support_measurableSet 𝓠)

lemma sumProdRect_mem_prod_summand (i : ι) :
    (((𝓟 i).mspace).prod 𝓠.mspace).MeasurableSet' (sumProdRect 𝓟 𝓠 i) :=
  @MeasurableSet.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace _ _
    (support_measurableSet (𝓟 i)) (support_measurableSet 𝓠)

/-- Intersecting with the rectangle of the `i`-th summand turns a set that is measurable for
the sum into one that is measurable for the summand. -/
lemma inter_sumProdRect_mem_summand {i : ι} (hi : ξ i ≠ 0) {A : Set (ℕ × ℕ)}
    (hA : ((sumMSpace ξ 𝓟).prod 𝓠.mspace).MeasurableSet' A) :
    (((𝓟 i).mspace).prod 𝓠.mspace).MeasurableSet' (A ∩ sumProdRect 𝓟 𝓠 i) := by
  have hle : (sumMSpace ξ 𝓟).prod 𝓠.mspace ≤
      restrictMSpace ((𝓟 i).mspace.prod 𝓠.mspace) (sumProdRect 𝓟 𝓠 i)
        (sumProdRect_mem_prod_summand 𝓟 𝓠 i) := by
    have hgen : (sumMSpace ξ 𝓟).prod 𝓠.mspace =
        generateFrom (Set.image2 (· ×ˢ ·) {s : Set ℕ | (sumMSpace ξ 𝓟).MeasurableSet' s}
          {t : Set ℕ | 𝓠.mspace.MeasurableSet' t}) :=
      (@generateFrom_prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace).symm
    rw [hgen]
    refine generateFrom_le ?_
    rintro _ ⟨s, hs, t, ht, rfl⟩
    change ((𝓟 i).mspace.prod 𝓠.mspace).MeasurableSet' ((s ×ˢ t) ∩ sumProdRect 𝓟 𝓠 i)
    have hrect : (s ×ˢ t) ∩ sumProdRect 𝓟 𝓠 i =
        (s ∩ (𝓟 i).support) ×ˢ (t ∩ 𝓠.support) := by
      ext x
      simp only [sumProdRect, Set.mem_inter_iff, Set.mem_prod]
      tauto
    rw [hrect]
    exact @MeasurableSet.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace _ _ (hs i hi)
      (@MeasurableSet.inter ℕ 𝓠.mspace _ _ ht (support_measurableSet 𝓠))
  exact hle A hA

/-- Intersecting with the rectangle of the `i`-th summand turns a set that is measurable for
the summand into one that is measurable for the sum. -/
lemma inter_sumProdRect_mem_sum
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {i : ι} {B : Set (ℕ × ℕ)}
    (hB : (((𝓟 i).mspace).prod 𝓠.mspace).MeasurableSet' B) :
    ((sumMSpace ξ 𝓟).prod 𝓠.mspace).MeasurableSet' (B ∩ sumProdRect 𝓟 𝓠 i) := by
  have hle : ((𝓟 i).mspace).prod 𝓠.mspace ≤
      restrictMSpace ((sumMSpace ξ 𝓟).prod 𝓠.mspace) (sumProdRect 𝓟 𝓠 i)
        (sumProdRect_mem_prod_sum ξ 𝓟 𝓠 h i) := by
    have hgen : (𝓟 i).mspace.prod 𝓠.mspace =
        generateFrom (Set.image2 (· ×ˢ ·) {s : Set ℕ | (𝓟 i).mspace.MeasurableSet' s}
          {t : Set ℕ | 𝓠.mspace.MeasurableSet' t}) :=
      (@generateFrom_prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace).symm
    rw [hgen]
    refine generateFrom_le ?_
    rintro _ ⟨s, hs, t, ht, rfl⟩
    change ((sumMSpace ξ 𝓟).prod 𝓠.mspace).MeasurableSet' ((s ×ˢ t) ∩ sumProdRect 𝓟 𝓠 i)
    have hrect : (s ×ˢ t) ∩ sumProdRect 𝓟 𝓠 i =
        (s ∩ (𝓟 i).support) ×ˢ (t ∩ 𝓠.support) := by
      ext x
      simp only [sumProdRect, Set.mem_inter_iff, Set.mem_prod]
      tauto
    rw [hrect]
    exact @MeasurableSet.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace _ _
      (inter_support_mem_sumMSpace ξ 𝓟 h hs)
      (@MeasurableSet.inter ℕ 𝓠.mspace _ _ ht (support_measurableSet 𝓠))
  exact hle B hB

/-- On the rectangle of the `i`-th summand, the product measure of the sum is `ξ i` times the
product measure of that summand: measurable version for the sum. -/
lemma prodMeasure_inter_sumProdRect_of_sum
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {i : ι} (hi : ξ i ≠ 0)
    {A : Set (ℕ × ℕ)} (hA : ((sumMSpace ξ 𝓟).prod 𝓠.mspace).MeasurableSet' A) :
    (@Measure.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace (sumMeasure ξ 𝓟) 𝓠.meas)
        (A ∩ sumProdRect 𝓟 𝓠 i)
      = ξ i * (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas)
        (A ∩ sumProdRect 𝓟 𝓠 i) := by
  haveI hsf : @SFinite ℕ 𝓠.mspace 𝓠.meas := @instSFiniteOfSigmaFinite ℕ 𝓠.mspace _ inferInstance
  set G := A ∩ sumProdRect 𝓟 𝓠 i with hG
  have hGS : ((sumMSpace ξ 𝓟).prod 𝓠.mspace).MeasurableSet' G :=
    @MeasurableSet.inter (ℕ × ℕ) ((sumMSpace ξ 𝓟).prod 𝓠.mspace) _ _ hA
      (sumProdRect_mem_prod_sum ξ 𝓟 𝓠 h i)
  have hGi : (((𝓟 i).mspace).prod 𝓠.mspace).MeasurableSet' G :=
    inter_sumProdRect_mem_summand ξ 𝓟 𝓠 hi hA
  have hfi : @Measurable ℕ ENNReal (𝓟 i).mspace _ (fun x ↦ 𝓠.meas (Prod.mk x ⁻¹' G)) :=
    @measurable_measure_prodMk_left ℕ ℕ (𝓟 i).mspace 𝓠.mspace 𝓠.meas hsf G hGi
  have hf0 : ∀ x, x ∉ (𝓟 i).support → 𝓠.meas (Prod.mk x ⁻¹' G) = 0 := by
    intro x hx
    have : (Prod.mk x ⁻¹' G) = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, hG]
      rintro ⟨-, hmem⟩
      exact hx hmem.1
    rw [this, measure_empty]
  rw [@Measure.prod_apply ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace _ _ _ _ hGS,
    @Measure.prod_apply ℕ ℕ (𝓟 i).mspace 𝓠.mspace _ _ _ _ hGi]
  exact lintegral_sumMeasure_of_support ξ 𝓟 h hfi hf0

/-- Same statement, for a set that is measurable for the summand. -/
lemma prodMeasure_inter_sumProdRect_of_summand
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {i : ι} (hi : ξ i ≠ 0)
    {B : Set (ℕ × ℕ)} (hB : (((𝓟 i).mspace).prod 𝓠.mspace).MeasurableSet' B) :
    (@Measure.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace (sumMeasure ξ 𝓟) 𝓠.meas)
        (B ∩ sumProdRect 𝓟 𝓠 i)
      = ξ i * (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas)
        (B ∩ sumProdRect 𝓟 𝓠 i) := by
  have hidem : (B ∩ sumProdRect 𝓟 𝓠 i) ∩ sumProdRect 𝓟 𝓠 i = B ∩ sumProdRect 𝓟 𝓠 i := by
    rw [Set.inter_assoc, Set.inter_self]
  have := prodMeasure_inter_sumProdRect_of_sum ξ 𝓟 𝓠 h hi
    (inter_sumProdRect_mem_sum ξ 𝓟 𝓠 h hB)
  rwa [hidem] at this

/-- On the rectangle of the `i`-th summand, the product measure of the sum is `ξ i` times the
product measure of that summand, for *arbitrary* subsets. -/
lemma prodMeasure_of_subset_sumProdRect
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {i : ι} (hi : ξ i ≠ 0)
    {A : Set (ℕ × ℕ)} (hsub : A ⊆ sumProdRect 𝓟 𝓠 i) :
    (@Measure.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace (sumMeasure ξ 𝓟) 𝓠.meas) A
      = ξ i * (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas) A := by
  refine le_antisymm ?_ ?_
  · obtain ⟨B, hAB, hB, hBeq⟩ :=
      @exists_measurable_superset (ℕ × ℕ) ((𝓟 i).mspace.prod 𝓠.mspace)
        (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas) A
    calc (@Measure.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace (sumMeasure ξ 𝓟) 𝓠.meas) A
        ≤ _ := measure_mono (Set.subset_inter hAB hsub)
      _ = ξ i * (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas)
            (B ∩ sumProdRect 𝓟 𝓠 i) :=
          prodMeasure_inter_sumProdRect_of_summand ξ 𝓟 𝓠 h hi hB
      _ ≤ ξ i * (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas) B :=
          mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
      _ = ξ i * (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas) A := by rw [hBeq]
  · obtain ⟨C, hAC, hC, hCeq⟩ :=
      @exists_measurable_superset (ℕ × ℕ) ((sumMSpace ξ 𝓟).prod 𝓠.mspace)
        (@Measure.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace (sumMeasure ξ 𝓟) 𝓠.meas) A
    calc ξ i * (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas) A
        ≤ ξ i * (@Measure.prod ℕ ℕ (𝓟 i).mspace 𝓠.mspace (𝓟 i).meas 𝓠.meas)
            (C ∩ sumProdRect 𝓟 𝓠 i) :=
          mul_le_mul' le_rfl (measure_mono (Set.subset_inter hAC hsub))
      _ = (@Measure.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace (sumMeasure ξ 𝓟) 𝓠.meas)
            (C ∩ sumProdRect 𝓟 𝓠 i) :=
          (prodMeasure_inter_sumProdRect_of_sum ξ 𝓟 𝓠 h hi hC).symm
      _ ≤ (@Measure.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace (sumMeasure ξ 𝓟) 𝓠.meas) C :=
          measure_mono Set.inter_subset_left
      _ = (@Measure.prod ℕ ℕ (sumMSpace ξ 𝓟) 𝓠.mspace (sumMeasure ξ 𝓟) 𝓠.meas) A := hCeq

end SumProdSection

/-! ### The two sides of the distributive law -/

section Distribute

variable {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (𝓠 : ProbSpace) (V : Set Var)
  (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
  (hdom : ∀ i : ι, (𝓟 i).dom = V)

/-- The preimage of the support of `𝓟 i ⊗ 𝓠` under the pairing bijection is the rectangle of
the `i`-th summand. -/
lemma preimage_support_product (i : ι) :
    Nat.pairEquiv ⁻¹' (𝓟 i ⊗ 𝓠).support = sumProdRect 𝓟 𝓠 i := by
  rw [support_product, Set.preimage_image_eq _ Nat.pairEquiv.injective]
  rfl

/-- The scaling law for the measure underlying the left-hand side, on the support of the
`i`-th summand. -/
lemma prodMeasure_sum_of_subset_support {i : ι} (hi : ξ i ≠ 0) {H : Set ℕ}
    (hsub : H ⊆ (𝓟 i ⊗ 𝓠).support) :
    prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 H = ξ i * prodMeasure (𝓟 i) 𝓠 H := by
  rw [prodMeasure_apply, prodMeasure_apply]
  refine prodMeasure_of_subset_sumProdRect ξ 𝓟 𝓠 h hi ?_
  rw [← preimage_support_product 𝓟 𝓠 i]
  exact Set.preimage_mono hsub

/-- Null sets contained in the support of the `i`-th summand are the same for both sides. -/
lemma prodMeasure_eq_zero_iff {i : ι} (hi : ξ i ≠ 0) {N : Set ℕ}
    (hsub : N ⊆ (𝓟 i ⊗ 𝓠).support) :
    prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 N = 0 ↔ prodMeasure (𝓟 i) 𝓠 N = 0 := by
  rw [prodMeasure_sum_of_subset_support ξ 𝓟 𝓠 V h hdom hi hsub, mul_eq_zero]
  exact ⟨fun hc ↦ hc.resolve_left hi, fun hc ↦ Or.inr hc⟩

/-- A set contained in the support of `𝓟 i ⊗ 𝓠` that is measurable for the left-hand side is
measurable for `𝓟 i ⊗ 𝓠`. -/
lemma measurableSet_summand_of_left {i : ι} (hi : ξ i ≠ 0) {X : Set ℕ}
    (hXsub : X ⊆ (𝓟 i ⊗ 𝓠).support)
    (hX : ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace.MeasurableSet' X) :
    (𝓟 i ⊗ 𝓠).mspace.MeasurableSet' X := by
  obtain ⟨F, hF, hae⟩ := hX
  replace hae := ae_eq_set.mp hae
  refine ⟨F ∩ (𝓟 i ⊗ 𝓠).support, ?_, ?_⟩
  · change ((𝓟 i).mspace.prod 𝓠.mspace).MeasurableSet'
      (Nat.pairEquiv ⁻¹' (F ∩ (𝓟 i ⊗ 𝓠).support))
    rw [Set.preimage_inter, preimage_support_product 𝓟 𝓠 i]
    exact inter_sumProdRect_mem_summand ξ 𝓟 𝓠 hi hF
  · refine ae_eq_set.mpr ⟨?_, ?_⟩
    · refine (prodMeasure_eq_zero_iff ξ 𝓟 𝓠 V h hdom hi
        (fun x hx ↦ hXsub hx.1)).mp (measure_mono_null ?_ hae.1)
      intro x hx
      exact ⟨hx.1, fun hc ↦ hx.2 ⟨hc, hXsub hx.1⟩⟩
    · refine (prodMeasure_eq_zero_iff ξ 𝓟 𝓠 V h hdom hi
        (fun x hx ↦ hx.1.2)).mp (measure_mono_null ?_ hae.2)
      intro x hx
      exact ⟨hx.1.1, hx.2⟩

/-- A set contained in the support of `𝓟 i ⊗ 𝓠` that is measurable for `𝓟 i ⊗ 𝓠` is
measurable for the left-hand side. -/
lemma measurableSet_left_of_summand {i : ι} (hi : ξ i ≠ 0) {X : Set ℕ}
    (hXsub : X ⊆ (𝓟 i ⊗ 𝓠).support)
    (hX : (𝓟 i ⊗ 𝓠).mspace.MeasurableSet' X) :
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace.MeasurableSet' X := by
  obtain ⟨F, hF, hae⟩ := hX
  replace hae := ae_eq_set.mp hae
  refine ⟨F ∩ (𝓟 i ⊗ 𝓠).support, ?_, ?_⟩
  · change (((sum ξ 𝓟 V h hdom).mspace).prod 𝓠.mspace).MeasurableSet'
      (Nat.pairEquiv ⁻¹' (F ∩ (𝓟 i ⊗ 𝓠).support))
    rw [Set.preimage_inter, preimage_support_product 𝓟 𝓠 i]
    exact inter_sumProdRect_mem_sum ξ 𝓟 𝓠 h hF
  · refine ae_eq_set.mpr ⟨?_, ?_⟩
    · refine (prodMeasure_eq_zero_iff ξ 𝓟 𝓠 V h hdom hi
        (fun x hx ↦ hXsub hx.1)).mpr (measure_mono_null ?_ hae.1)
      intro x hx
      exact ⟨hx.1, fun hc ↦ hx.2 ⟨hc, hXsub hx.1⟩⟩
    · refine (prodMeasure_eq_zero_iff ξ 𝓟 𝓠 V h hdom hi
        (fun x hx ↦ hx.1.2)).mpr (measure_mono_null ?_ hae.2)
      intro x hx
      exact ⟨hx.1.1, hx.2⟩

/-- The common support of the two sides of the distributive law. -/
def sumProdSupport {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (𝓠 : ProbSpace) : Set ℕ :=
  ⋃ i ∈ {i : ι | ξ i ≠ 0}, (𝓟 i ⊗ 𝓠).support

lemma countable_xi_support : Set.Countable {i : ι | ξ i ≠ 0} := ξ.support_countable

lemma support_left_eq :
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).support = sumProdSupport ξ 𝓟 𝓠 := by
  rw [support_product, support_sum]
  ext k
  simp only [sumProdSupport, Set.mem_image, Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq,
    exists_prop]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    obtain ⟨i, hi, hai⟩ := ha
    exact ⟨i, hi, by rw [support_product]; exact ⟨(a, b), ⟨hai, hb⟩, rfl⟩⟩
  · rintro ⟨i, hi, hk⟩
    rw [support_product] at hk
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hk
    exact ⟨(a, b), ⟨⟨i, hi, ha⟩, hb⟩, rfl⟩

lemma support_right_eq :
    (sumProd ξ 𝓟 𝓠 V h hdom).support = sumProdSupport ξ 𝓟 𝓠 :=
  support_sum ξ (fun i ↦ 𝓟 i ⊗ 𝓠) (V ∪ 𝓠.dom) (sum_prod_disjoint 𝓠 h) (sum_prod_dom 𝓠 hdom)

/-- The complement of the common support is null for the measure of the left-hand side. -/
lemma prodMeasure_compl_sumProdSupport :
    prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 (sumProdSupport ξ 𝓟 𝓠)ᶜ = 0 := by
  set L := (sum ξ 𝓟 V h hdom) ⊗ 𝓠 with hL
  have h1 : L.meas (L.support)ᶜ = 0 := by
    rw [measure_compl (support_measurableSet L) (measure_ne_top _ _), measure_support L,
      @measure_univ ℕ L.mspace L.meas (isProbabilityMeasure_meas L), tsub_self]
  rwa [support_left_eq ξ 𝓟 𝓠 V h hdom] at h1

/-- The support of the `i`-th summand is measurable for the left-hand side. -/
lemma support_summand_measurableSet_left (i : ι) :
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace.MeasurableSet' (𝓟 i ⊗ 𝓠).support := by
  refine @MeasurableSet.nullMeasurableSet ℕ (prodMSpace (sum ξ 𝓟 V h hdom) 𝓠) _ _ ?_
  change (((sum ξ 𝓟 V h hdom).mspace).prod 𝓠.mspace).MeasurableSet'
    (Nat.pairEquiv ⁻¹' (𝓟 i ⊗ 𝓠).support)
  rw [preimage_support_product 𝓟 𝓠 i]
  exact sumProdRect_mem_prod_sum ξ 𝓟 𝓠 h i

/-- The two sides of the distributive law have the same σ-algebra. -/
lemma mspace_eq :
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace = (sumProd ξ 𝓟 𝓠 V h hdom).mspace := by
  refine MeasurableSpace.ext (fun E ↦ ⟨fun hE i hi ↦ ?_, fun hE ↦ ?_⟩)
  · refine measurableSet_summand_of_left ξ 𝓟 𝓠 V h hdom hi Set.inter_subset_right ?_
    exact @MeasurableSet.inter ℕ ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace _ _ hE
      (support_summand_measurableSet_left ξ 𝓟 𝓠 V h hdom i)
  · have hcount : Countable {i : ι | ξ i ≠ 0} :=
      (countable_xi_support ξ).to_subtype
    have hunion : E ∩ sumProdSupport ξ 𝓟 𝓠
        = ⋃ i : {i : ι | ξ i ≠ 0}, (E ∩ (𝓟 (i : ι) ⊗ 𝓠).support) := by
      rw [sumProdSupport, Set.biUnion_eq_iUnion, Set.inter_iUnion]
    have hpart : (E ∩ sumProdSupport ξ 𝓟 𝓠) ∪ (E \ sumProdSupport ξ 𝓟 𝓠) = E :=
      Set.inter_union_sdiff E _
    have hdiff : ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace.MeasurableSet'
        (E \ sumProdSupport ξ 𝓟 𝓠) := by
      refine NullMeasurableSet.of_null (measure_mono_null (fun x hx ↦ hx.2) ?_)
      exact prodMeasure_compl_sumProdSupport ξ 𝓟 𝓠 V h hdom
    have hinter : ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace.MeasurableSet'
        (E ∩ sumProdSupport ξ 𝓟 𝓠) := by
      rw [hunion]
      refine NullMeasurableSet.iUnion (fun i ↦ ?_)
      exact measurableSet_left_of_summand ξ 𝓟 𝓠 V h hdom i.2 Set.inter_subset_right (hE i i.2)
    rw [← hpart]
    exact @MeasurableSet.union ℕ ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace _ _ hinter hdiff

/-- On measurable sets, the two sides of the distributive law have the same measure. -/
lemma meas_agree_of_measurable {E : Set ℕ}
    (hE : (sumProd ξ 𝓟 𝓠 V h hdom).mspace.MeasurableSet' E) :
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).meas E = (sumProd ξ 𝓟 𝓠 V h hdom).meas E := by
  have hcount : Countable {i : ι | ξ i ≠ 0} := (countable_xi_support ξ).to_subtype
  have hRE : (sumProd ξ 𝓟 𝓠 V h hdom).meas E
      = ∑' i : ι, ξ i * prodMeasure (𝓟 i) 𝓠 (E ∩ (𝓟 i ⊗ 𝓠).support) :=
    sumMeasure_apply ξ (fun i ↦ 𝓟 i ⊗ 𝓠) hE
  have hsupp : Function.support
      (fun (i : ι) ↦ ξ i * prodMeasure (𝓟 i) 𝓠 (E ∩ (𝓟 i ⊗ 𝓠).support)) ⊆ {i : ι | ξ i ≠ 0} := by
    intro i hi
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hi
    exact hi.1
  have hsub : ∀ i : ι, E ∩ (𝓟 i ⊗ 𝓠).support ⊆ (𝓟 i ⊗ 𝓠).support :=
    fun _ ↦ Set.inter_subset_right
  have hnm : ∀ i : {i : ι | ξ i ≠ 0},
      ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace.MeasurableSet' (E ∩ (𝓟 (i : ι) ⊗ 𝓠).support) :=
    fun i ↦ measurableSet_left_of_summand ξ 𝓟 𝓠 V h hdom i.2 (hsub i)
      (hE i i.2)
  have hdisj : Pairwise (fun (a b : {i : ι | ξ i ≠ 0}) ↦
      @AEDisjoint ℕ (prodMSpace (sum ξ 𝓟 V h hdom) 𝓠) (prodMeasure (sum ξ 𝓟 V h hdom) 𝓠)
        (E ∩ (𝓟 (a : ι) ⊗ 𝓠).support) (E ∩ (𝓟 (b : ι) ⊗ 𝓠).support)) := by
    intro a b hab
    refine Disjoint.aedisjoint ?_
    exact ((sum_prod_disjoint 𝓠 h (fun hc ↦ hab (Subtype.ext hc))).mono
      Set.inter_subset_right Set.inter_subset_right)
  have hunion : E ∩ sumProdSupport ξ 𝓟 𝓠
      = ⋃ i : {i : ι | ξ i ≠ 0}, (E ∩ (𝓟 (i : ι) ⊗ 𝓠).support) := by
    rw [sumProdSupport, Set.biUnion_eq_iUnion, Set.inter_iUnion]
  have hstep : prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 (E ∩ sumProdSupport ξ 𝓟 𝓠)
      = ∑' i : {i : ι | ξ i ≠ 0},
        prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 (E ∩ (𝓟 (i : ι) ⊗ 𝓠).support) := by
    rw [hunion]
    exact measure_iUnion₀ hdisj hnm
  have hfull : prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 (E ∩ sumProdSupport ξ 𝓟 𝓠)
      = prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 E := by
    refine le_antisymm (measure_mono Set.inter_subset_left) ?_
    have hd : prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 (E \ sumProdSupport ξ 𝓟 𝓠) = 0 :=
      measure_mono_null (fun x hx ↦ hx.2) (prodMeasure_compl_sumProdSupport ξ 𝓟 𝓠 V h hdom)
    calc prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 E
        = prodMeasure (sum ξ 𝓟 V h hdom) 𝓠
            ((E ∩ sumProdSupport ξ 𝓟 𝓠) ∪ (E \ sumProdSupport ξ 𝓟 𝓠)) := by
          rw [Set.inter_union_sdiff]
      _ ≤ prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 (E ∩ sumProdSupport ξ 𝓟 𝓠)
            + prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 (E \ sumProdSupport ξ 𝓟 𝓠) := measure_union_le _ _
      _ = prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 (E ∩ sumProdSupport ξ 𝓟 𝓠) := by rw [hd, add_zero]
  rw [hRE, ← tsum_subtype_eq_of_support_subset hsupp]
  change prodMeasure (sum ξ 𝓟 V h hdom) 𝓠 E = _
  rw [← hfull, hstep]
  refine tsum_congr (fun i ↦ ?_)
  exact prodMeasure_sum_of_subset_support ξ 𝓟 𝓠 V h hdom i.2 (hsub i)

/-- The two sides of the distributive law have the same measure, on *all* sets. -/
lemma meas_eq (E : Set ℕ) :
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).meas E = (sumProd ξ 𝓟 𝓠 V h hdom).meas E := by
  refine le_antisymm ?_ ?_
  · obtain ⟨t, hEt, ht, hteq⟩ := @exists_measurable_superset ℕ (sumProd ξ 𝓟 𝓠 V h hdom).mspace
      (sumProd ξ 𝓟 𝓠 V h hdom).meas E
    calc ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).meas E ≤ ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).meas t := measure_mono hEt
      _ = (sumProd ξ 𝓟 𝓠 V h hdom).meas t := meas_agree_of_measurable ξ 𝓟 𝓠 V h hdom ht
      _ = (sumProd ξ 𝓟 𝓠 V h hdom).meas E := hteq
  · obtain ⟨t, hEt, ht, hteq⟩ := @exists_measurable_superset ℕ ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace
      ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).meas E
    have ht' : (sumProd ξ 𝓟 𝓠 V h hdom).mspace.MeasurableSet' t := by
      rw [← mspace_eq ξ 𝓟 𝓠 V h hdom]; exact ht
    calc (sumProd ξ 𝓟 𝓠 V h hdom).meas E ≤ (sumProd ξ 𝓟 𝓠 V h hdom).meas t := measure_mono hEt
      _ = ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).meas t := (meas_agree_of_measurable ξ 𝓟 𝓠 V h hdom ht').symm
      _ = ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).meas E := hteq

/-! ### The states -/

lemma product_state (p q : ProbSpace) (k : ℕ) :
    (p ⊗ q).state k =
      Mem.union (p.state (Nat.pairEquiv.symm k).1) (q.state (Nat.pairEquiv.symm k).2) := rfl

lemma mem_support_product_iff {p q : ProbSpace} {k : ℕ} :
    k ∈ (p ⊗ q).support ↔
      (Nat.pairEquiv.symm k).1 ∈ p.support ∧ (Nat.pairEquiv.symm k).2 ∈ q.support := by
  rw [support_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨Nat.pairEquiv.symm k, ⟨ha, hb⟩, Equiv.apply_symm_apply _ _⟩

/-- Because the summands have disjoint supports, a point of the support determines its
summand. -/
lemma sum_index_unique (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    {c c' : ι} {n : ℕ}
    (hc : n ∈ (𝓟 c).support) (hc' : n ∈ (𝓟 c').support) : c = c' := by
  by_contra hne
  exact Set.disjoint_left.mp (h hne) hc hc'

/-- On their common support, the two sides of the distributive law have the same state. -/
lemma state_eq_on_support {k : ℕ} (hk : k ∈ sumProdSupport ξ 𝓟 𝓠) :
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).state k = (sumProd ξ 𝓟 𝓠 V h hdom).state k := by
  classical
  obtain ⟨c, hc, hkc⟩ : ∃ c, ξ c ≠ 0 ∧ k ∈ (𝓟 c ⊗ 𝓠).support := by
    simpa only [sumProdSupport, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using hk
  have hi : (Nat.pairEquiv.symm k).1 ∈ (𝓟 c).support := (mem_support_product_iff.mp hkc).1
  have hexL : ∃ a, (Nat.pairEquiv.symm k).1 ∈ (𝓟 a).support := ⟨c, hi⟩
  have hexR : ∃ a, k ∈ (𝓟 a ⊗ 𝓠).support := ⟨c, hkc⟩
  have hL : ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).state k =
      Mem.union ((𝓟 c).state (Nat.pairEquiv.symm k).1) (𝓠.state (Nat.pairEquiv.symm k).2) := by
    rw [product_state]
    have hstate : (sum ξ 𝓟 V h hdom).state (Nat.pairEquiv.symm k).1
        = (𝓟 c).state (Nat.pairEquiv.symm k).1 := by
      change sumState 𝓟 V (Nat.pairEquiv.symm k).1 = _
      rw [sumState, dif_pos hexL, sum_index_unique 𝓟 h hexL.choose_spec hi]
    rw [hstate]
  have hR : (sumProd ξ 𝓟 𝓠 V h hdom).state k =
      Mem.union ((𝓟 c).state (Nat.pairEquiv.symm k).1) (𝓠.state (Nat.pairEquiv.symm k).2) := by
    change sumState (fun a ↦ 𝓟 a ⊗ 𝓠) (V ∪ 𝓠.dom) k = _
    rw [sumState, dif_pos hexR,
      sum_index_unique 𝓟 h (mem_support_product_iff.mp hexR.choose_spec).1 hi, product_state]
  rw [hL, hR]

/-! ### The distributive law -/

/--
The distributive law of products over sums.

The equality of `ProbSpace` structures is false (see the discussion in
`PcolIris/OProp/ProbSpace.lean`); what does hold is that the two sides have the same
σ-algebra, the same measure (on *all* sets, not only the measurable ones), the same domain,
the same support, and the same state at every point of that support.
-/
theorem sum_prod_distribute :
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).mspace = (sumProd ξ 𝓟 𝓠 V h hdom).mspace ∧
    (∀ E : Set ℕ, ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).meas E = (sumProd ξ 𝓟 𝓠 V h hdom).meas E) ∧
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).dom = (sumProd ξ 𝓟 𝓠 V h hdom).dom ∧
    ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).support = (sumProd ξ 𝓟 𝓠 V h hdom).support ∧
    (∀ k ∈ ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).support,
      ((sum ξ 𝓟 V h hdom) ⊗ 𝓠).state k = (sumProd ξ 𝓟 𝓠 V h hdom).state k) := by
  refine ⟨mspace_eq ξ 𝓟 𝓠 V h hdom, meas_eq ξ 𝓟 𝓠 V h hdom, rfl, ?_, ?_⟩
  · rw [support_left_eq ξ 𝓟 𝓠 V h hdom, support_right_eq ξ 𝓟 𝓠 V h hdom]
  · intro k hk
    rw [support_left_eq ξ 𝓟 𝓠 V h hdom] at hk
    exact state_eq_on_support ξ 𝓟 𝓠 V h hdom hk

end Distribute

end ProbSpace

end Pcol
