/-
Laws of sums of probability spaces: moving a space to a chosen part of the outcomes
(`ProbSpace.shift`), and monotonicity of sums (Lemma B.5 of the paper).
-/
import PcolIris.OProp.ProductLaws

namespace Pcol

open MeasureTheory

namespace ProbSpace

/-! ### Supports -/

lemma meas_compl_support (p : ProbSpace) : p.meas p.supportᶜ = 0 := by
  rw [measure_compl (support_measurableSet p) (measure_ne_top _ _), measure_support p,
    measure_univ, tsub_self]

lemma meas_inter_support (p : ProbSpace) (A : Set ℕ) :
    (@ProbabilityMeasure.toMeasure ℕ p.mspace p.μ) (A ∩ p.support) =
      (@ProbabilityMeasure.toMeasure ℕ p.mspace p.μ) A :=
  measure_inter_conull (meas_compl_support p)

/-! ### Shifting a space to the outcomes `(c, n)` -/

/-- The encoding of the outcome `n` in the `c`-th copy of `ℕ`. -/
def shiftMap (c : ℕ) (n : ℕ) : ℕ := Nat.pairEquiv (c, n)

lemma shiftMap_injective (c : ℕ) : Function.Injective (shiftMap c) := by
  intro n n' h
  have := congrArg Prod.snd (Nat.pairEquiv.injective h)
  exact this

/-- The space `p`, with its outcome `n` renamed to `shiftMap c n`. -/
noncomputable def shift (p : ProbSpace) (c : ℕ) : ProbSpace where
  mspace := p.mspace.map (shiftMap c)
  μ := ⟨@Measure.map ℕ ℕ p.mspace (p.mspace.map (shiftMap c)) (shiftMap c) p.meas, by
    constructor
    rw [@Measure.map_apply ℕ ℕ p.mspace (p.mspace.map (shiftMap c)) p.meas (shiftMap c)
      (measurable_iff_le_map.mpr le_rfl) Set.univ MeasurableSet.univ, Set.preimage_univ]
    exact @measure_univ ℕ p.mspace p.meas p.μ.2⟩
  dom := p.dom
  state m := p.state (Nat.pairEquiv.symm m).2
  dom_valid _ := p.dom_valid _
  complete := by
    constructor
    intro s hs
    have hle := @Measure.le_map_apply ℕ ℕ p.mspace (p.mspace.map (shiftMap c)) p.meas
      (shiftMap c) ⟨shiftMap c, measurable_iff_le_map.mpr le_rfl, Filter.EventuallyEq.rfl⟩ s
    have h0 : p.meas (shiftMap c ⁻¹' s) = 0 := le_antisymm (hs ▸ hle) bot_le
    exact p.complete.out _ h0

lemma shift_measurableSet {p : ProbSpace} {c : ℕ} {E : Set ℕ} :
    (p.shift c).mspace.MeasurableSet' E ↔ p.mspace.MeasurableSet' (shiftMap c ⁻¹' E) :=
  Iff.rfl

lemma shift_meas (p : ProbSpace) (c : ℕ) {E : Set ℕ}
    (hE : (p.shift c).mspace.MeasurableSet' E) : (p.shift c).meas E = p.meas (shiftMap c ⁻¹' E) :=
  @Measure.map_apply ℕ ℕ p.mspace (p.mspace.map (shiftMap c)) p.meas (shiftMap c)
    (measurable_iff_le_map.mpr le_rfl) E hE

lemma shift_state (p : ProbSpace) (c n : ℕ) : (p.shift c).state (shiftMap c n) = p.state n := by
  change p.state (Nat.pairEquiv.symm (Nat.pairEquiv (c, n))).2 = p.state n
  rw [Equiv.symm_apply_apply]

/-- The outcomes of a shifted space lie in the `c`-th copy of `ℕ`. -/
lemma support_shift_subset (p : ProbSpace) (c : ℕ) :
    (p.shift c).support ⊆ Set.range (shiftMap c) := by
  have hm : (p.shift c).mspace.MeasurableSet' (Set.range (shiftMap c)) := by
    rw [shift_measurableSet, Set.preimage_range]; exact @MeasurableSet.univ ℕ p.mspace
  refine support_subset hm ?_
  rw [shift_meas p c hm, Set.preimage_range]
  exact measure_univ

lemma disjoint_support_shift (p q : ProbSpace) {c c' : ℕ} (h : c ≠ c') :
    Disjoint (p.shift c).support (q.shift c').support := by
  refine Set.disjoint_left.mpr fun m hm hm' ↦ ?_
  obtain ⟨n, rfl⟩ := support_shift_subset p c hm
  obtain ⟨n', hn'⟩ := support_shift_subset q c' hm'
  exact h (congrArg Prod.fst (Nat.pairEquiv.injective hn')).symm

/-- Products of spaces with disjoint supports have disjoint supports. -/
lemma disjoint_support_product' {p p' q q' : ProbSpace} (hd : Disjoint p.support p'.support) :
    Disjoint (p ⊗ q).support (p' ⊗ q').support := by
  rw [support_product, support_product, Set.disjoint_left]
  rintro _ ⟨⟨i, j⟩, ⟨hi, -⟩, rfl⟩ ⟨⟨i', j'⟩, ⟨hi', -⟩, heq⟩
  have := congrArg Prod.fst (Nat.pairEquiv.injective heq)
  simp only at this
  subst this
  exact Set.disjoint_left.mp hd hi hi'

lemma shift_le (p : ProbSpace) (c : ℕ) : p.shift c ≤ p := by
  refine ⟨shiftMap c, fun E hE ↦ hE, fun E hE ↦ ?_, le_rfl, fun n _ ↦ le_of_eq (shift_state p c n)⟩
  refine ENNReal.coe_injective ?_
  rw [prob_coe, prob_coe]
  exact (shift_meas p c hE).symm

lemma le_shift (p : ProbSpace) (c : ℕ) : p ≤ p.shift c := by
  refine ⟨fun m ↦ (Nat.pairEquiv.symm m).2, fun E hE ↦ ?_, fun E hE ↦ ?_, le_rfl,
    fun m _ ↦ le_refl _⟩
  · change p.mspace.MeasurableSet' (shiftMap c ⁻¹' ((fun m ↦ (Nat.pairEquiv.symm m).2) ⁻¹' E))
    convert hE using 1
    ext n; simp [shiftMap]
  · have hE' : (p.shift c).mspace.MeasurableSet' ((fun m ↦ (Nat.pairEquiv.symm m).2) ⁻¹' E) := by
      change p.mspace.MeasurableSet' (shiftMap c ⁻¹' ((fun m ↦ (Nat.pairEquiv.symm m).2) ⁻¹' E))
      convert hE using 1
      ext n; simp [shiftMap]
    refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    change (p.shift c).meas _ = p.meas E
    rw [shift_meas p c hE']
    congr 1
    ext n; simp [shiftMap]

/-! ### Monotonicity of sums (Lemma B.5) -/

section SumMono

variable {ι : Type} {ξ : PMF ι}

lemma sumState_of_mem {𝓟 : ι → ProbSpace} {V : Set Var}
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) {v : ι} {n : ℕ}
    (hn : n ∈ (𝓟 v).support) : sumState 𝓟 V n = (𝓟 v).state n := by
  classical
  have hex : ∃ i, n ∈ (𝓟 i).support := ⟨v, hn⟩
  rw [sumState, dif_pos hex]
  have : hex.choose = v := by
    by_contra hne; exact Set.disjoint_left.mp (h hne) hex.choose_spec hn
  rw [this]

/-- Sums are monotone: if each summand of positive weight grows, then so does the sum. -/
theorem sum_mono {𝓟 𝓠 : ι → ProbSpace} {V W : Set Var}
    (hP : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    (hQ : ∀ {i j : ι}, i ≠ j → Disjoint (𝓠 i).support (𝓠 j).support)
    (hdP : ∀ i, (𝓟 i).dom = V) (hdQ : ∀ i, (𝓠 i).dom = W) (hVW : V ⊆ W)
    (h : ∀ v, ξ v ≠ 0 → 𝓟 v ≤ 𝓠 v) : sum ξ 𝓟 V hP hdP ≤ sum ξ 𝓠 W hQ hdQ := by
  classical
  choose g hg using h
  have hgeq : ∀ a b (e : a = b) (ha : ξ a ≠ 0) (hb : ξ b ≠ 0) (n : ℕ), g a ha n = g b hb n := by
    intro a b e; subst e; intros; rfl
  let G : ℕ → ℕ := fun n ↦
    if hex : ∃ v, ξ v ≠ 0 ∧ n ∈ (𝓠 v).support then g hex.choose hex.choose_spec.1 n else 0
  have hG : ∀ v (hv : ξ v ≠ 0), ∀ n ∈ (𝓠 v).support, G n = g v hv n := by
    intro v hv n hn
    have hex : ∃ v, ξ v ≠ 0 ∧ n ∈ (𝓠 v).support := ⟨v, hv, hn⟩
    simp only [G, dif_pos hex]
    refine hgeq _ _ ?_ _ _ n
    by_contra hne; exact Set.disjoint_left.mp (hQ hne) hex.choose_spec.2 hn
  have hpre : ∀ v (hv : ξ v ≠ 0) (E : Set ℕ),
      G ⁻¹' E ∩ (𝓠 v).support = g v hv ⁻¹' (E ∩ (𝓟 v).support) ∩ (𝓠 v).support := by
    intro v hv E; ext n
    constructor
    · rintro ⟨hE, hn⟩
      refine ⟨⟨?_, (hg v hv).mem_support hn⟩, hn⟩
      rw [← hG v hv n hn]; exact hE
    · rintro ⟨⟨hE, -⟩, hn⟩
      exact ⟨by rw [Set.mem_preimage, hG v hv n hn]; exact hE, hn⟩
  have hmeas : ∀ E, (sumMSpace ξ 𝓟).MeasurableSet' E →
      (sumMSpace ξ 𝓠).MeasurableSet' (G ⁻¹' E) := by
    intro E hE v hv
    rw [hpre v hv E]
    exact @MeasurableSet.inter ℕ (𝓠 v).mspace _ _ ((hg v hv).mspace _ (hE v hv))
      (support_measurableSet _)
  refine ⟨G, hmeas, fun E hE ↦ ?_, hVW, fun n hn ↦ ?_⟩
  · refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    change sumMeasure ξ 𝓠 (G ⁻¹' E) = sumMeasure ξ 𝓟 E
    rw [sumMeasure_apply ξ 𝓠 (hmeas E hE), sumMeasure_apply ξ 𝓟 hE, sumMeasureFun,
      sumMeasureFun]
    refine tsum_congr fun v ↦ ?_
    by_cases hv : ξ v = 0
    · simp [hv]
    · congr 1
      rw [← prob_coe, ← prob_coe, ← ENNReal.coe_inj.mpr ((hg v hv).μ _ (hE v hv)), prob_coe,
        prob_coe, hpre v hv E, meas_inter_support]
  · rw [support_sum] at hn
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn
    obtain ⟨v, hv, hn⟩ := hn
    change sumState 𝓟 V (G n) ≤ sumState 𝓠 W n
    rw [sumState_of_mem hQ hn, hG v hv n hn, sumState_of_mem hP ((hg v hv).mem_support hn)]
    exact (hg v hv).state n hn

/-- A sum over a point mass is (below) its summand. -/
theorem sum_pure_le {𝓟 : ι → ProbSpace} {V : Set Var}
    (hP : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    (hdP : ∀ i, (𝓟 i).dom = V) (i : ι) : sum (PMF.pure i) 𝓟 V hP hdP ≤ 𝓟 i := by
  classical
  have hmeas : ∀ E, (sumMSpace (PMF.pure i) 𝓟).MeasurableSet' E →
      (𝓟 i).mspace.MeasurableSet' E := by
    intro E hE
    have h1 := hE i (by simp)
    have hnull : (𝓟 i).meas (E \ (𝓟 i).support) = 0 :=
      measure_mono_null (Set.diff_subset_compl _ _) (meas_compl_support _)
    have h2 := (𝓟 i).complete.out _ hnull
    have := @MeasurableSet.union ℕ (𝓟 i).mspace _ _ h1 h2
    rwa [Set.inter_union_sdiff] at this
  refine le_of_id hmeas (fun E hE ↦ ?_) (hdP i).symm.subset
    (fun n hn ↦ le_of_eq (sumState_of_mem hP hn))
  refine ENNReal.coe_injective ?_
  rw [prob_coe, prob_coe]
  change sumMeasure (PMF.pure i) 𝓟 E = _
  rw [sumMeasure_apply _ _ hE, sumMeasureFun, tsum_eq_single i]
  · rw [PMF.pure_apply_self, one_mul, meas_inter_support]
  · intro j hj; rw [PMF.pure_apply_of_ne _ _ hj, zero_mul]

end SumMono

end ProbSpace

end Pcol
