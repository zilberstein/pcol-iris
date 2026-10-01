/-
Regrouping sums of probability spaces.

A sum can be reindexed along an injective map (`sum_map_le`, `le_sum_map`), and a sum of sums
whose weights have disjoint supports is the sum over the combined weights
(`sum_nested_le`, `le_sum_nested`).  These are the laws behind the regrouping of outcome
conjunctions.
-/
import PcolIris.OProp.SumLaws

namespace Pcol

open MeasureTheory

namespace ProbSpace

/-- The domain parameter of a sum is only a name for the common domain of the summands. -/
lemma sum_dom_congr {ι : Type} {ξ : PMF ι} {𝓟 : ι → ProbSpace} {V V' : Set Var}
    {hd : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support}
    {hdom : ∀ i, (𝓟 i).dom = V} {hdom' : ∀ i, (𝓟 i).dom = V'} (h : V = V') :
    sum ξ 𝓟 V hd hdom ≤ sum ξ 𝓟 V' hd hdom' := by
  subst h; exact le_refl _

section Reindex

variable {α β : Type} {p : PMF α} {e : α → β} (he : Function.Injective e) {𝓡 : β → ProbSpace}
  {V : Set Var} (hd : ∀ {i j : β}, i ≠ j → Disjoint (𝓡 i).support (𝓡 j).support)
  (hdom : ∀ i, (𝓡 i).dom = V)

include he hd in
lemma comp_disjoint : ∀ {i j : α}, i ≠ j → Disjoint (𝓡 (e i)).support (𝓡 (e j)).support :=
  fun hij ↦ hd (he.ne hij)

lemma map_apply_ne_zero_iff {j : β} : p.map e j ≠ 0 ↔ ∃ i, p i ≠ 0 ∧ e i = j := by
  rw [← PMF.mem_support_iff, PMF.mem_support_map_iff]
  simp only [PMF.mem_support_iff]

include he in
lemma mem_sum_map_iff {E : Set ℕ} :
    E ∈ sum (p.map e) 𝓡 V hd hdom ↔ E ∈ sum p (𝓡 ∘ e) V (comp_disjoint he hd) (fun _ ↦ hdom _) := by
  constructor
  · intro hE i hi
    exact hE (e i) (map_apply_ne_zero_iff.mpr ⟨i, hi, rfl⟩)
  · intro hE j hj
    obtain ⟨i, hi, rfl⟩ := map_apply_ne_zero_iff.mp hj
    exact hE i hi

include he in
lemma sum_map_meas {E : Set ℕ} (hE : E ∈ sum (p.map e) 𝓡 V hd hdom) :
    (sum (p.map e) 𝓡 V hd hdom).meas E =
      (sum p (𝓡 ∘ e) V (comp_disjoint he hd) (fun _ ↦ hdom _)).meas E := by
  classical
  change sumMeasure _ _ E = sumMeasure _ _ E
  rw [sumMeasure_apply _ _ hE, sumMeasure_apply _ _ ((mem_sum_map_iff he hd hdom).mp hE),
    sumMeasureFun, sumMeasureFun]
  have key : ∀ j, (p.map e) j * (𝓡 j).meas (E ∩ (𝓡 j).support) =
      ∑' i, if j = e i then p i * (𝓡 j).meas (E ∩ (𝓡 j).support) else 0 := fun j ↦ by
    rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun i ↦ ?_
    split_ifs <;> simp
  change ∑' j, (p.map e) j * (𝓡 j).meas (E ∩ (𝓡 j).support) =
    ∑' i, p i * (𝓡 (e i)).meas (E ∩ (𝓡 (e i)).support)
  rw [tsum_congr key, ENNReal.tsum_comm]
  refine tsum_congr fun i ↦ ?_
  rw [tsum_eq_single (e i) fun j hj ↦ if_neg hj, if_pos rfl]

include he in
lemma sum_map_state (n : ℕ) (i : α) (hn : n ∈ (𝓡 (e i)).support) :
    (sum (p.map e) 𝓡 V hd hdom).state n =
      (sum p (𝓡 ∘ e) V (comp_disjoint he hd) (fun _ ↦ hdom _)).state n := by
  change sumState 𝓡 V n = sumState (𝓡 ∘ e) V n
  rw [sumState_of_mem hd hn, sumState_of_mem (𝓟 := 𝓡 ∘ e) (comp_disjoint he hd) hn]
  rfl

include he in
theorem sum_map_le :
    sum (p.map e) 𝓡 V hd hdom ≤ sum p (𝓡 ∘ e) V (comp_disjoint he hd) (fun _ ↦ hdom _) := by
  refine le_of_id (fun E h ↦ (mem_sum_map_iff he hd hdom).mp h) (fun E hE ↦ ?_) subset_rfl
    fun n hn ↦ ?_
  · refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]; exact sum_map_meas he hd hdom hE
  · rw [support_sum] at hn
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn
    obtain ⟨i, -, hni⟩ := hn
    exact le_of_eq (sum_map_state he hd hdom n i hni)

include he in
theorem le_sum_map :
    sum p (𝓡 ∘ e) V (comp_disjoint he hd) (fun _ ↦ hdom _) ≤ sum (p.map e) 𝓡 V hd hdom := by
  refine le_of_id (fun E h ↦ (mem_sum_map_iff he hd hdom).mpr h) (fun E hE ↦ ?_) subset_rfl
    fun n hn ↦ ?_
  · refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    exact (sum_map_meas he hd hdom ((mem_sum_map_iff he hd hdom).mpr hE)).symm
  · rw [support_sum] at hn
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn
    obtain ⟨j, hj, hnj⟩ := hn
    obtain ⟨i, -, rfl⟩ := map_apply_ne_zero_iff.mp hj
    exact le_of_eq (sum_map_state he hd hdom n i hnj).symm

end Reindex

section Nested

variable {ι κ : Type} {ξ : PMF κ} {ζ : κ → PMF ι} {𝓟 : ι → ProbSpace} {V : Set Var}
  (hd : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
  (hdom : ∀ i, (𝓟 i).dom = V)
  (hζ : ∀ {k k' : κ}, k ≠ k' → Disjoint (ζ k).support (ζ k').support)


lemma subset_support_inner {k : κ} {i : ι} (hi : ζ k i ≠ 0) :
    (𝓟 i).support ⊆ (sum (ζ k) 𝓟 V hd hdom).support := by
  rw [support_sum]
  exact Set.subset_biUnion_of_mem (u := fun i ↦ (𝓟 i).support) (show i ∈ {i | ζ k i ≠ 0} from hi)

include hζ in
lemma nested_disjoint {k k' : κ} (hkk' : k ≠ k') :
    Disjoint (sum (ζ k) 𝓟 V hd hdom).support (sum (ζ k') 𝓟 V hd hdom).support := by
  rw [support_sum, support_sum, Set.disjoint_left]
  intro n hn hn'
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn hn'
  obtain ⟨i, hi, hni⟩ := hn
  obtain ⟨i', hi', hni'⟩ := hn'
  by_cases hii : i = i'
  · subst hii
    exact Set.disjoint_left.mp (hζ hkk') ((PMF.mem_support_iff _ _).mpr hi)
      ((PMF.mem_support_iff _ _).mpr hi')
  · exact Set.disjoint_left.mp (hd hii) hni hni'

lemma inter_support_inner {E : Set ℕ} {k : κ} {i : ι} (hi : ζ k i ≠ 0) :
    (E ∩ (sum (ζ k) 𝓟 V hd hdom).support) ∩ (𝓟 i).support = E ∩ (𝓟 i).support := by
  rw [Set.inter_assoc, Set.inter_eq_right.mpr (subset_support_inner hd hdom hi)]

lemma mem_nested_iff {E : Set ℕ} :
    E ∈ sum ξ (fun k ↦ sum (ζ k) 𝓟 V hd hdom) V (nested_disjoint hd hdom hζ) (fun _ ↦ rfl) ↔
      E ∈ sum (ξ.bind ζ) 𝓟 V hd hdom := by
  constructor
  · intro hE i hi
    obtain ⟨k, hk, hik⟩ := (PMF.mem_support_bind_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hi)
    have hik' : ζ k i ≠ 0 := (PMF.mem_support_iff _ _).mp hik
    have := hE k ((PMF.mem_support_iff _ _).mp hk) i hik'
    rwa [inter_support_inner hd hdom hik'] at this
  · intro hE k hk i hi
    rw [inter_support_inner hd hdom hi]
    exact hE i ((PMF.mem_support_iff _ _).mp ((PMF.mem_support_bind_iff _ _ _).mpr
      ⟨k, (PMF.mem_support_iff _ _).mpr hk, (PMF.mem_support_iff _ _).mpr hi⟩))

lemma nested_meas {E : Set ℕ}
    (hE : E ∈ sum ξ (fun k ↦ sum (ζ k) 𝓟 V hd hdom) V (nested_disjoint hd hdom hζ)
      (fun _ ↦ rfl)) :
    (sum ξ (fun k ↦ sum (ζ k) 𝓟 V hd hdom) V (nested_disjoint hd hdom hζ) (fun _ ↦ rfl)).meas E =
      (sum (ξ.bind ζ) 𝓟 V hd hdom).meas E := by
  classical
  have hE' := (mem_nested_iff hd hdom hζ).mp hE
  change sumMeasure _ _ E = sumMeasure _ _ E
  rw [sumMeasure_apply _ _ hE, sumMeasure_apply _ _ hE', sumMeasureFun, sumMeasureFun]
  have hk : ∀ k, ξ k * (sum (ζ k) 𝓟 V hd hdom).meas (E ∩ (sum (ζ k) 𝓟 V hd hdom).support) =
      ∑' i, ξ k * (ζ k i * (𝓟 i).meas (E ∩ (𝓟 i).support)) := by
    intro k
    by_cases hξ : ξ k = 0
    · simp [hξ]
    change ξ k * sumMeasure (ζ k) 𝓟 _ = _
    rw [sumMeasure_apply _ _ (hE k hξ), sumMeasureFun, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun i ↦ ?_
    by_cases hζi : ζ k i = 0
    · simp [hζi]
    · rw [inter_support_inner hd hdom hζi]
  change ∑' k, ξ k * (sum (ζ k) 𝓟 V hd hdom).meas (E ∩ (sum (ζ k) 𝓟 V hd hdom).support) = _
  rw [tsum_congr hk, ENNReal.tsum_comm]
  refine tsum_congr fun i ↦ ?_
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  exact tsum_congr fun k ↦ by rw [mul_assoc]

lemma nested_state {n : ℕ} {k : κ} {i : ι} (hi : ζ k i ≠ 0) (hn : n ∈ (𝓟 i).support) :
    (sum ξ (fun k ↦ sum (ζ k) 𝓟 V hd hdom) V (nested_disjoint hd hdom hζ) (fun _ ↦ rfl)).state n =
      (sum (ξ.bind ζ) 𝓟 V hd hdom).state n := by
  change sumState (fun k ↦ sum (ζ k) 𝓟 V hd hdom) V n = sumState 𝓟 V n
  rw [sumState_of_mem (nested_disjoint hd hdom hζ) (subset_support_inner hd hdom hi hn)]
  rfl

/-- A sum of sums whose weights have disjoint supports is below the sum over the combined
weights. -/
theorem sum_nested_le :
    sum ξ (fun k ↦ sum (ζ k) 𝓟 V hd hdom) V (nested_disjoint hd hdom hζ) (fun _ ↦ rfl) ≤
      sum (ξ.bind ζ) 𝓟 V hd hdom := by
  refine le_of_id (fun E h ↦ (mem_nested_iff hd hdom hζ).mp h) (fun E hE ↦ ?_) subset_rfl
    fun n hn ↦ ?_
  · refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]; exact nested_meas hd hdom hζ hE
  · rw [support_sum] at hn
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn
    obtain ⟨i, hi, hni⟩ := hn
    obtain ⟨k, -, hik⟩ := (PMF.mem_support_bind_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hi)
    exact le_of_eq (nested_state hd hdom hζ ((PMF.mem_support_iff _ _).mp hik) hni)

/-- The sum over combined weights is below the corresponding sum of sums. -/
theorem le_sum_nested :
    sum (ξ.bind ζ) 𝓟 V hd hdom ≤
      sum ξ (fun k ↦ sum (ζ k) 𝓟 V hd hdom) V (nested_disjoint hd hdom hζ) (fun _ ↦ rfl) := by
  refine le_of_id (fun E h ↦ (mem_nested_iff hd hdom hζ).mpr h) (fun E hE ↦ ?_) subset_rfl
    fun n hn ↦ ?_
  · refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    exact (nested_meas hd hdom hζ ((mem_nested_iff hd hdom hζ).mpr hE)).symm
  · rw [support_sum] at hn
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn
    obtain ⟨k, -, hnk⟩ := hn
    rw [support_sum] at hnk
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hnk
    obtain ⟨i, hi, hni⟩ := hnk
    exact le_of_eq (nested_state hd hdom hζ hi hni).symm

end Nested

end ProbSpace

end Pcol
