/-
Refinement of probability spaces by distributions.

A distribution `ν` refines a space `𝓡` exactly when `𝓡` is below the discrete space of some
representation of `ν` (`ProbSpace.ofPMF`).  This makes it possible to use the laws of the
order on spaces to reason about refinement, e.g. to add to `𝓡` the variables that `ν`
allocates (`Distr.Refines.pad`).
-/
import PcolIris.OProp.TrivialSpace
import PcolIris.OProp.SumLaws
import PcolIris.OProp.OProp

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

/-- The product of two discrete spaces is below the discrete space of the product
distribution (whose outcomes are encoded pairs), when the memories of the latter extend the
unions of the memories of the factors. -/
theorem ofPMF_product_le (Ξ P : PMF ℕ) (f s F : ℕ → Mem) (D E : Set Var)
    (hF : ∀ k ∈ Ξ.support, ∀ j ∈ P.support, D ∪ E ⊆ (F (Nat.pairEquiv (k, j))).dom ∧
      ((ofPMF Ξ f D).state k ⊎ (ofPMF P s E).state j) ≤ F (Nat.pairEquiv (k, j))) :
    (ofPMF Ξ f D ⊗ ofPMF P s E) ≤
      ofPMF (Ξ.bind fun k ↦ P.map fun j ↦ Nat.pairEquiv (k, j)) F (D ∪ E) := by
  set Ξ' := Ξ.bind fun k ↦ P.map fun j ↦ Nat.pairEquiv (k, j)
  have hsupp : ∀ n ∈ Ξ'.support, ∃ k ∈ Ξ.support, ∃ j ∈ P.support, n = Nat.pairEquiv (k, j) := by
    intro n hn
    obtain ⟨k, hk, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
    obtain ⟨j, hj, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    exact ⟨k, hk, j, hj, rfl⟩
  refine le_of_id (fun _ _ ↦ MeasurableSpace.measurableSet_top) (fun E' _ ↦ ?_) subset_rfl
    fun n hn ↦ ?_
  · refine ENNReal.coe_injective ?_
    rw [ofPMF_μ, product_μ_apply, prod_coe_apply]
    have hsing : @MeasurableSingletonClass ℕ (ofPMF Ξ f D).mspace :=
      ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
    have hsing₂ : @MeasurableSingletonClass (ℕ × ℕ)
        ((ofPMF Ξ f D).mspace.prod (ofPMF P s E).mspace) := by
      refine ⟨fun ⟨a, b⟩ ↦ ?_⟩
      rw [← Set.singleton_prod_singleton]
      exact @MeasurableSet.prod ℕ ℕ (ofPMF Ξ f D).mspace (ofPMF P s E).mspace _ _
        MeasurableSpace.measurableSet_top MeasurableSpace.measurableSet_top
    have hS : @MeasurableSet (ℕ × ℕ) ((ofPMF Ξ f D).mspace.prod (ofPMF P s E).mspace)
        (Nat.pairEquiv ⁻¹' E') :=
      @Set.Countable.measurableSet (ℕ × ℕ) _ hsing₂ _ (Set.to_countable _)
    rw [@Measure.prod_apply ℕ ℕ (ofPMF Ξ f D).mspace (ofPMF P s E).mspace _ _ _ _ hS,
      @lintegral_countable' ℕ (ofPMF Ξ f D).mspace _ _ hsing, PMF.toOuterMeasure_bind_apply]
    refine tsum_congr fun k ↦ ?_
    rw [mul_comm, PMF.toOuterMeasure_map_apply]
    congr 1
    · exact @PMF.toMeasure_apply_singleton ℕ ⊤ Ξ k MeasurableSpace.measurableSet_top
    · exact @PMF.toMeasure_apply_eq_toOuterMeasure_apply ℕ ⊤ P _ MeasurableSpace.measurableSet_top
  · rw [support_ofPMF] at hn
    obtain ⟨k, hk, j, hj, rfl⟩ := hsupp n hn
    obtain ⟨hdom, hle⟩ := hF k hk j hj
    rw [ofPMF_state hdom, product_state, Equiv.symm_apply_apply]
    refine Mem.le_restrict hle ?_
    rw [Mem.dom_union, (ofPMF Ξ f D).dom_valid, (ofPMF P s E).dom_valid]
    rfl

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

lemma bind_congr_support' {α β : Type*} (p : PMF α) {f g : α → PMF β}
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a ↦ ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [h a ((PMF.mem_support_iff _ _).mpr ha)]

/-- **Padding.**  If `ν` refines `𝓡` and allocates the variables `U`, then `ν` also refines
`𝓡` together with a space over `U` that carries no probabilistic information (the memories
of `ν`, restricted to `U`). -/
lemma Refines.pad (h : 𝓡 ≼ ν) {U : Set Var} (hU : Distr.Owns ν U) :
    ∃ T : ProbSpace, T.dom = U ∧ ((𝓡 ⊗ T) ≼ ν) ∧
      ∀ k, ∃ m : Mem, ν (m : WithBot Mem) ≠ 0 ∧ T.state k = m.restrict U := by
  obtain ⟨ξ, f, g, hμ, hst, rfl⟩ := h
  have hsupp : ∀ k ∈ ξ.support, (ξ.map (some ∘ f)) (f k : WithBot Mem) ≠ 0 := by
    intro k hk
    rw [← PMF.mem_support_iff, PMF.support_map]; exact ⟨k, hk, rfl⟩
  have hf : ∀ k ∈ ξ.support, 𝓡.dom ∪ U ⊆ (f k).dom := by
    intro k hk
    refine Set.union_subset ?_ (hU _ (hsupp k hk))
    rw [← 𝓡.dom_valid (g k)]
    exact Mem.dom_mono (hst k hk)
  have hle := Refines.le_ofPMF hμ hst Set.subset_union_left hf
  have hUZ : U ⊆ (ProbSpace.ofPMF ξ f (𝓡.dom ∪ U)).dom := Set.subset_union_right
  refine ⟨ProbSpace.forget _ U hUZ, rfl,
    refines_of_le_ofPMF (ProbSpace.product_forget_le hle hUZ) hf, fun k ↦ ?_⟩
  obtain ⟨k', hk', heq⟩ := ProbSpace.forget_state_restrict _ hUZ k
  rw [ProbSpace.support_ofPMF] at hk'
  refine ⟨f k', hsupp k' hk', ?_⟩
  rw [heq, ProbSpace.ofPMF_state (hf k' hk'), Mem.restrict_restrict,
    Set.inter_eq_right.mpr Set.subset_union_right]

/-- Every memory of a distribution that refines `𝓡` extends a memory of `𝓑`. -/
lemma Refines.exists_le (h : 𝓡 ≼ ν) {m : Mem} (hm : ν (m : WithBot Mem) ≠ 0) :
    ∃ j ∈ 𝓡.support, 𝓡.state j ≤ m := by
  obtain ⟨ξ, f, g, hμ, hst, rfl⟩ := h
  have : (m : WithBot Mem) ∈ (ξ.map (some ∘ f)).support := (PMF.mem_support_iff _ _).mpr hm
  rw [PMF.support_map] at this
  obtain ⟨k, hk, hkm⟩ := this
  cases hkm
  exact ⟨g k, Refines.mem_support hμ hk, hst k hk⟩

/-- An almost sure assertion about a refined space holds of all the memories of the
distribution. -/
lemma Refines.sure {P : MProp} (h : 𝓡 ≼ ν) (hP : OProp.sure P 𝓡) {m : Mem}
    (hm : ν (m : WithBot Mem) ≠ 0) : P m := by
  obtain ⟨j, hj, hle⟩ := Refines.exists_le h hm
  exact P.upcl hle (hP hj)

lemma map_eq_self_of_support {α : Type*} (p : PMF α) {φ : α → α}
    (h : ∀ a ∈ p.support, φ a = a) : p.map φ = p := by
  rw [← PMF.bind_pure_comp]
  conv_rhs => rw [← PMF.bind_pure p]
  refine bind_congr_support' p fun a ha ↦ ?_
  simp only [Function.comp_apply, h a ha]

/-- **Running a kernel.**  Let `𝓐` be refined by `μ`, and let `𝓐'` carry the same
probabilistic information as `𝓐`, but other memories.  If, whenever an outcome `i` of `𝓐`
is compatible with a memory `m` of `μ`, the kernel `K` only produces memories extending the
memory of `𝓐'` at `i`, then `μ.bind K` refines `𝓐'`. -/
theorem Refines.bind {𝓐 𝓐' : ProbSpace} {μ : Distr Mem} (h : 𝓐 ≼ μ)
    (hm : ∀ E, E ∈ 𝓐' → E ∈ 𝓐) (hμ' : ∀ E, E ∈ 𝓐' → 𝓐'.μ E = 𝓐.μ E)
    {K : WithBot Mem → Distr Mem}
    (hK : ∀ i ∈ 𝓐.support, ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → 𝓐.state i ≤ m →
      ∀ y ∈ (K m).support, ∃ m' : Mem, y = (m' : WithBot Mem) ∧ 𝓐'.state i ≤ m') :
    𝓐' ≼ μ.bind K := by
  classical
  obtain ⟨Ξ, f, g, hΞ, hst, rfl⟩ := h
  set ν : Distr Mem := (Ξ.map (some ∘ f)).bind K with hν
  have hsupp : ∀ k ∈ Ξ.support, (Ξ.map (some ∘ f)) (f k : WithBot Mem) ≠ 0 := by
    intro k hk
    rw [← PMF.mem_support_iff, PMF.support_map]; exact ⟨k, hk, rfl⟩
  have hνsupp : ∀ k ∈ Ξ.support, ∀ y ∈ (K (f k)).support, y ∈ ν.support := by
    intro k hk y hy
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨_, (PMF.mem_support_iff _ _).mpr (hsupp k hk), hy⟩
  -- Code the (countably many) outcomes of `ν` by natural numbers
  haveI : Countable ↑(PMF.support ν) := (PMF.support_countable ν).to_subtype
  obtain ⟨c, hc⟩ := Countable.exists_injective_nat ↑(PMF.support ν)
  let code : WithBot Mem → ℕ := fun y ↦ if hy : y ∈ ν.support then c ⟨y, hy⟩ else 0
  let dec : ℕ → WithBot Mem := fun n ↦
    if h : ∃ y ∈ ν.support, code y = n then h.choose else ⊥
  have hcode : ∀ y ∈ ν.support, ∀ y' ∈ ν.support, code y = code y' → y = y' := by
    intro y hy y' hy' h
    have e1 : code y = c ⟨y, hy⟩ := dif_pos hy
    have e2 : code y' = c ⟨y', hy'⟩ := dif_pos hy'
    rw [e1, e2] at h
    exact congrArg Subtype.val (hc h)
  have hdec : ∀ y ∈ ν.support, dec (code y) = y := by
    intro y hy
    have h : ∃ y' ∈ ν.support, code y' = code y := ⟨y, hy, rfl⟩
    simp only [dec, dif_pos h]
    exact hcode _ h.choose_spec.1 y hy h.choose_spec.2
  let f' : ℕ → Mem := fun n ↦ match dec (Nat.unpair n).2 with
    | some m => m
    | none => Mem.emp
  let g' : ℕ → ℕ := fun n ↦ g (Nat.unpair n).1
  let φ : ℕ → WithBot Mem → ℕ := fun k y ↦ Nat.pair k (code y)
  have hf' : ∀ k ∈ Ξ.support, ∀ y ∈ (K (f k)).support, ∃ m' : Mem, y = (m' : WithBot Mem) ∧
      f' (φ k y) = m' ∧ 𝓐'.state (g' (φ k y)) ≤ m' := by
    intro k hk y hy
    obtain ⟨m', rfl, hle⟩ := hK (g k) (Refines.mem_support hΞ hk) (f k) (hsupp k hk) (hst k hk)
      y hy
    refine ⟨m', rfl, ?_, ?_⟩
    · simp only [f', φ, Nat.unpair_pair, hdec _ (hνsupp k hk _ hy)]
    · simp only [g', φ, Nat.unpair_pair]; exact hle
  let Ξ' : PMF ℕ := Ξ.bind fun k ↦ (K (f k)).map (φ k)
  refine ⟨Ξ', f', g', fun {E} hE ↦ ?_, fun n hn ↦ ?_, ?_⟩
  · rw [hμ' E hE, hΞ (hm E hE), tsum_subtype, tsum_subtype, ← PMF.toOuterMeasure_apply,
      ← PMF.toOuterMeasure_apply, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun k ↦ ?_
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hk : g k ∈ E
    · have : φ k ⁻¹' (g' ⁻¹' E) = Set.univ := by
        ext y; simp only [Set.mem_preimage, g', φ, Nat.unpair_pair, hk, Set.mem_univ]
      rw [this, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _), mul_one,
        Set.indicator_of_mem (show k ∈ g ⁻¹' E from hk)]
    · have : φ k ⁻¹' (g' ⁻¹' E) = ∅ := by
        ext y; simp only [Set.mem_preimage, g', φ, Nat.unpair_pair, hk, Set.mem_empty_iff_false]
      rw [this, (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr (Set.disjoint_empty _), mul_zero,
        Set.indicator_of_notMem (show k ∉ g ⁻¹' E from hk)]
  · obtain ⟨k, hk, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
    rw [PMF.mem_support_map_iff] at hn
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨m', -, hfm, hle⟩ := hf' k hk y hy
    rw [hfm]; exact hle
  · change (Ξ.map (some ∘ f)).bind K = (Ξ.bind fun k ↦ (K (f k)).map (φ k)).map (some ∘ f')
    rw [PMF.bind_map, PMF.map_bind]
    refine bind_congr_support' Ξ fun k hk ↦ ?_
    rw [PMF.map_comp]
    refine (map_eq_self_of_support (K (f k)) fun y hy ↦ ?_).symm
    obtain ⟨m', rfl, hfm, -⟩ := hf' k hk y hy
    simp only [Function.comp_apply, hfm]
    rfl

/-- Combining the outcomes of two distributions. -/
def liftMem (c : Mem → Mem → Mem) : WithBot Mem → WithBot Mem → WithBot Mem
  | some a, some b => some (c a b)
  | _, _ => none

/-- **Independence.**  Drawing independently from two distributions that refine `𝓐` and `B`
refines their product, provided the combined memories extend the memories of both. -/
theorem Refines.prod {𝓐 B : ProbSpace} {ρ β : Distr Mem} (hA : 𝓐 ≼ ρ) (hB : B ≼ β)
    (hd : Disjoint 𝓐.dom B.dom) {c : Mem → Mem → Mem}
    (hc : ∀ a b : Mem, 𝓐.dom ⊆ a.dom → B.dom ⊆ b.dom →
      𝓐.dom ∪ B.dom ⊆ (c a b).dom ∧ (a.restrict 𝓐.dom ⊎ b.restrict B.dom) ≤ c a b) :
    (𝓐 ⊗ B) ≼ ρ.bind fun y ↦ β.map (liftMem c y) := by
  obtain ⟨Ξ, f, g, hμ, hst, rfl⟩ := hA
  obtain ⟨P, s, h, hμ', hst', rfl⟩ := hB
  have hf : ∀ k ∈ Ξ.support, 𝓐.dom ⊆ (f k).dom := fun k hk ↦
    (𝓐.dom_valid (g k)).symm.subset.trans (Mem.dom_mono (hst k hk))
  have hs : ∀ j ∈ P.support, B.dom ⊆ (s j).dom := fun j hj ↦
    (B.dom_valid (h j)).symm.subset.trans (Mem.dom_mono (hst' j hj))
  let F : ℕ → Mem := fun n ↦ c (f (Nat.pairEquiv.symm n).1) (s (Nat.pairEquiv.symm n).2)
  have hF : ∀ k j, F (Nat.pairEquiv (k, j)) = c (f k) (s j) := fun k j ↦ by
    simp only [F, Equiv.symm_apply_apply]
  have hle := (ProbSpace.product_mono (Refines.le_ofPMF hμ hst subset_rfl hf)
    (Refines.le_ofPMF hμ' hst' subset_rfl hs) hd).trans
    (ProbSpace.ofPMF_product_le Ξ P f s F 𝓐.dom B.dom fun k hk j hj ↦ by
      rw [hF, ProbSpace.ofPMF_state (hf k hk), ProbSpace.ofPMF_state (hs j hj)]
      exact hc _ _ (hf k hk) (hs j hj))
  have href := refines_of_le_ofPMF hle fun n hn ↦ by
    obtain ⟨k, hk, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
    obtain ⟨j, hj, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    rw [hF]; exact (hc _ _ (hf k hk) (hs j hj)).1
  convert href using 1
  change (Ξ.map (some ∘ f)).bind (fun y ↦ (P.map (some ∘ s)).map (liftMem c y)) =
    (Ξ.bind fun k ↦ P.map fun j ↦ Nat.pairEquiv (k, j)).map (some ∘ F)
  rw [PMF.bind_map, PMF.map_bind]
  congr 1
  funext k
  change PMF.map (liftMem c ((f k : Mem) : WithBot Mem))
      (PMF.map (fun j ↦ ((s j : Mem) : WithBot Mem)) P) =
    PMF.map (fun n ↦ ((F n : Mem) : WithBot Mem)) (PMF.map (fun j ↦ Nat.pairEquiv (k, j)) P)
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext j
  simp only [Function.comp_apply, hF]
  rfl

/-! ### Refinement of sums -/

section Sums

variable {ι : Type} [Countable ι] {ξ : PMF ι} {𝓡 : ι → ProbSpace} {V : Set Var}
  {hd : ∀ {i j : ι}, i ≠ j → Disjoint (𝓡 i).support (𝓡 j).support}
  {hdom : ∀ i, (𝓡 i).dom = V}

omit [Countable ι] in
/-- The measure of a sum, on a set that is measurable there. -/
lemma sum_μ_apply {E : Set ℕ} (hE : E ∈ ProbSpace.sum ξ 𝓡 V hd hdom) :
    ((ProbSpace.sum ξ 𝓡 V hd hdom).μ E : ENNReal) =
      ∑' i, ξ i * (𝓡 i).meas (E ∩ (𝓡 i).support) := by
  rw [ProbSpace.prob_coe]
  exact ProbSpace.sumMeasure_apply ξ 𝓡 hE

/-- **Gluing refinements.**  If each summand of positive weight is refined by a distribution,
then the sum is refined by the `ξ`-average of these distributions. -/
theorem Refines.sum {ν : ι → Distr Mem} (hν : ∀ i, ξ i ≠ 0 → 𝓡 i ≼ ν i) :
    ProbSpace.sum ξ 𝓡 V hd hdom ≼ ξ.bind ν := by
  classical
  have hw : ∀ i, ∃ (Ξ : PMF ℕ) (F : ℕ → Mem) (G : ℕ → ℕ), ξ i ≠ 0 →
      (∀ {E}, E ∈ 𝓡 i → (𝓡 i).μ E = ∑' k : ↑(G ⁻¹' E), Ξ k) ∧
      (∀ k ∈ Ξ.support, (𝓡 i).state (G k) ≤ F k) ∧ ν i = Ξ.map (some ∘ F) := by
    intro i
    by_cases hi : ξ i = 0
    · exact ⟨PMF.pure 0, fun _ ↦ Mem.emp, id, fun h ↦ absurd hi h⟩
    · obtain ⟨Ξ, F, G, h₁, h₂, h₃⟩ := hν i hi
      exact ⟨Ξ, F, G, fun _ ↦ ⟨h₁, h₂, h₃⟩⟩
  choose Ξ F G hw using hw
  haveI : Encodable ι := Encodable.ofCountable ι
  -- The outcome `k` of the summand `i` becomes the outcome `⟨i, k⟩`
  let e : ι → ℕ → ℕ := fun i k ↦ Nat.pair (Encodable.encode i) k
  let dec : ℕ → Option ι := fun n ↦ Encodable.decode (Nat.unpair n).1
  let F' : ℕ → Mem := fun n ↦ match dec n with
    | some i => F i (Nat.unpair n).2
    | none => Mem.emp
  let G' : ℕ → ℕ := fun n ↦ match dec n with
    | some i => G i (Nat.unpair n).2
    | none => 0
  have hdec : ∀ i k, dec (e i k) = some i := fun i k ↦ by
    simp only [dec, e, Nat.unpair_pair, Encodable.encodek]
  have hF' : ∀ i k, F' (e i k) = F i k := fun i k ↦ by
    simp only [F', hdec, e, Nat.unpair_pair]
  have hG' : ∀ i k, G' (e i k) = G i k := fun i k ↦ by
    simp only [G', hdec, e, Nat.unpair_pair]
  let Ξ' : PMF ℕ := ξ.bind fun i ↦ (Ξ i).map (e i)
  refine ⟨Ξ', F', G', fun {E} hE ↦ ?_, fun n hn ↦ ?_, ?_⟩
  · rw [sum_μ_apply hE, tsum_subtype, ← PMF.toOuterMeasure_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_congr fun i ↦ ?_
    by_cases hi : ξ i = 0
    · rw [hi, zero_mul, zero_mul]
    congr 1
    obtain ⟨hμ, hst, -⟩ := hw i hi
    have hEi : E ∩ (𝓡 i).support ∈ 𝓡 i := hE i hi
    rw [PMF.toOuterMeasure_map_apply, ← ProbSpace.prob_coe, hμ hEi, tsum_subtype,
      ← PMF.toOuterMeasure_apply]
    refine PMF.toOuterMeasure_apply_eq_of_inter_support_eq _ ?_
    ext k
    simp only [Set.mem_inter_iff, Set.mem_preimage, hG']
    exact ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨h₁, h₃⟩,
      fun ⟨h₁, h₃⟩ ↦ ⟨⟨h₁, Distr.Refines.mem_support hμ h₃⟩, h₃⟩⟩
  · rw [PMF.mem_support_bind_iff] at hn
    obtain ⟨i, hi, hn⟩ := hn
    rw [PMF.mem_support_map_iff] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    have hi' : ξ i ≠ 0 := (PMF.mem_support_iff _ _).mp hi
    obtain ⟨hμ, hst, -⟩ := hw i hi'
    rw [hF', hG']
    change ProbSpace.sumState 𝓡 V (G i k) ≤ F i k
    rw [ProbSpace.sumState_of_mem hd (Distr.Refines.mem_support hμ hk)]
    exact hst k hk
  · change ξ.bind ν = (ξ.bind fun i ↦ (Ξ i).map (e i)).map (some ∘ F')
    rw [PMF.map_bind]
    refine bind_congr_support' ξ fun i hi ↦ ?_
    rw [PMF.map_comp, (hw i ((PMF.mem_support_iff _ _).mp hi)).2.2]
    congr 1
    funext k
    simp only [Function.comp_apply, hF']

lemma filter_toOuterMeasure {α : Type*} (p : PMF α) (s t : Set α)
    (h : ∃ a ∈ s, a ∈ p.support) :
    (p.filter s h).toOuterMeasure t = p.toOuterMeasure (t ∩ s) * (p.toOuterMeasure s)⁻¹ := by
  simp only [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun a ↦ ?_
  by_cases ht : a ∈ t <;> by_cases hs : a ∈ s <;> simp [Set.indicator, ht, hs]

omit [Countable ι] in
/-- **Splitting a refinement.**  A distribution that refines a sum is the `ξ`-average of
distributions that refine the summands (the distribution conditioned on each summand). -/
theorem Refines.split {μ : Distr Mem} (h : ProbSpace.sum ξ 𝓡 V hd hdom ≼ μ) :
    ∃ μ' : ι → Distr Mem, (∀ i, ξ i ≠ 0 → 𝓡 i ≼ μ' i) ∧ μ = ξ.bind μ' := by
  classical
  obtain ⟨Ξ, f, g, hμ, hst, rfl⟩ := h
  set S := ProbSpace.sum ξ 𝓡 V hd hdom with hS
  -- The part of an event of a summand that lies in its support is an event of the sum
  have hmeas : ∀ i, ξ i ≠ 0 → ∀ E, E ∈ 𝓡 i → E ∩ (𝓡 i).support ∈ S := by
    intro i hi E hE j hj
    by_cases hij : j = i
    · subst hij
      rw [Set.inter_assoc, Set.inter_self]
      exact @MeasurableSet.inter ℕ (𝓡 j).mspace _ _ hE (ProbSpace.support_measurableSet _)
    · rw [Set.inter_assoc, (hd (Ne.symm hij)).inter_eq, Set.inter_empty]
      exact (𝓡 j).mspace.measurableSet_empty
  have hsumμ : ∀ i, ξ i ≠ 0 → ∀ E, E ∈ 𝓡 i →
      (S.μ (E ∩ (𝓡 i).support) : ENNReal) = ξ i * (𝓡 i).meas E := by
    intro i hi E hE
    rw [sum_μ_apply (hmeas i hi E hE), tsum_eq_single i]
    · rw [Set.inter_assoc, Set.inter_self, ProbSpace.meas_inter_support]
    · intro j hij
      rw [Set.inter_assoc, (hd (Ne.symm hij)).inter_eq, Set.inter_empty, measure_empty,
        mul_zero]
  -- The outcomes that are sent to the summand `i` have probability `ξ i`
  have hA : ∀ i, ξ i ≠ 0 → Ξ.toOuterMeasure (g ⁻¹' (𝓡 i).support) = ξ i := by
    intro i hi
    have h1 := hμ (hmeas i hi _ (ProbSpace.support_measurableSet (𝓡 i)))
    have h2 := hsumμ i hi _ (ProbSpace.support_measurableSet (𝓡 i))
    rw [Set.inter_self] at h1 h2
    rw [PMF.toOuterMeasure_apply, ← tsum_subtype, ← h1, h2, ProbSpace.measure_support, mul_one]
  have hne : ∀ i, ξ i ≠ 0 → ∃ a ∈ g ⁻¹' (𝓡 i).support, a ∈ Ξ.support := by
    intro i hi
    have h0 : Ξ.toOuterMeasure (g ⁻¹' (𝓡 i).support) ≠ 0 := by rw [hA i hi]; exact hi
    rw [Ne, PMF.toOuterMeasure_apply_eq_zero_iff, Set.not_disjoint_iff] at h0
    obtain ⟨a, ha, ha'⟩ := h0
    exact ⟨a, ha', ha⟩
  let Ξi : ι → PMF ℕ := fun i ↦
    if hi : ξ i = 0 then Ξ else Ξ.filter (g ⁻¹' (𝓡 i).support) (hne i hi)
  have hΞi : ∀ i (hi : ξ i ≠ 0), Ξi i = Ξ.filter (g ⁻¹' (𝓡 i).support) (hne i hi) :=
    fun i hi ↦ dif_neg hi
  refine ⟨fun i ↦ (Ξi i).map (some ∘ f), fun i hi ↦ ?_, ?_⟩
  · refine ⟨Ξi i, f, g, fun {E} hE ↦ ?_, fun k hk ↦ ?_, rfl⟩
    · rw [tsum_subtype, ← PMF.toOuterMeasure_apply, hΞi i hi, filter_toOuterMeasure, hA i hi,
        ← Set.preimage_inter, PMF.toOuterMeasure_apply, ← tsum_subtype, ← hμ (hmeas i hi E hE),
        hsumμ i hi E hE, ProbSpace.prob_coe, mul_comm, ← mul_assoc,
        ENNReal.inv_mul_cancel hi (PMF.apply_ne_top _ _), one_mul]
    · rw [hΞi i hi, PMF.support_filter] at hk
      have := hst k hk.2
      change ProbSpace.sumState 𝓡 V (g k) ≤ f k at this
      rwa [ProbSpace.sumState_of_mem hd hk.1] at this
  · have hbind : ξ.bind Ξi = Ξ := by
      ext k
      rw [PMF.bind_apply]
      by_cases hk : k ∈ Ξ.support
      · have hgk := Distr.Refines.mem_support hμ hk
        rw [ProbSpace.support_sum] at hgk
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hgk
        obtain ⟨i₀, hi₀, hgi₀⟩ := hgk
        rw [tsum_eq_single i₀]
        · have hk₀ : k ∈ g ⁻¹' (𝓡 i₀).support := hgi₀
          rw [hΞi i₀ hi₀, PMF.filter_apply, Set.indicator_of_mem hk₀, ← PMF.toOuterMeasure_apply,
            hA i₀ hi₀, mul_comm (Ξ k), ← mul_assoc,
            ENNReal.mul_inv_cancel hi₀ (PMF.apply_ne_top _ _), one_mul]
        · intro j hj
          by_cases hξj : ξ j = 0
          · rw [hξj, zero_mul]
          rw [hΞi j hξj, PMF.filter_apply, Set.indicator_of_notMem, zero_mul, mul_zero]
          exact fun h ↦ Set.disjoint_left.mp (hd (Ne.symm hj)) hgi₀ h
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hk]
        refine ENNReal.tsum_eq_zero.mpr fun i ↦ ?_
        by_cases hξi : ξ i = 0
        · rw [hξi, zero_mul]
        rw [hΞi i hξi, PMF.filter_apply, Set.indicator_apply_eq_zero.mpr
          (fun _ ↦ (PMF.apply_eq_zero_iff _ _).mpr hk), zero_mul, mul_zero]
    change Ξ.map (some ∘ f) = ξ.bind fun i ↦ (Ξi i).map (some ∘ f)
    rw [← PMF.map_bind, hbind]

end Sums

/-! ### Refinement through a given representation -/

/-- `𝓡` is refined by the distribution represented by `(Ξ, f)`, through the relabeling `g`. -/
def RefinesVia (𝓡 : ProbSpace) (Ξ : PMF ℕ) (f : ℕ → Mem) (g : ℕ → ℕ) : Prop :=
  (∀ {E}, E ∈ 𝓡 → 𝓡.μ E = ∑' k : ↑(g ⁻¹' E), Ξ k) ∧ ∀ k ∈ Ξ.support, 𝓡.state (g k) ≤ f k

namespace RefinesVia

variable {Ξ : PMF ℕ} {f : ℕ → Mem} {g : ℕ → ℕ}

lemma refines (h : RefinesVia 𝓡 Ξ f g) : 𝓡 ≼ Ξ.map (some ∘ f) := ⟨Ξ, f, g, h.1, h.2, rfl⟩

lemma of_refines (h : 𝓡 ≼ ν) : ∃ Ξ f g, RefinesVia 𝓡 Ξ f g ∧ ν = Ξ.map (some ∘ f) :=
  let ⟨Ξ, f, g, h₁, h₂, h₃⟩ := h; ⟨Ξ, f, g, ⟨h₁, h₂⟩, h₃⟩

/-- A space below a refined space is refined through the composed relabeling. -/
lemma mono {𝓟 : ProbSpace} {h : ℕ → ℕ} (hr : ProbSpace.Relabels 𝓟 𝓡 h)
    (hv : RefinesVia 𝓡 Ξ f g) : RefinesVia 𝓟 Ξ f (h ∘ g) := by
  refine ⟨fun {E} hE ↦ ?_, fun k hk ↦ ?_⟩
  · rw [← hr.μ E hE]; exact hv.1 (hr.mspace E hE)
  · exact (hr.state _ (Refines.mem_support hv.1 hk)).trans (hv.2 k hk)

lemma support (hv : RefinesVia 𝓡 Ξ f g) {k : ℕ} (hk : k ∈ Ξ.support) : g k ∈ 𝓡.support :=
  Refines.mem_support hv.1 hk

/-- **Conditioning.**  A space whose events all have probability `0` or `1` is refined by
every conditioning of a distribution that refines it. -/
lemma filter (hv : RefinesVia 𝓡 Ξ f g) (h01 : ∀ E, E ∈ 𝓡 → 𝓡.μ E = 0 ∨ 𝓡.μ E = 1)
    {S : Set ℕ} (hS : ∃ a ∈ S, a ∈ Ξ.support) : RefinesVia 𝓡 (Ξ.filter S hS) f g := by
  refine ⟨fun {E} hE ↦ ?_, fun k hk ↦ hv.2 k ((PMF.support_filter hS ▸ hk).2)⟩
  have hΞ := hv.1 hE
  rw [tsum_subtype, ← PMF.toOuterMeasure_apply] at hΞ ⊢
  rw [filter_toOuterMeasure]
  have hS0 : Ξ.toOuterMeasure S ≠ 0 := by
    rw [Ne, PMF.toOuterMeasure_apply_eq_zero_iff, Set.not_disjoint_iff]
    obtain ⟨a, ha, ha'⟩ := hS; exact ⟨a, ha', ha⟩
  have hStop : Ξ.toOuterMeasure S ≠ (⊤ : ENNReal) := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← (PMF.toOuterMeasure_apply_eq_one_iff Ξ Set.univ).mpr (Set.subset_univ _)]
    exact measure_mono (Set.subset_univ _)
  rcases h01 E hE with h0 | h1
  · rw [h0] at hΞ ⊢
    have : Ξ.toOuterMeasure (g ⁻¹' E ∩ S) = 0 :=
      measure_mono_null Set.inter_subset_left hΞ.symm
    rw [this, zero_mul]; rfl
  · rw [h1] at hΞ ⊢
    have hfull : Ξ.toOuterMeasure (g ⁻¹' E ∩ S) = Ξ.toOuterMeasure S := by
      refine PMF.toOuterMeasure_apply_eq_of_inter_support_eq _ ?_
      ext k
      simp only [Set.mem_inter_iff]
      refine ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨?_, h.1⟩, h.2⟩⟩
      exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mp hΞ.symm h.2
    rw [hfull, ENNReal.mul_inv_cancel hS0 hStop]; rfl

/-- **Adding information-free variables.**  If the memories of the distribution extend the
memories `s` (read through `t`), then the space without probabilistic information over those
memories can be added to a refined space. -/
lemma product_trivialOn {X : ProbSpace} (hv : RefinesVia X Ξ f g) {V : Set Var}
    {s : ℕ → Mem} {hs : ∀ n, (s n).dom = V} (t : ℕ → ℕ) (ht : ∀ k ∈ Ξ.support, s (t k) ≤ f k) :
    ∃ g', RefinesVia (X ⊗ ProbSpace.trivialOn V s hs) Ξ f g' := by
  have hf : ∀ k ∈ Ξ.support, X.dom ∪ V ⊆ (f k).dom := fun k hk ↦
    Set.union_subset ((X.dom_valid (g k)).symm.subset.trans (Mem.dom_mono (hv.2 k hk)))
      ((hs (t k)).symm.subset.trans (Mem.dom_mono (ht k hk)))
  have hle := Refines.le_ofPMF hv.1 hv.2 Set.subset_union_left hf
  have hle' := ProbSpace.product_trivialOn_le (hf := hs) hle Set.subset_union_right t
    fun k hk ↦ by
      rw [ProbSpace.support_ofPMF] at hk
      rw [ProbSpace.ofPMF_state (hf k hk)]
      exact Mem.le_restrict (ht k hk) ((hs (t k)).subset.trans Set.subset_union_right)
  obtain ⟨g', hg'⟩ := hle'
  refine ⟨g', fun {E} hE ↦ ?_, fun k hk ↦ ?_⟩
  · rw [← hg'.μ E hE, ProbSpace.ofPMF_μ, PMF.toOuterMeasure_apply, tsum_subtype]
  · have hk' : k ∈ (ProbSpace.ofPMF Ξ f (X.dom ∪ V)).support := by
      rwa [ProbSpace.support_ofPMF]
    refine (hg'.state k hk').trans ?_
    rw [ProbSpace.ofPMF_state (hf k hk)]
    exact Mem.restrict_le _ _

end RefinesVia

open Classical in
/-- A distribution is the average of its conditionings on the fibers of a map. -/
lemma bind_filter_fiber {ι : Type} (Ξ : PMF ℕ) (I : ℕ → ι) :
    (Ξ.map I).bind (fun i ↦ if h : ∃ a ∈ I ⁻¹' {i}, a ∈ Ξ.support
      then Ξ.filter (I ⁻¹' {i}) h else Ξ) = Ξ := by
  ext k
  rw [PMF.bind_apply, tsum_eq_single (I k)]
  · by_cases hk : Ξ k = 0
    · split_ifs with hh
      · rw [PMF.filter_apply, Set.indicator_of_mem (show k ∈ I ⁻¹' {I k} from rfl), hk,
          zero_mul, mul_zero]
      · rw [hk, mul_zero]
    · have hh : ∃ a ∈ I ⁻¹' {I k}, a ∈ Ξ.support :=
        ⟨k, rfl, (PMF.mem_support_iff _ _).mpr hk⟩
      rw [dif_pos hh, PMF.filter_apply, Set.indicator_of_mem (show k ∈ I ⁻¹' {I k} from rfl)]
      have hsum : ∑' a, (I ⁻¹' {I k}).indicator Ξ a = Ξ.map I (I k) := by
        rw [PMF.map_apply]
        refine tsum_congr fun a ↦ ?_
        by_cases ha : I k = I a
        · rw [if_pos ha, Set.indicator_of_mem (show a ∈ I ⁻¹' {I k} from ha.symm)]
        · rw [if_neg ha, Set.indicator_of_notMem (show a ∉ I ⁻¹' {I k} from fun h ↦ ha h.symm)]
      have hne : Ξ.map I (I k) ≠ 0 := (PMF.mem_support_iff _ _).mp
        ((PMF.mem_support_map_iff _ _ _).mpr ⟨k, (PMF.mem_support_iff _ _).mpr hk, rfl⟩)
      rw [hsum, mul_comm (Ξ k), ← mul_assoc, ENNReal.mul_inv_cancel hne (PMF.apply_ne_top _ _),
        one_mul]
  · intro i hi
    split_ifs with hh
    · rw [PMF.filter_apply, Set.indicator_of_notMem (show k ∉ I ⁻¹' {i} from fun h ↦ hi h.symm),
        zero_mul, mul_zero]
    · have : Ξ.map I i = 0 := by
        rw [PMF.map_apply]
        refine ENNReal.tsum_eq_zero.mpr fun a ↦ ?_
        split_ifs with hia
        · by_contra ha
          exact hh ⟨a, hia.symm, (PMF.mem_support_iff _ _).mpr ha⟩
        · rfl
      rw [this, zero_mul]


end Distr

end Pcol
