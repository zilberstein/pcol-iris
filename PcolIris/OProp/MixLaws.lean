/-
Regrouping outcome conjunctions.

A mixture of mixtures is a mixture over pairs (`OProp.oplus_flatten`), and the branches of a
mixture that satisfy the same convex assertion can be merged (`OProp.oplus_regroup`).
-/
import PcolIris.OProp.Laws
import PcolIris.OProp.SumBind

namespace Pcol

open MeasureTheory

namespace ProbSpace

/-- The summands of a sum below `P` can be extended to the variables of `P`, without adding
probabilistic information. -/
lemma pad_sum {κ : Type} {ζ : PMF κ} {𝓠 : κ → ProbSpace} {W : Set Var}
    {hd : ∀ {i j : κ}, i ≠ j → Disjoint (𝓠 i).support (𝓠 j).support}
    {hdom : ∀ k, (𝓠 k).dom = W} {P : ProbSpace} (hle : sum ζ 𝓠 W hd hdom ≤ P) :
    ∃ (𝓠' : κ → ProbSpace) (hd' : ∀ {i j : κ}, i ≠ j → Disjoint (𝓠' i).support (𝓠' j).support)
      (hdom' : ∀ k, (𝓠' k).dom = P.dom), (∀ k, 𝓠 k ≤ 𝓠' k) ∧ sum ζ 𝓠' P.dom hd' hdom' ≤ P := by
  have hW : W ⊆ P.dom := dom_mono hle
  have hU : P.dom \ W ⊆ P.dom := Set.sdiff_subset
  set F := forget P (P.dom \ W) hU
  have hdom' : ∀ k, (𝓠 k ⊗ F).dom = P.dom := fun k ↦ by
    change (𝓠 k).dom ∪ (P.dom \ W) = P.dom
    rw [hdom k, Set.union_sdiff_self, Set.union_eq_right.mpr hW]
  refine ⟨fun k ↦ 𝓠 k ⊗ F, sum_prod_disjoint F hd, hdom', fun k ↦ le_product_left _ _, ?_⟩
  have hPW : P.dom = W ∪ F.dom := by
    change P.dom = W ∪ (P.dom \ W)
    rw [Set.union_sdiff_self, Set.union_eq_right.mpr hW]
  exact (sum_dom_congr hPW).trans
    ((sumProd_le_sum_product ζ 𝓠 F W hd hdom).trans (product_forget_le hle hU))

end ProbSpace

namespace OProp

/-- **Flattening.**  A mixture of mixtures is a mixture over pairs. -/
theorem oplus_flatten {ι κ : Type} [Countable ι] [Countable κ] (ξ : PMF ι) (ζ : ι → PMF κ)
    (φ : ι → κ → OProp) :
    (⨁[ξ] fun i ↦ ⨁[ζ i] φ i) ⊢ ⨁[ξ.bind fun i ↦ (ζ i).map (Prod.mk i)] fun p ↦ φ p.1 p.2 := by
  classical
  haveI : Encodable κ := Encodable.ofCountable κ
  haveI : Encodable (ι × κ) := Encodable.ofCountable _
  rintro 𝓟 ⟨𝓟s, V, hd, hdom, hsum, hφ⟩
  -- The inner mixtures, padded to the variables `V`
  have hin : ∀ i, ∃ (𝓠 : κ → ProbSpace)
      (hdQ : ∀ {k k' : κ}, k ≠ k' → Disjoint (𝓠 k).support (𝓠 k').support)
      (hdomQ : ∀ k, (𝓠 k).dom = V), ξ i ≠ 0 →
        ProbSpace.sum (ζ i) 𝓠 V hdQ hdomQ ≤ 𝓟s i ∧ ∀ k ∈ (ζ i).support, φ i k (𝓠 k) := by
    intro i
    by_cases hi : ξ i = 0
    · exact ⟨fun k ↦ (𝓟s i).shift (Encodable.encode k),
        fun h ↦ ProbSpace.disjoint_support_shift _ _ fun h' ↦ h (Encodable.encode_injective h'),
        fun _ ↦ hdom i, fun h ↦ absurd hi h⟩
    · obtain ⟨𝓠, W, hdQ, hdomQ, hsumQ, hφQ⟩ := hφ i ((PMF.mem_support_iff _ _).mpr hi)
      obtain ⟨𝓠', hd', hdom', hle', hsum'⟩ := ProbSpace.pad_sum (hd := hdQ) hsumQ
      refine ⟨𝓠', hd', fun k ↦ (hdom' k).trans (hdom i),
        fun _ ↦ ⟨(ProbSpace.sum_dom_congr (hdom i).symm).trans hsum',
          fun k hk ↦ (φ i k).mono (hle' k) (hφQ k hk)⟩⟩
  choose 𝓠 hdQ hdomQ hin using hin
  -- The flat family over pairs
  let 𝓡 : ι × κ → ProbSpace := fun p ↦ (𝓠 p.1 p.2).shift (Encodable.encode p)
  have hd𝓡 : ∀ {p q : ι × κ}, p ≠ q → Disjoint (𝓡 p).support (𝓡 q).support := fun h ↦
    ProbSpace.disjoint_support_shift _ _ fun h' ↦ h (Encodable.encode_injective h')
  have hdom𝓡 : ∀ p, (𝓡 p).dom = V := fun p ↦ hdomQ p.1 p.2
  have hζ' : ∀ {i i' : ι}, i ≠ i' →
      Disjoint ((ζ i).map (Prod.mk i)).support ((ζ i').map (Prod.mk i')).support := by
    intro i i' hii
    rw [PMF.support_map, PMF.support_map, Set.disjoint_left]
    rintro _ ⟨k, -, rfl⟩ ⟨k', -, h⟩
    exact hii (congrArg Prod.fst h).symm
  have hinj : ∀ i, Function.Injective (Prod.mk i : κ → ι × κ) :=
    fun i k k' h ↦ (Prod.ext_iff.mp h).2
  refine ⟨𝓡, V, hd𝓡, hdom𝓡, ?_, fun p hp ↦ ?_⟩
  · refine (ProbSpace.le_sum_nested (ξ := ξ) (ζ := fun i ↦ (ζ i).map (Prod.mk i)) hd𝓡 hdom𝓡
      hζ').trans ((ProbSpace.sum_mono (ProbSpace.nested_disjoint hd𝓡 hdom𝓡 hζ') hd
        (fun _ ↦ rfl) hdom subset_rfl fun i hi ↦ ?_).trans hsum)
    exact (ProbSpace.sum_map_le (hinj i) hd𝓡 hdom𝓡).trans
      ((ProbSpace.sum_mono _ (hdQ i) _ (hdomQ i) subset_rfl
        fun k _ ↦ ProbSpace.shift_le _ _).trans (hin i hi).1)
  · obtain ⟨i, hi, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    obtain ⟨k, hk, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    exact (φ i k).mono (ProbSpace.le_shift _ _)
      ((hin i ((PMF.mem_support_iff _ _).mp hi)).2 k hk)

/-- An assertion is convex when it is closed under probabilistic mixtures. -/
def Convex (ψ : OProp) : Prop :=
  ∀ {ι : Type} [Countable ι] (ξ : PMF ι), (⨁[ξ] fun (_ : ι) ↦ ψ) ⊢ ψ

/-- Almost sure assertions are convex. -/
theorem Convex.sure (P : MProp) : Convex (sure P) := by
  intro ι _ ξ 𝓟 ⟨𝓠, V, hd, hdom, hsum, hφ⟩
  refine (OProp.sure P).mono hsum fun n hn ↦ ?_
  rw [ProbSpace.support_sum ξ 𝓠 V hd hdom] at hn
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn
  obtain ⟨v, hv, hnv⟩ := hn
  change P (ProbSpace.sumState 𝓠 V n)
  rw [ProbSpace.sumState_of_mem hd hnv]
  exact hφ v ((PMF.mem_support_iff _ _).mpr hv) hnv

/-- **Regrouping.**  The branches of a mixture that satisfy the same convex assertion can be
merged. -/
theorem oplus_regroup {ι κ : Type} [Countable ι] [Countable κ] (ρ : PMF ι) (f : ι → κ)
    (φ : κ → OProp) (hφ : ∀ k, ρ.map f k ≠ 0 → Convex (φ k)) :
    (⨁[ρ] fun i ↦ φ (f i)) ⊢ ⨁[ρ.map f] φ := by
  classical
  haveI : Encodable κ := Encodable.ofCountable κ
  rintro 𝓟 ⟨𝓟s, V, hd, hdom, hsum, hφs⟩
  -- The images of positive weight, and the conditionings of `ρ` on their fibers
  let κ' := {k : κ // ρ.map f k ≠ 0}
  have hne : ∀ k' : κ', ∃ i ∈ f ⁻¹' {k'.1}, i ∈ ρ.support := fun k' ↦ by
    obtain ⟨i, hi, hik⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr k'.2)
    exact ⟨i, hik, hi⟩
  let ζ : κ' → PMF ι := fun k' ↦ ρ.filter (f ⁻¹' {k'.1}) (hne k')
  have hζsupp : ∀ k' i, i ∈ (ζ k').support → f i = k'.1 ∧ i ∈ ρ.support := fun k' i hi ↦ by
    rw [PMF.support_filter] at hi; exact hi
  have hζ : ∀ {k k' : κ'}, k ≠ k' → Disjoint (ζ k).support (ζ k').support := by
    intro k k' hkk'
    refine Set.disjoint_left.mpr fun i hi hi' ↦ hkk' (Subtype.ext ?_)
    rw [← (hζsupp k i hi).1, (hζsupp k' i hi').1]
  let ξ' : PMF κ' := ⟨fun k' ↦ ρ.map f k'.1, by
    rw [ENNReal.summable.hasSum_iff]
    change ∑' (b : ({k | ρ.map f k ≠ 0} : Set κ)), ρ.map f b = 1
    rw [tsum_subtype_eq_of_support_subset (f := fun k ↦ ρ.map f k) (s := {k | ρ.map f k ≠ 0})
      (fun k hk ↦ hk)]
    exact (ρ.map f).tsum_coe⟩
  have hbind : ξ'.bind ζ = ρ := by
    ext i
    rw [PMF.bind_apply]
    by_cases hi : ρ i = 0
    · rw [hi]
      refine ENNReal.tsum_eq_zero.mpr fun k' ↦ ?_
      rw [PMF.filter_apply, Set.indicator_apply_eq_zero.mpr fun _ ↦ hi, zero_mul, mul_zero]
    · have hfi : ρ.map f (f i) ≠ 0 := (PMF.mem_support_iff _ _).mp
        ((PMF.mem_support_map_iff _ _ _).mpr ⟨i, (PMF.mem_support_iff _ _).mpr hi, rfl⟩)
      rw [tsum_eq_single ⟨f i, hfi⟩]
      · change ρ.map f (f i) * (ρ.filter _ _) i = ρ i
        rw [PMF.filter_apply, Set.indicator_of_mem (show i ∈ f ⁻¹' {f i} from rfl)]
        have hsum' : ∑' a, (f ⁻¹' {f i}).indicator ρ a = ρ.map f (f i) := by
          rw [PMF.map_apply]
          refine tsum_congr fun a ↦ ?_
          by_cases ha : f i = f a
          · rw [if_pos ha, Set.indicator_of_mem (show a ∈ f ⁻¹' {f i} from ha.symm)]
          · rw [if_neg ha, Set.indicator_of_notMem (show a ∉ f ⁻¹' {f i} from fun h ↦ ha h.symm)]
        rw [hsum', mul_comm (ρ i), ← mul_assoc, ENNReal.mul_inv_cancel hfi (PMF.apply_ne_top _ _),
          one_mul]
      · intro k' hk'
        rw [PMF.filter_apply, Set.indicator_of_notMem, zero_mul, mul_zero]
        exact fun h ↦ hk' (Subtype.ext h.symm)
  -- The merged branches
  let 𝓡 : κ' → ProbSpace := fun k' ↦ ProbSpace.sum (ζ k') 𝓟s V hd hdom
  have h𝓡 : ∀ k' : κ', φ k'.1 (𝓡 k') := fun k' ↦ hφ k'.1 k'.2 (ζ k') (𝓡 k')
    ⟨𝓟s, V, hd, hdom, le_refl _, fun i hi ↦ by
      obtain ⟨hfi, hi'⟩ := hζsupp k' i hi
      rw [← hfi]; exact hφs i hi'⟩
  have hnest : ProbSpace.sum ξ' 𝓡 V (ProbSpace.nested_disjoint hd hdom hζ) (fun _ ↦ rfl) ≤ 𝓟 := by
    have h := ProbSpace.sum_nested_le (ξ := ξ') hd hdom hζ
    rw [hbind] at h
    exact h.trans hsum
  -- Back to the index type `κ`
  obtain ⟨i₀, -⟩ := ρ.support_nonempty
  let G : κ → ProbSpace := fun k ↦
    (if h : ρ.map f k ≠ 0 then 𝓡 ⟨k, h⟩ else 𝓟s i₀).shift (Encodable.encode k)
  have hdG : ∀ {k k' : κ}, k ≠ k' → Disjoint (G k).support (G k').support := fun h ↦
    ProbSpace.disjoint_support_shift _ _ fun h' ↦ h (Encodable.encode_injective h')
  have hdomG : ∀ k, (G k).dom = V := fun k ↦ by
    change (if h : ρ.map f k ≠ 0 then 𝓡 ⟨k, h⟩ else 𝓟s i₀).dom = V
    split_ifs
    · rfl
    · exact hdom i₀
  have hG : ∀ k' : κ', G k'.1 = (𝓡 k').shift (Encodable.encode k'.1) := fun k' ↦ by
    change (if h : ρ.map f k'.1 ≠ 0 then 𝓡 ⟨k'.1, h⟩ else 𝓟s i₀).shift _ = _
    rw [dif_pos k'.2]
  have hmap : ξ'.map Subtype.val = ρ.map f := by
    ext k
    rw [PMF.map_apply]
    by_cases hk : ρ.map f k = 0
    · rw [hk]
      refine ENNReal.tsum_eq_zero.mpr fun k' ↦ ?_
      split_ifs with h
      · exact absurd (h ▸ hk) k'.2
      · rfl
    · rw [tsum_eq_single ⟨k, hk⟩ fun k' hk' ↦ if_neg fun h ↦ hk' (Subtype.ext h.symm), if_pos rfl]
      rfl
  refine ⟨G, V, hdG, hdomG, ?_, fun k hk ↦ ?_⟩
  · rw [← hmap]
    refine (ProbSpace.sum_map_le Subtype.val_injective hdG hdomG).trans
      ((ProbSpace.sum_mono _ _ _ _ subset_rfl fun k' _ ↦ ?_).trans hnest)
    change G k'.1 ≤ 𝓡 k'
    rw [hG]; exact ProbSpace.shift_le _ _
  · have hk' : ρ.map f k ≠ 0 := (PMF.mem_support_iff _ _).mp hk
    rw [hG ⟨k, hk'⟩]
    exact (φ k).mono (ProbSpace.le_shift _ _) (h𝓡 ⟨k, hk'⟩)

/-- A mixture of convex assertions is convex. -/
theorem Convex.oplus {ι : Type} [Countable ι] {ξ : PMF ι} {φ : ι → OProp}
    (h : ∀ i, Convex (φ i)) : Convex (⨁[ξ] φ) := by
  intro κ _ ζ
  refine Iris.BI.Entails.trans (oplus_flatten ζ (fun _ ↦ ξ) (fun _ ↦ φ)) ?_
  have hmap : (ζ.bind fun k ↦ ξ.map (Prod.mk k)).map Prod.snd = ξ := by
    rw [PMF.map_bind]
    simp_rw [PMF.map_comp]
    have hid : ∀ k : κ, (Prod.snd ∘ Prod.mk k : ι → ι) = id := fun _ ↦ rfl
    simp_rw [hid, PMF.map_id]
    exact PMF.bind_const _ _
  have := oplus_regroup (ζ.bind fun k ↦ ξ.map (Prod.mk k)) Prod.snd φ fun i _ ↦ h i
  rwa [hmap] at this

/-- A nondeterministic choice between convex assertions is convex. -/
theorem Convex.nondet {ι : Type} [Countable ι] {φ : ι → OProp} (h : ∀ i, Convex (φ i)) :
    Convex (& φ) := by
  classical
  intro κ _ ζ 𝓟 ⟨𝓟s, V, hd, hdom, hsum, hφ⟩
  obtain ⟨k₀, hk₀⟩ := ζ.support_nonempty
  obtain ⟨ξ₀, -⟩ := hφ k₀ hk₀
  have hch : ∀ k, ∃ ξ : PMF ι, k ∈ ζ.support → (⨁[ξ] φ) (𝓟s k) := fun k ↦ by
    by_cases hk : k ∈ ζ.support
    · obtain ⟨ξ, hξ⟩ := hφ k hk; exact ⟨ξ, fun _ ↦ hξ⟩
    · exact ⟨ξ₀, fun h ↦ absurd h hk⟩
  choose ξ hξ using hch
  have hmix : (⨁[ζ] fun k ↦ ⨁[ξ k] φ) 𝓟 := ⟨𝓟s, V, hd, hdom, hsum, fun k hk ↦ hξ k hk⟩
  have := oplus_regroup _ Prod.snd φ (fun i _ ↦ h i) _ (oplus_flatten ζ ξ (fun _ ↦ φ) _ hmix)
  exact ⟨_, this⟩

end OProp

end Pcol
