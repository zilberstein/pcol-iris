/-
Distributions that refine a precondition together with a frame and the invariant.

This is the shape of the assumption on the initial distribution, and of the guarantee on the
final distribution, in the definition of the weakest precondition (Definition 5.1 of the
paper).
-/
import PcolIris.OProp.OProp
import PcolIris.OProp.ProductLaws
import PcolIris.Semantics.Invariant
import PcolIris.OProp.Laws
import PcolIris.OProp.Refines

namespace Pcol

/-- An invariant only talks about its own variables. -/
lemma Inv.footprint (𝓘 : Inv) : 𝓘.to_MProp.Footprint 𝓘.dom := by
  intro σ
  change 𝓘.prop (σ.restrict 𝓘.dom) ↔ 𝓘.dom ⊆ σ.dom ∧ 𝓘.prop ((σ.restrict 𝓘.dom).restrict 𝓘.dom)
  rw [Mem.restrict_restrict, Set.inter_self]
  refine ⟨fun h ↦ ⟨?_, h⟩, fun h ↦ h.2⟩
  have := 𝓘.dom_valid h
  rw [Mem.restrict_dom] at this
  exact Set.inter_eq_right.mp this

/-- A run from `μ` to `ν` does not deallocate variables. -/
def Distr.Keeps (μ ν : Distr Mem) : Prop :=
  ∀ D, Distr.Owns μ D → Distr.Owns ν D

lemma Distr.Keeps.refl (μ : Distr Mem) : Distr.Keeps μ μ := fun _ h ↦ h

lemma Distr.Keeps.trans {μ ν ρ : Distr Mem} (h₁ : Distr.Keeps μ ν) (h₂ : Distr.Keeps ν ρ) : Distr.Keeps μ ρ :=
  fun D h ↦ h₂ D (h₁ D h)

/--
`Framed 𝓘 𝓟 𝓟fr 𝓙 μ` states that the distribution `μ` refines the product of a space `𝓟`
(owned by the program), a frame `𝓟fr`, and a space `𝓙` in which the invariant `𝓘` holds
almost surely, where the three spaces own disjoint sets of variables.

This is the relation `P' ⪯ μ` with `P' ∈ P ⋄ P_F` and `Γ, P ⊨ φ ∗ ⌈I⌉` of Definition 5.1,
where the part of the precondition that satisfies the invariant is kept as a separate factor.
-/
structure Framed (𝓘 : Inv) (𝓟 𝓟fr 𝓙 : ProbSpace) (μ : Distr Mem) : Prop where
  inv : OProp.sure 𝓘.to_MProp 𝓙
  disj_frame : Disjoint 𝓟.dom 𝓟fr.dom
  disj_inv : Disjoint (𝓟.dom ∪ 𝓟fr.dom) 𝓙.dom
  refines : (𝓟 ⊗ 𝓟fr ⊗ 𝓙) ≼ μ

namespace Framed

variable {𝓘 : Inv} {𝓟 𝓟' 𝓟fr 𝓙 : ProbSpace} {μ : Distr Mem}

/-- A distribution that is framed with a space is also framed with any space that carries
less information. -/
lemma mono (h : 𝓟 ≤ 𝓟') (hf : Framed 𝓘 𝓟' 𝓟fr 𝓙 μ) : Framed 𝓘 𝓟 𝓟fr 𝓙 μ where
  inv := hf.inv
  disj_frame := hf.disj_frame.mono_left (ProbSpace.dom_mono h)
  disj_inv := hf.disj_inv.mono_left (Set.union_subset_union_left _ (ProbSpace.dom_mono h))
  refines := Distr.Refines.mono
    (ProbSpace.product_mono_left (ProbSpace.product_mono_left h hf.disj_frame) hf.disj_inv)
    hf.refines

/-- The left factor of a framed product is framed by the right factor and the frame. -/
lemma left {𝓟₁ 𝓟₂ : ProbSpace} (hd : Disjoint 𝓟₁.dom 𝓟₂.dom)
    (hf : Framed 𝓘 (𝓟₁ ⊗ 𝓟₂) 𝓟fr 𝓙 μ) : Framed 𝓘 𝓟₁ (𝓟₂ ⊗ 𝓟fr) 𝓙 μ where
  inv := hf.inv
  disj_frame := Set.disjoint_union_right.mpr
    ⟨hd, hf.disj_frame.mono_left Set.subset_union_left⟩
  disj_inv := by
    have := hf.disj_inv
    change Disjoint (𝓟₁.dom ∪ (𝓟₂.dom ∪ 𝓟fr.dom)) 𝓙.dom
    change Disjoint ((𝓟₁.dom ∪ 𝓟₂.dom) ∪ 𝓟fr.dom) 𝓙.dom at this
    rwa [Set.union_assoc] at this
  refines := Distr.Refines.mono
    (ProbSpace.product_mono_left (ProbSpace.product_assoc' 𝓟₁ 𝓟₂ 𝓟fr) hf.disj_inv) hf.refines

/-- The right factor of a framed product is framed by the left factor and the frame. -/
lemma right {𝓟₁ 𝓟₂ : ProbSpace} (hd : Disjoint 𝓟₁.dom 𝓟₂.dom)
    (hf : Framed 𝓘 (𝓟₁ ⊗ 𝓟₂) 𝓟fr 𝓙 μ) : Framed 𝓘 𝓟₂ (𝓟₁ ⊗ 𝓟fr) 𝓙 μ := by
  have hc : (𝓟₂ ⊗ 𝓟₁) ≤ (𝓟₁ ⊗ 𝓟₂) := ProbSpace.product_comm hd
  have hf' : Framed 𝓘 (𝓟₂ ⊗ 𝓟₁) 𝓟fr 𝓙 μ := hf.mono hc
  exact hf'.left hd.symm

/-- Moving the left factor of the frame into the program's space. -/
lemma unright {𝓟₁ 𝓟₂ : ProbSpace} (hd₁ : Disjoint 𝓟₁.dom 𝓟fr.dom)
    (hf : Framed 𝓘 𝓟₂ (𝓟₁ ⊗ 𝓟fr) 𝓙 μ) : Framed 𝓘 (𝓟₁ ⊗ 𝓟₂) 𝓟fr 𝓙 μ := by
  have hd : Disjoint 𝓟₂.dom (𝓟₁.dom ∪ 𝓟fr.dom) := hf.disj_frame
  have h₂₁ : Disjoint 𝓟₂.dom 𝓟₁.dom := (Set.disjoint_union_right.mp hd).1
  have h₂f : Disjoint 𝓟₂.dom 𝓟fr.dom := (Set.disjoint_union_right.mp hd).2
  refine ⟨hf.inv, Set.disjoint_union_left.mpr ⟨hd₁, h₂f⟩, ?_, ?_⟩
  · have h := hf.disj_inv
    change Disjoint (𝓟₂.dom ∪ (𝓟₁.dom ∪ 𝓟fr.dom)) 𝓙.dom at h
    change Disjoint ((𝓟₁.dom ∪ 𝓟₂.dom) ∪ 𝓟fr.dom) 𝓙.dom
    rwa [Set.union_comm 𝓟₁.dom 𝓟₂.dom, Set.union_assoc]
  · refine Distr.Refines.mono (ProbSpace.product_mono_left ?_ hf.disj_inv) hf.refines
    exact (ProbSpace.product_mono_left (ProbSpace.product_comm h₂₁)
      (Set.disjoint_union_left.mpr ⟨h₂f, hd₁⟩)).trans (ProbSpace.product_assoc 𝓟₂ 𝓟₁ 𝓟fr)

/-- The invariant can always be established by a space that owns exactly the variables of the
invariant. -/
lemma shrink_inv (hf : Framed 𝓘 𝓟 𝓟fr 𝓙 μ) :
    ∃ 𝓙₀ : ProbSpace, 𝓙₀.dom = 𝓘.dom ∧ 𝓘.dom ⊆ 𝓙.dom ∧ Framed 𝓘 𝓟 𝓟fr 𝓙₀ μ := by
  obtain ⟨hV, hinv⟩ := OProp.sure_forget 𝓘.footprint hf.inv
  refine ⟨ProbSpace.forget 𝓙 𝓘.dom hV, rfl, hV,
    ⟨hinv, hf.disj_frame, hf.disj_inv.mono_right hV, ?_⟩⟩
  exact Distr.Refines.mono
    (ProbSpace.product_mono_right (ProbSpace.forget_le _ _) (hf.disj_inv.mono_right hV))
    hf.refines

/-- **Padding.**  A space framed in `ν` can be extended by variables that `ν` allocates and
that are not owned by the frame or by the invariant space. -/
lemma pad (hf : Framed 𝓘 𝓟 𝓟fr 𝓙 μ) {U : Set Var} (hU : Distr.Owns μ U)
    (hUfr : Disjoint U 𝓟fr.dom) (hUJ : Disjoint U 𝓙.dom) :
    ∃ 𝓟' : ProbSpace, 𝓟 ≤ 𝓟' ∧ 𝓟'.dom = 𝓟.dom ∪ U ∧ Framed 𝓘 𝓟' 𝓟fr 𝓙 μ := by
  set U' := U \ 𝓟.dom
  obtain ⟨T, hT, hTref, -⟩ := Distr.Refines.pad hf.refines (U := U') fun m hm ↦
    Set.sdiff_subset.trans (hU m hm)
  have hfr : Disjoint T.dom 𝓟fr.dom := hT ▸ hUfr.mono_left Set.sdiff_subset
  have hJ : Disjoint T.dom 𝓙.dom := hT ▸ hUJ.mono_left Set.sdiff_subset
  have hP : Disjoint 𝓟.dom T.dom := hT ▸ Set.disjoint_sdiff_right
  have hPfr : Disjoint 𝓟.dom 𝓟fr.dom := hf.disj_frame
  have hPJ : Disjoint 𝓟.dom 𝓙.dom := (Set.disjoint_union_left.mp hf.disj_inv).1
  have hfrJ : Disjoint 𝓟fr.dom 𝓙.dom := (Set.disjoint_union_left.mp hf.disj_inv).2
  refine ⟨𝓟 ⊗ T, ProbSpace.le_product_left 𝓟 T, ?_, hf.inv, ?_, ?_, ?_⟩
  · change 𝓟.dom ∪ T.dom = 𝓟.dom ∪ U
    rw [hT, Set.union_sdiff_self]
  · exact Set.disjoint_union_left.mpr ⟨hPfr, hfr⟩
  · change Disjoint ((𝓟.dom ∪ T.dom) ∪ 𝓟fr.dom) 𝓙.dom
    exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hPJ, hJ⟩, hfrJ⟩
  · refine Distr.Refines.mono ?_ hTref
    refine (ProbSpace.product_mono_left
      (ProbSpace.product_swap_right hfr.symm (Set.disjoint_union_right.mpr ⟨hPfr, hP⟩)) ?_).trans
      (ProbSpace.product_swap_right hJ.symm ?_)
    · change Disjoint ((𝓟.dom ∪ 𝓟fr.dom) ∪ T.dom) 𝓙.dom
      exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hPJ, hfrJ⟩, hJ⟩
    · change Disjoint (𝓟.dom ∪ 𝓟fr.dom) (𝓙.dom ∪ T.dom)
      exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_right.mpr ⟨hPJ, hP⟩,
        Set.disjoint_union_right.mpr ⟨hfrJ, hfr.symm⟩⟩

/-- A framed distribution allocates the variables of the framed space. -/
lemma owns (hf : Framed 𝓘 𝓟 𝓟fr 𝓙 μ) : Distr.Owns μ 𝓟.dom := fun m hm ↦
  Set.subset_union_left.trans (Set.subset_union_left.trans (Distr.Refines.owns hf.refines m hm))

/-- **Splitting.**  A distribution framed with a sum is the average of distributions framed with
the summands. -/
lemma split {ι : Type} {ξ : PMF ι} {𝓟 : ι → ProbSpace} {V : Set Var}
    {hd : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support}
    {hdom : ∀ i, (𝓟 i).dom = V} (hf : Framed 𝓘 (ProbSpace.sum ξ 𝓟 V hd hdom) 𝓟fr 𝓙 μ) :
    ∃ μ' : ι → Distr Mem, (∀ i, ξ i ≠ 0 → Framed 𝓘 (𝓟 i) 𝓟fr 𝓙 (μ' i)) ∧ μ = ξ.bind μ' := by
  have href : ProbSpace.sumProd ξ 𝓟 (𝓟fr ⊗ 𝓙) V hd hdom ≼ μ :=
    Distr.Refines.mono ((ProbSpace.sumProd_le_sum_product ξ 𝓟 _ V hd hdom).trans
      (ProbSpace.product_assoc' _ _ _)) hf.refines
  obtain ⟨μ', hμ', rfl⟩ := Distr.Refines.split (hd := ProbSpace.sum_prod_disjoint _ hd) href
  refine ⟨μ', fun i hi ↦ ⟨hf.inv, ?_, ?_, ?_⟩, rfl⟩
  · rw [hdom i]; exact hf.disj_frame
  · rw [hdom i]; exact hf.disj_inv
  · exact Distr.Refines.mono (ProbSpace.product_assoc _ _ _) (hμ' i hi)

/-- **Gluing.**  If each distribution `ν i` of positive weight is framed with a space `𝓠 i`
over the variables `W`, then their `ξ`-average is framed with a sum of spaces above the
`𝓠 i` (copies of the `𝓠 i` with disjoint supports). -/
lemma glue {ι : Type} [Countable ι] {ξ : PMF ι} {𝓠 𝓙 : ι → ProbSpace} {ν : ι → Distr Mem}
    {W : Set Var} (hf : ∀ i, ξ i ≠ 0 → Framed 𝓘 (𝓠 i) 𝓟fr (𝓙 i) (ν i))
    (hW : ∀ i, ξ i ≠ 0 → (𝓠 i).dom = W) (hJ : ∀ i, ξ i ≠ 0 → (𝓙 i).dom = 𝓘.dom) :
    ∃ (𝓠' : ι → ProbSpace) (hd : ∀ {i j : ι}, i ≠ j → Disjoint (𝓠' i).support (𝓠' j).support)
      (hdom : ∀ i, (𝓠' i).dom = W) (𝓙' : ProbSpace),
      (∀ i, ξ i ≠ 0 → 𝓠 i ≤ 𝓠' i) ∧
      Framed 𝓘 (ProbSpace.sum ξ 𝓠' W hd hdom) 𝓟fr 𝓙' (ξ.bind ν) := by
  classical
  haveI : Encodable ι := Encodable.ofCountable ι
  obtain ⟨i₀, hi₀⟩ := ξ.support_nonempty
  have hi₀' : ξ i₀ ≠ 0 := (PMF.mem_support_iff _ _).mp hi₀
  -- Summands of weight zero are replaced by spaces over the right variables
  let 𝓠₀ : ι → ProbSpace := fun i ↦ if ξ i = 0 then
    ProbSpace.trivialOn W (fun _ ↦ ProbSpace.junkMem W) (fun _ ↦ ProbSpace.junkMem_dom W)
    else 𝓠 i
  let 𝓙₀ : ι → ProbSpace := fun i ↦ if ξ i = 0 then
    ProbSpace.trivialOn 𝓘.dom (fun _ ↦ ProbSpace.junkMem 𝓘.dom)
      (fun _ ↦ ProbSpace.junkMem_dom 𝓘.dom)
    else 𝓙 i
  have h𝓠₀ : ∀ i, ξ i ≠ 0 → 𝓠₀ i = 𝓠 i := fun i hi ↦ if_neg hi
  have h𝓙₀ : ∀ i, ξ i ≠ 0 → 𝓙₀ i = 𝓙 i := fun i hi ↦ if_neg hi
  have hW₀ : ∀ i, (𝓠₀ i).dom = W := fun i ↦ by
    by_cases hi : ξ i = 0
    · simp only [𝓠₀, if_pos hi]; rfl
    · rw [h𝓠₀ i hi]; exact hW i hi
  have hJ₀ : ∀ i, (𝓙₀ i).dom = 𝓘.dom := fun i ↦ by
    by_cases hi : ξ i = 0
    · simp only [𝓙₀, if_pos hi]; rfl
    · rw [h𝓙₀ i hi]; exact hJ i hi
  -- Disjoint copies
  let 𝓠' : ι → ProbSpace := fun i ↦ (𝓠₀ i).shift (Encodable.encode i)
  have hd : ∀ {i j : ι}, i ≠ j → Disjoint (𝓠' i).support (𝓠' j).support :=
    fun hij ↦ ProbSpace.disjoint_support_shift _ _ fun h ↦ hij (Encodable.encode_injective h)
  have hdom : ∀ i, (𝓠' i).dom = W := hW₀
  have hWfr : Disjoint W 𝓟fr.dom := hW i₀ hi₀' ▸ (hf i₀ hi₀').disj_frame
  have hWI : Disjoint (W ∪ 𝓟fr.dom) 𝓘.dom := by
    have := (hf i₀ hi₀').disj_inv
    rwa [hW i₀ hi₀', hJ i₀ hi₀'] at this
  -- The summands of the glued distribution
  let 𝓡 : ι → ProbSpace := fun i ↦ (𝓠' i ⊗ 𝓟fr) ⊗ 𝓙₀ i
  have hdR : ∀ {i j : ι}, i ≠ j → Disjoint (𝓡 i).support (𝓡 j).support :=
    fun hij ↦ ProbSpace.disjoint_support_product' (ProbSpace.disjoint_support_product' (hd hij))
  have hdomR : ∀ i, (𝓡 i).dom = (W ∪ 𝓟fr.dom) ∪ 𝓘.dom := fun i ↦ by
    change ((𝓠' i).dom ∪ 𝓟fr.dom) ∪ (𝓙₀ i).dom = _
    rw [hdom i, hJ₀ i]
  have hdisjR : ∀ i, Disjoint (𝓠' i ⊗ 𝓟fr).dom (𝓙₀ i).dom := fun i ↦ by
    change Disjoint ((𝓠' i).dom ∪ 𝓟fr.dom) (𝓙₀ i).dom
    rw [hdom i, hJ₀ i]; exact hWI
  have href : ProbSpace.sum ξ 𝓡 _ hdR hdomR ≼ ξ.bind ν := by
    refine Distr.Refines.sum fun i hi ↦ Distr.Refines.mono ?_ (hf i hi).refines
    change (((𝓠₀ i).shift _ ⊗ 𝓟fr) ⊗ 𝓙₀ i) ≤ _
    rw [h𝓠₀ i hi, h𝓙₀ i hi]
    refine ProbSpace.product_mono_left
      (ProbSpace.product_mono_left (ProbSpace.shift_le _ _) (hf i hi).disj_frame) ?_
    exact (hf i hi).disj_inv
  set Z := ProbSpace.sum ξ 𝓡 _ hdR hdomR
  have hXZ : (ProbSpace.sum ξ 𝓠' W hd hdom ⊗ 𝓟fr) ≤ Z :=
    (ProbSpace.sum_product_le_sumProd ξ 𝓠' 𝓟fr W hd hdom).trans
      (ProbSpace.sum_mono (ProbSpace.sum_prod_disjoint 𝓟fr hd) hdR (ProbSpace.sum_prod_dom 𝓟fr hdom) hdomR Set.subset_union_left
        fun v _ ↦ ProbSpace.le_product_left _ _)
  have hIZ : 𝓘.dom ⊆ Z.dom := Set.subset_union_right
  -- The invariant holds almost surely in the glued space
  have hinvZ : OProp.sure 𝓘.to_MProp Z := by
    intro n hn
    change n ∈ (ProbSpace.sum ξ 𝓡 _ hdR hdomR).support at hn
    rw [ProbSpace.support_sum] at hn
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hn
    obtain ⟨i, hi, hni⟩ := hn
    change 𝓘.to_MProp (ProbSpace.sumState 𝓡 _ n)
    rw [ProbSpace.sumState_of_mem hdR hni]
    have hinv : OProp.sure 𝓘.to_MProp (𝓙₀ i) := by rw [h𝓙₀ i hi]; exact (hf i hi).inv
    exact (OProp.sure 𝓘.to_MProp).mono (ProbSpace.le_product_right (hdisjR i)) hinv hni
  obtain ⟨hIZ', hinv'⟩ := OProp.sure_forget 𝓘.footprint hinvZ
  refine ⟨𝓠', hd, hdom, ProbSpace.forget Z 𝓘.dom hIZ, fun i hi ↦ ?_, hinv', hWfr, hWI, ?_⟩
  · change 𝓠 i ≤ (𝓠₀ i).shift _
    rw [h𝓠₀ i hi]; exact ProbSpace.le_shift _ _
  · exact Distr.Refines.mono (ProbSpace.product_forget_le hXZ hIZ) href

end Framed

end Pcol
