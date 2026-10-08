/-
Algebraic laws of the product of probability spaces.

The product `p ⊗ q` encodes a pair of outcomes `(i, j)` as the natural number
`Nat.pairEquiv (i, j)`, so it is only monotone, commutative, associative and unital up to a
relabeling of the outcomes.  The order on probability spaces allows such relabelings
(`ProbSpace.Relabels`), and this file proves the corresponding laws.

The relabelings are all obtained from measure-preserving maps between the (uncompleted)
product measures, using the measure-preserving maps provided by Mathlib.
-/
import PcolIris.OProp.SumProd

namespace Pcol

open MeasureTheory MeasurableSpace

namespace ProbSpace

/-! ### Measure-preserving maps between non-canonical measurable spaces

The σ-algebras of probability spaces on `ℕ` are not the instance `Nat.instMeasurableSpace`, so
the Mathlib lemmas about measure-preserving maps are restated here with the measurable
spaces as explicit arguments. -/

section MP

variable {α β γ : Type*}

/-- `MP ma mb f μ ν`: the map `f` is measure-preserving from `(ma, μ)` to `(mb, ν)`. -/
abbrev MP (ma : MeasurableSpace α) (mb : MeasurableSpace β) (f : α → β) (μ : @Measure α ma)
    (ν : @Measure β mb) : Prop :=
  @MeasurePreserving α β ma mb f μ ν

variable {ma : MeasurableSpace α} {mb : MeasurableSpace β} {mc : MeasurableSpace γ}
  {μa : @Measure α ma} {μb : @Measure β mb} {μc : @Measure γ mc}

lemma MP.comp {g : β → γ} {f : α → β} (hg : MP mb mc g μb μc) (hf : MP ma mb f μa μb) :
    MP ma mc (g ∘ f) μa μc :=
  @MeasurePreserving.comp α β γ ma mb mc μa μb μc g f hg hf

lemma MP.measure_preimage {f : α → β} (hf : MP ma mb f μa μb) {s : Set β}
    (hs : @NullMeasurableSet β mb s μb) : μa (f ⁻¹' s) = μb s :=
  @MeasurePreserving.measure_preimage α β ma mb μa μb f hf s hs

lemma MP.nullMeasurableSet_preimage {f : α → β} (hf : MP ma mb f μa μb) {s : Set β}
    (hs : @NullMeasurableSet β mb s μb) : @NullMeasurableSet α ma (f ⁻¹' s) μa :=
  @NullMeasurableSet.preimage α β ma mb μa μb f s hs
    (@MeasurePreserving.quasiMeasurePreserving α β ma mb μa μb f hf)

lemma MP.id (μ : @Measure α ma) : MP ma ma id μ μ := @MeasurePreserving.id α ma μ

end MP

/-! ### Spaces lying inside a completion -/

/-- `IsCompletionOf a m ν` states that the σ-algebra of `a` lies between `m` and its
completion for `ν`, and that the measure of `a` agrees with `ν` there.  The product of two
probability spaces is the completion of the product σ-algebra (`IsCompletionOf.product`),
and the property is stable under products (`IsCompletionOf.prod`), which is what makes it
possible to compare nested products. -/
structure IsCompletionOf (a : ProbSpace) (m : MeasurableSpace ℕ) (ν : @Measure ℕ m) : Prop where
  le : m ≤ a.mspace
  null : ∀ S, a.mspace.MeasurableSet' S → @NullMeasurableSet ℕ m S ν
  meas : ∀ S, a.mspace.MeasurableSet' S → a.meas S = ν S

lemma IsCompletionOf.self (a : ProbSpace) : IsCompletionOf a a.mspace a.meas :=
  ⟨le_refl _, fun S hS ↦ @MeasurableSet.nullMeasurableSet ℕ a.mspace a.meas S hS,
    fun _ _ ↦ rfl⟩

lemma IsCompletionOf.product (p q : ProbSpace) :
    IsCompletionOf (p ⊗ q) (prodMSpace p q) (prodMeasure p q) :=
  ⟨fun S hS ↦ @MeasurableSet.nullMeasurableSet ℕ (prodMSpace p q) (prodMeasure p q) S hS,
    fun _ hS ↦ hS, fun _ _ ↦ rfl⟩

/-! ### Relabelings from measure-preserving maps -/

/-- If `p` lies inside the completion of `(m, ν)`, then any map that is measure-preserving
from `q` to `(m, ν)` relabels `p` into `q`, as far as the σ-algebras and the measures are
concerned. -/
lemma relabels_of_measurePreserving {p q : ProbSpace} {m : MeasurableSpace ℕ}
    {ν : @Measure ℕ m} {g : ℕ → ℕ} (hp : IsCompletionOf p m ν)
    (hg : MP q.mspace m g q.meas ν)
    (hdom : p.dom ⊆ q.dom) (hst : ∀ i ∈ q.support, p.state (g i) ≤ q.state i) :
    Relabels p q g := by
  haveI : @Measure.IsComplete ℕ q.mspace q.meas := q.complete
  refine ⟨fun E hE ↦ ?_, fun E hE ↦ ?_, hdom, hst⟩
  · exact @NullMeasurableSet.measurable_of_complete ℕ q.mspace q.meas _
      (hg.nullMeasurableSet_preimage (hp.null E hE)) this
  · refine ENNReal.coe_injective ?_
    rw [prob_coe, prob_coe]
    change q.meas (g ⁻¹' E) = p.meas E
    rw [hp.meas E hE]
    exact hg.measure_preimage (hp.null E hE)

/-- A relabeling is a measure-preserving map. -/
lemma Relabels.measurePreserving {p q : ProbSpace} {g : ℕ → ℕ} (hg : Relabels p q g) :
    MP q.mspace p.mspace g q.meas p.meas := by
  have hmeas : @Measurable ℕ ℕ q.mspace p.mspace g := fun E hE ↦ hg.mspace E hE
  refine @MeasurePreserving.mk ℕ ℕ q.mspace p.mspace g q.meas p.meas hmeas ?_
  refine @Measure.ext ℕ p.mspace _ _ (fun E hE ↦ ?_)
  rw [@Measure.map_apply ℕ ℕ q.mspace p.mspace q.meas g hmeas E hE]
  calc q.meas (g ⁻¹' E) = ((q.μ (g ⁻¹' E) : NNReal) : ENNReal) := (prob_coe _ _).symm
    _ = ((p.μ E : NNReal) : ENNReal) := by rw [hg.μ E hE]
    _ = p.meas E := prob_coe _ _

/-! ### The product measure as a measure-preserving image -/

lemma measurePreserving_pair (p q : ProbSpace) :
    MP (p.mspace.prod q.mspace) (prodMSpace p q) Nat.pairEquiv
      (@Measure.prod ℕ ℕ p.mspace q.mspace p.meas q.meas) (prodMeasure p q) :=
  @MeasurePreserving.mk (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) (prodMSpace p q) _ _ _
    (pairEquiv_measurable p q) rfl

lemma measurePreserving_unpair (p q : ProbSpace) :
    MP (prodMSpace p q) (p.mspace.prod q.mspace) Nat.pairEquiv.symm
      (prodMeasure p q) (@Measure.prod ℕ ℕ p.mspace q.mspace p.meas q.meas) :=
  @MeasurePreserving.symm (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) (prodMSpace p q)
    (pairMeasurableEquiv p q) _ _ (measurePreserving_pair p q)

/-- Forgetting the completion of a product is measure-preserving. -/
lemma measurePreserving_uncomplete (p q : ProbSpace) :
    MP (p ⊗ q).mspace (prodMSpace p q) id (p ⊗ q).meas (prodMeasure p q) := by
  have hmeas : @Measurable ℕ ℕ (p ⊗ q).mspace (prodMSpace p q) id :=
    fun E hE ↦ @MeasurableSet.nullMeasurableSet ℕ (prodMSpace p q) (prodMeasure p q) E hE
  refine @MeasurePreserving.mk ℕ ℕ (p ⊗ q).mspace (prodMSpace p q) id _ _ hmeas ?_
  refine @Measure.ext ℕ (prodMSpace p q) _ _ (fun E hE ↦ ?_)
  rw [@Measure.map_apply ℕ ℕ (p ⊗ q).mspace (prodMSpace p q) (p ⊗ q).meas id hmeas E hE]
  rfl

/-- `MeasurePreserving.prod` for probability spaces. -/
lemma MP.prod {α β γ δ : Type*} {ma : MeasurableSpace α} {mb : MeasurableSpace β}
    {mc : MeasurableSpace γ} {md : MeasurableSpace δ} {μa : @Measure α ma} {μb : @Measure β mb}
    {μc : @Measure γ mc} {μd : @Measure δ md} [@IsProbabilityMeasure α ma μa]
    [@IsProbabilityMeasure γ mc μc] {f : α → β} {g : γ → δ}
    (hf : MP ma mb f μa μb) (hg : MP mc md g μc μd) :
    MP (ma.prod mc) (mb.prod md) (Prod.map f g)
      (@Measure.prod α γ ma mc μa μc) (@Measure.prod β δ mb md μb μd) :=
  @MeasurePreserving.prod α β γ ma mb mc δ md μa μb μc μd inferInstance inferInstance f g hf hg

/-! ### Monotonicity -/

/-- The relabeling of a product along relabelings of its two factors. -/
def prodRelabel (a b : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.pairEquiv (Prod.map a b (Nat.pairEquiv.symm k))

/-- The product of probability spaces is monotone.  Since the memory of a product is a
left-biased union, the variables gained by the left factor must not clash with the right
factor. -/
theorem product_mono {p p' q q' : ProbSpace} (h₁ : p ≤ p') (h₂ : q ≤ q')
    (hd : Disjoint p'.dom q.dom) : (p ⊗ q) ≤ (p' ⊗ q') := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  haveI := isProbabilityMeasure_meas p'
  haveI := isProbabilityMeasure_meas q'
  refine ⟨prodRelabel a b, relabels_of_measurePreserving (IsCompletionOf.product p q) ?_
    (Set.union_subset_union ha.dom hb.dom) ?_⟩
  · exact (measurePreserving_pair p q).comp ((MP.prod ha.measurePreserving hb.measurePreserving).comp
      ((measurePreserving_unpair p' q').comp (measurePreserving_uncomplete p' q')))
  · intro k hk
    obtain ⟨hi, hj⟩ := mem_support_product_iff.mp hk
    rw [product_state, product_state, prodRelabel, Equiv.symm_apply_apply]
    refine Mem.union_mono (ha.state _ hi) (hb.state _ hj) ?_
    rw [p'.dom_valid, q.dom_valid]
    exact hd

/-- The product of probability spaces is monotone in its left argument. -/
lemma product_mono_left {p p' q : ProbSpace} (h : p ≤ p') (hd : Disjoint p'.dom q.dom) :
    (p ⊗ q) ≤ (p' ⊗ q) :=
  product_mono h (le_refl q) hd

/-- The product of probability spaces is monotone in its right argument. -/
lemma product_mono_right {p q q' : ProbSpace} (h : q ≤ q') (hd : Disjoint p.dom q.dom) :
    (p ⊗ q) ≤ (p ⊗ q') :=
  product_mono (le_refl p) h hd

/-! ### Commutativity -/

/-- Swapping the two coordinates of an encoded pair. -/
def swapRelabel (k : ℕ) : ℕ := Nat.pairEquiv (Nat.pairEquiv.symm k).swap

/-- The product of probability spaces with disjoint domains is commutative. -/
theorem product_comm {p q : ProbSpace} (hd : Disjoint p.dom q.dom) : (q ⊗ p) ≤ (p ⊗ q) := by
  haveI := isProbabilityMeasure_meas p
  haveI := isProbabilityMeasure_meas q
  have hswap : MP (p.mspace.prod q.mspace) (q.mspace.prod p.mspace) Prod.swap
      (@Measure.prod ℕ ℕ p.mspace q.mspace p.meas q.meas)
      (@Measure.prod ℕ ℕ q.mspace p.mspace q.meas p.meas) :=
    @Measure.measurePreserving_swap ℕ ℕ p.mspace q.mspace p.meas q.meas inferInstance
      inferInstance
  refine ⟨swapRelabel, relabels_of_measurePreserving (IsCompletionOf.product q p) ?_ ?_ ?_⟩
  · exact (measurePreserving_pair q p).comp
      (hswap.comp ((measurePreserving_unpair p q).comp (measurePreserving_uncomplete p q)))
  · exact (Set.union_comm _ _).subset
  · intro k _
    rw [product_state, product_state, swapRelabel, Equiv.symm_apply_apply]
    refine le_of_eq (Mem.union_comm ?_).symm
    rw [p.dom_valid, q.dom_valid]
    exact hd

/-! ### Products of spaces lying inside completions -/

/-- `Nat.pairEquiv` as a measurable equivalence onto the pushforward σ-algebra. -/
def pairEquivOf (m : MeasurableSpace (ℕ × ℕ)) :
    @MeasurableEquiv (ℕ × ℕ) ℕ m (m.map Nat.pairEquiv) :=
  @MeasurableEquiv.mk (ℕ × ℕ) ℕ m (m.map Nat.pairEquiv) Nat.pairEquiv
    (measurable_iff_le_map.mpr fun _ h ↦ h)
    (by
      intro S hS
      change m.MeasurableSet' (Nat.pairEquiv ⁻¹' (Nat.pairEquiv.symm ⁻¹' S))
      rwa [← Set.preimage_comp, show (Nat.pairEquiv.symm ∘ Nat.pairEquiv) = id from
        funext (fun x ↦ Nat.pairEquiv.left_inv x), Set.preimage_id])

/-- The pushforward of a measure along the pairing. -/
noncomputable abbrev pairMeasure {m : MeasurableSpace (ℕ × ℕ)} (ν : @Measure (ℕ × ℕ) m) :
    @Measure ℕ (m.map Nat.pairEquiv) :=
  @Measure.map (ℕ × ℕ) ℕ m (m.map Nat.pairEquiv) Nat.pairEquiv ν

lemma measurePreserving_pairEquivOf {m : MeasurableSpace (ℕ × ℕ)} (ν : @Measure (ℕ × ℕ) m) :
    MP m (m.map Nat.pairEquiv) Nat.pairEquiv ν (pairMeasure ν) :=
  @MeasurePreserving.mk (ℕ × ℕ) ℕ m (m.map Nat.pairEquiv) _ _ _
    (@MeasurableEquiv.measurable (ℕ × ℕ) ℕ m (m.map Nat.pairEquiv) (pairEquivOf m)) rfl

lemma measurePreserving_unpairEquivOf {m : MeasurableSpace (ℕ × ℕ)} (ν : @Measure (ℕ × ℕ) m) :
    MP (m.map Nat.pairEquiv) m Nat.pairEquiv.symm (pairMeasure ν) ν :=
  @MeasurePreserving.symm (ℕ × ℕ) ℕ m (m.map Nat.pairEquiv) (pairEquivOf m) _ _
    (measurePreserving_pairEquivOf ν)

lemma pairMeasure_apply {m : MeasurableSpace (ℕ × ℕ)} (ν : @Measure (ℕ × ℕ) m) (S : Set ℕ) :
    pairMeasure ν S = ν (Nat.pairEquiv ⁻¹' S) :=
  @MeasurableEquiv.map_apply (ℕ × ℕ) ℕ m (m.map Nat.pairEquiv) ν (pairEquivOf m) S

section CompletionProd

variable {a b : ProbSpace} {ma mb : MeasurableSpace ℕ} {νa : @Measure ℕ ma}
  {νb : @Measure ℕ mb}

/-- Every set of the product σ-algebra of `a` and `b` is null-measurable for the product of
`νa` and `νb`. -/
lemma IsCompletionOf.prod_null
    (ha : IsCompletionOf a ma νa) (hb : IsCompletionOf b mb νb) :
    a.mspace.prod b.mspace ≤ @NullMeasurableSpace.instMeasurableSpace (ℕ × ℕ) (ma.prod mb)
      (@Measure.prod ℕ ℕ ma mb νa νb) := by
  refine sup_le ?_ ?_
  · rintro _ ⟨S, hS, rfl⟩
    have := @NullMeasurableSet.prod ℕ ℕ ma mb νa νb S Set.univ (ha.null S hS)
      (@nullMeasurableSet_univ ℕ mb νb)
    rwa [Set.prod_univ] at this
  · rintro _ ⟨T, hT, rfl⟩
    have := @NullMeasurableSet.prod ℕ ℕ ma mb νa νb Set.univ T
      (@nullMeasurableSet_univ ℕ ma νa) (hb.null T hT)
    rwa [Set.univ_prod] at this

/-- On the product σ-algebra of `a` and `b`, the product of their measures is the product of
`νa` and `νb`. -/
lemma IsCompletionOf.prod_meas [@SFinite ℕ mb νb]
    (ha : IsCompletionOf a ma νa) (hb : IsCompletionOf b mb νb) {F : Set (ℕ × ℕ)}
    (hF : (a.mspace.prod b.mspace).MeasurableSet' F) :
    @Measure.prod ℕ ℕ a.mspace b.mspace a.meas b.meas F = @Measure.prod ℕ ℕ ma mb νa νb F := by
  haveI := isProbabilityMeasure_meas a
  haveI := isProbabilityMeasure_meas b
  have hle := ha.prod_null hb
  let ρ : @Measure (ℕ × ℕ) (a.mspace.prod b.mspace) :=
    @Measure.trim (ℕ × ℕ) (a.mspace.prod b.mspace) _
      (@Measure.completion (ℕ × ℕ) (ma.prod mb) (@Measure.prod ℕ ℕ ma mb νa νb)) hle
  have hρ : ∀ G, (a.mspace.prod b.mspace).MeasurableSet' G →
      ρ G = @Measure.prod ℕ ℕ ma mb νa νb G := fun G hG ↦
    @trim_measurableSet_eq (ℕ × ℕ) (a.mspace.prod b.mspace) _ _ G hle hG
  have key : @Measure.prod ℕ ℕ a.mspace b.mspace a.meas b.meas = ρ := by
    refine @ext_of_generate_finite _ (a.mspace.prod b.mspace) _ _
      (Set.image2 (fun x1 x2 ↦ x1 ×ˢ x2) {s | @MeasurableSet ℕ a.mspace s}
        {t | @MeasurableSet ℕ b.mspace t})
      (@generateFrom_prod ℕ ℕ a.mspace b.mspace).symm (@isPiSystem_prod ℕ ℕ a.mspace b.mspace)
      inferInstance ?_ ?_
    · rintro _ ⟨S, hS, T, hT, rfl⟩
      rw [@Measure.prod_prod ℕ ℕ a.mspace b.mspace a.meas b.meas _ S T,
        hρ _ (@MeasurableSet.prod ℕ ℕ a.mspace b.mspace S T hS hT),
        @Measure.prod_prod ℕ ℕ ma mb νa νb _ S T, ha.meas S hS, hb.meas T hT]
    · rw [hρ _ (@MeasurableSet.univ _ (a.mspace.prod b.mspace)),
        ← Set.univ_prod_univ, @Measure.prod_prod ℕ ℕ ma mb νa νb _ Set.univ Set.univ,
        @Measure.prod_prod ℕ ℕ a.mspace b.mspace a.meas b.meas _ Set.univ Set.univ,
        ← ha.meas _ (@MeasurableSet.univ _ a.mspace), ← hb.meas _ (@MeasurableSet.univ _ b.mspace)]
  rw [key, hρ F hF]

/-- The product of spaces lying inside completions lies inside the completion of the product.
-/
theorem IsCompletionOf.prod [@SFinite ℕ mb νb]
    (ha : IsCompletionOf a ma νa) (hb : IsCompletionOf b mb νb) :
    IsCompletionOf (a ⊗ b) ((ma.prod mb).map Nat.pairEquiv)
      (pairMeasure (@Measure.prod ℕ ℕ ma mb νa νb)) := by
  set ν' := pairMeasure (@Measure.prod ℕ ℕ ma mb νa νb)
  have hunpair := measurePreserving_unpairEquivOf (@Measure.prod ℕ ℕ ma mb νa νb)
  -- The sets of the (uncompleted) product σ-algebra of `a` and `b`
  have hbase : ∀ F, (prodMSpace a b).MeasurableSet' F →
      @NullMeasurableSet ℕ ((ma.prod mb).map Nat.pairEquiv) F ν' ∧ ν' F = prodMeasure a b F := by
    intro F hF
    have hF' : (a.mspace.prod b.mspace).MeasurableSet' (Nat.pairEquiv ⁻¹' F) := hF
    refine ⟨?_, ?_⟩
    · have h := hunpair.nullMeasurableSet_preimage (ha.prod_null hb _ hF')
      rwa [← Set.preimage_comp, show (Nat.pairEquiv ∘ Nat.pairEquiv.symm) = id from
        funext (fun x ↦ Nat.pairEquiv.right_inv x), Set.preimage_id] at h
    · exact (pairMeasure_apply _ F).trans ((ha.prod_meas hb hF').symm.trans
        (prodMeasure_apply a b F).symm)
  -- Null sets of the product of `a` and `b` are null for `ν'`
  have hnull : ∀ N, prodMeasure a b N = 0 → ν' N = 0 := by
    intro N hN
    obtain ⟨M, hNM, hM, hM0⟩ :=
      @exists_measurable_superset_of_null ℕ (prodMSpace a b) (prodMeasure a b) N hN
    exact measure_mono_null hNM (by rw [(hbase M hM).2, hM0])
  have hae : ∀ {E F : Set ℕ}, E =ᵐ[prodMeasure a b] F → E =ᵐ[ν'] F := by
    intro E F h
    rw [Filter.EventuallyEq, ae_iff] at h ⊢
    exact hnull _ h
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    refine @MeasurableSet.nullMeasurableSet ℕ (prodMSpace a b) (prodMeasure a b) E ?_
    change (a.mspace.prod b.mspace).MeasurableSet' (Nat.pairEquiv ⁻¹' E)
    exact prod_le_prod_right hb.le _ (prod_le_prod_left ha.le _ hE)
  · rintro E ⟨F, hF, hEF⟩
    exact @NullMeasurableSet.congr ℕ _ ν' F E (hbase F hF).1 (hae hEF).symm
  · rintro E ⟨F, hF, hEF⟩
    change prodMeasure a b E = ν' E
    rw [measure_congr hEF, measure_congr (hae hEF), (hbase F hF).2]

end CompletionProd

/-! ### Associativity -/

/-- Re-bracketing an encoded triple `(i, (j, l))` as `((i, j), l)`. -/
def assocRelabel (k : ℕ) : ℕ :=
  Nat.pairEquiv (Prod.map Nat.pairEquiv id
    ((Equiv.prodAssoc ℕ ℕ ℕ).symm (Prod.map id Nat.pairEquiv.symm (Nat.pairEquiv.symm k))))

/-- Re-bracketing an encoded triple `((i, j), l)` as `(i, (j, l))`. -/
def assocRelabel' (k : ℕ) : ℕ :=
  Nat.pairEquiv (Prod.map id Nat.pairEquiv
    ((Equiv.prodAssoc ℕ ℕ ℕ) (Prod.map Nat.pairEquiv.symm id (Nat.pairEquiv.symm k))))

lemma measurePreserving_prodAssoc' (p q r : ProbSpace) :
    MP ((p.mspace.prod q.mspace).prod r.mspace) (p.mspace.prod (q.mspace.prod r.mspace))
      (Equiv.prodAssoc ℕ ℕ ℕ)
      (@Measure.prod (ℕ × ℕ) ℕ (p.mspace.prod q.mspace) r.mspace
        (@Measure.prod ℕ ℕ p.mspace q.mspace p.meas q.meas) r.meas)
      (@Measure.prod ℕ (ℕ × ℕ) p.mspace (q.mspace.prod r.mspace) p.meas
        (@Measure.prod ℕ ℕ q.mspace r.mspace q.meas r.meas)) := by
  haveI := isProbabilityMeasure_meas q
  haveI := isProbabilityMeasure_meas r
  exact @measurePreserving_prodAssoc ℕ ℕ ℕ p.mspace q.mspace r.mspace p.meas q.meas r.meas
    inferInstance inferInstance

theorem product_assoc (p q r : ProbSpace) : ((p ⊗ q) ⊗ r) ≤ (p ⊗ (q ⊗ r)) := by
  haveI := isProbabilityMeasure_meas p
  haveI := isProbabilityMeasure_meas q
  haveI := isProbabilityMeasure_meas r
  haveI := isProbabilityMeasure_meas (q ⊗ r)
  haveI := isProbabilityMeasure_meas (p ⊗ q)
  haveI : @IsProbabilityMeasure (ℕ × ℕ) (p.mspace.prod q.mspace)
      (@Measure.prod ℕ ℕ p.mspace q.mspace p.meas q.meas) := inferInstance
  refine ⟨assocRelabel,
    relabels_of_measurePreserving ((IsCompletionOf.product p q).prod (IsCompletionOf.self r))
      ?_ (Set.union_assoc _ _ _).subset ?_⟩
  · have u1 := (measurePreserving_unpair p (q ⊗ r)).comp (measurePreserving_uncomplete p (q ⊗ r))
    have u2 := MP.prod (MP.id p.meas)
      ((measurePreserving_unpair q r).comp (measurePreserving_uncomplete q r))
    have u3 := @MeasurePreserving.symm ((ℕ × ℕ) × ℕ) (ℕ × ℕ × ℕ)
      ((p.mspace.prod q.mspace).prod r.mspace) (p.mspace.prod (q.mspace.prod r.mspace))
      (@MeasurableEquiv.prodAssoc ℕ ℕ ℕ p.mspace q.mspace r.mspace) _ _
      (measurePreserving_prodAssoc' p q r)
    have u4 := MP.prod (measurePreserving_pair p q) (MP.id r.meas)
    exact (measurePreserving_pairEquivOf _).comp (u4.comp (MP.comp u3 (u2.comp u1)))
  · intro k _
    simp only [assocRelabel, product_state, Equiv.symm_apply_apply, Prod.map_fst, Prod.map_snd,
      Equiv.prodAssoc_symm_apply, id_eq, Mem.union_assoc]
    exact le_refl _

theorem product_assoc' (p q r : ProbSpace) : (p ⊗ (q ⊗ r)) ≤ ((p ⊗ q) ⊗ r) := by
  haveI := isProbabilityMeasure_meas p
  haveI := isProbabilityMeasure_meas q
  haveI := isProbabilityMeasure_meas r
  haveI := isProbabilityMeasure_meas (q ⊗ r)
  haveI := isProbabilityMeasure_meas (p ⊗ q)
  haveI : @IsProbabilityMeasure (ℕ × ℕ) (p.mspace.prod q.mspace)
      (@Measure.prod ℕ ℕ p.mspace q.mspace p.meas q.meas) := inferInstance
  haveI : @IsProbabilityMeasure (ℕ × ℕ) (q.mspace.prod r.mspace)
      (@Measure.prod ℕ ℕ q.mspace r.mspace q.meas r.meas) := inferInstance
  refine ⟨assocRelabel',
    relabels_of_measurePreserving ((IsCompletionOf.self p).prod (IsCompletionOf.product q r))
      ?_ (Set.union_assoc _ _ _).symm.subset ?_⟩
  · have u1 := (measurePreserving_unpair (p ⊗ q) r).comp (measurePreserving_uncomplete (p ⊗ q) r)
    have u2 := MP.prod ((measurePreserving_unpair p q).comp (measurePreserving_uncomplete p q))
      (MP.id r.meas)
    have u3 := measurePreserving_prodAssoc' p q r
    have u4 := MP.prod (MP.id p.meas) (measurePreserving_pair q r)
    exact (measurePreserving_pairEquivOf _).comp (u4.comp (u3.comp (u2.comp u1)))
  · intro k _
    simp only [assocRelabel', product_state, Equiv.symm_apply_apply, Prod.map_fst, Prod.map_snd,
      Equiv.prodAssoc_apply, id_eq, Mem.union_assoc]
    exact le_refl _

/-! ### Projections and the unit -/

/-- A product carries at least the information of its left factor. -/
theorem le_product_left (p q : ProbSpace) : p ≤ (p ⊗ q) := by
  haveI := isProbabilityMeasure_meas q
  have hfst : MP (p.mspace.prod q.mspace) p.mspace Prod.fst
      (@Measure.prod ℕ ℕ p.mspace q.mspace p.meas q.meas) p.meas :=
    @measurePreserving_fst ℕ ℕ p.mspace q.mspace p.meas q.meas inferInstance inferInstance
  refine ⟨fun k ↦ (Nat.pairEquiv.symm k).1,
    relabels_of_measurePreserving (IsCompletionOf.self p) ?_ Set.subset_union_left ?_⟩
  · exact hfst.comp ((measurePreserving_unpair p q).comp (measurePreserving_uncomplete p q))
  · intro k _
    rw [product_state]
    exact Mem.le_union_left _ _

/-- A product carries at least the information of its right factor, provided the factors have
disjoint domains. -/
theorem le_product_right {p q : ProbSpace} (hd : Disjoint p.dom q.dom) : q ≤ (p ⊗ q) := by
  haveI := isProbabilityMeasure_meas p
  haveI := isProbabilityMeasure_meas q
  have hsnd : MP (p.mspace.prod q.mspace) q.mspace Prod.snd
      (@Measure.prod ℕ ℕ p.mspace q.mspace p.meas q.meas) q.meas :=
    @measurePreserving_snd ℕ ℕ p.mspace q.mspace p.meas q.meas inferInstance inferInstance
  refine ⟨fun k ↦ (Nat.pairEquiv.symm k).2,
    relabels_of_measurePreserving (IsCompletionOf.self q) ?_ Set.subset_union_right ?_⟩
  · exact hsnd.comp ((measurePreserving_unpair p q).comp (measurePreserving_uncomplete p q))
  · intro k _
    rw [product_state]
    exact Mem.le_union_right (by rw [p.dom_valid, q.dom_valid]; exact hd)

/-- The unit of the product: the space that knows nothing and owns no variables. -/
noncomputable def unit : ProbSpace where
  mspace := ⊤
  μ := ⟨@Measure.dirac ℕ ⊤ 0, @Measure.dirac.isProbabilityMeasure ℕ ⊤ 0⟩
  dom := ∅
  state _ := Mem.emp
  dom_valid _ := Mem.emp_dom
  complete := ⟨fun _ _ ↦ by trivial⟩

/-- Multiplying by the unit loses no information. -/
theorem product_unit_le (p : ProbSpace) : (unit ⊗ p) ≤ p := by
  haveI := isProbabilityMeasure_meas p
  have hmk : MP p.mspace (unit.mspace.prod p.mspace) (Prod.mk 0) p.meas
      (@Measure.prod ℕ ℕ unit.mspace p.mspace unit.meas p.meas) := by
    refine @MeasurePreserving.mk ℕ (ℕ × ℕ) p.mspace (unit.mspace.prod p.mspace) _ _ _
      (@measurable_prodMk_left ℕ ℕ unit.mspace p.mspace 0) ?_
    exact (@Measure.dirac_prod ℕ ℕ unit.mspace p.mspace p.meas inferInstance 0).symm
  refine ⟨fun i ↦ Nat.pairEquiv (0, i),
    relabels_of_measurePreserving (IsCompletionOf.product unit p)
      ((measurePreserving_pair unit p).comp hmk) (Set.empty_union _).subset ?_⟩
  intro i _
  rw [product_state, Equiv.symm_apply_apply]
  exact le_of_eq (Mem.emp_union _)

theorem le_unit_product (p : ProbSpace) : p ≤ (unit ⊗ p) :=
  le_product_right (Set.empty_disjoint _)

end ProbSpace

end Pcol
