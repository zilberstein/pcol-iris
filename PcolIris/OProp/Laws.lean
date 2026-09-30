import PcolIris.OProp.OProp
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.OProp.ProductLaws
import PcolIris.OProp.TrivialSpace

namespace Pcol

namespace ProbSpace

/-- The distributive law of products over sums, as a pair of inequalities. -/
lemma sumProd_le_sum_product {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (𝓠 : ProbSpace)
    (V : Set Var) (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    (hdom : ∀ i : ι, (𝓟 i).dom = V) :
    sumProd ξ 𝓟 𝓠 V h hdom ≤ (sum ξ 𝓟 V h hdom ⊗ 𝓠) := by
  obtain ⟨hms, hmeas, hd, hsupp, hst⟩ := sum_prod_distribute ξ 𝓟 𝓠 V h hdom
  refine le_of_id (fun E hE ↦ hms ▸ hE) (fun E _ ↦ ?_) hd.symm.subset
    (fun k hk ↦ le_of_eq (hst k hk).symm)
  refine ENNReal.coe_injective ?_
  rw [prob_coe, prob_coe]
  exact (hmeas E).symm

lemma sum_product_le_sumProd {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (𝓠 : ProbSpace)
    (V : Set Var) (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    (hdom : ∀ i : ι, (𝓟 i).dom = V) :
    (sum ξ 𝓟 V h hdom ⊗ 𝓠) ≤ sumProd ξ 𝓟 𝓠 V h hdom := by
  obtain ⟨hms, hmeas, hd, hsupp, hst⟩ := sum_prod_distribute ξ 𝓟 𝓠 V h hdom
  refine le_of_id (fun E hE ↦ hms.symm ▸ hE) (fun E _ ↦ ?_) hd.subset
    (fun k hk ↦ le_of_eq (hst k (hsupp ▸ hk)))
  refine ENNReal.coe_injective ?_
  rw [prob_coe, prob_coe]
  exact hmeas E

/-- The left factor of a product is contained in the product state. -/
lemma state_le_product_left (p q : ProbSpace) (n : ℕ) :
    p.state (Nat.pairEquiv.symm n).1 ≤ (p ⊗ q).state n := by
  intro x; rw [ProbSpace.product_state]
  cases hx : p.state (Nat.pairEquiv.symm n).1 x with
  | none => trivial
  | some v => rw [Mem.union_apply_of_mem_dom (Mem.mem_dom_iff.mpr (by rw [hx]; simp)), hx]

/-- The right factor of a product with disjoint domains is contained in the product state. -/
lemma state_le_product_right {p q : ProbSpace} (hdisj : Disjoint p.dom q.dom) (n : ℕ) :
    q.state (Nat.pairEquiv.symm n).2 ≤ (p ⊗ q).state n := by
  intro x; rw [ProbSpace.product_state]
  cases hx : q.state (Nat.pairEquiv.symm n).2 x with
  | none => trivial
  | some v =>
    have hxd : x ∈ q.dom := by
      rw [← q.dom_valid (Nat.pairEquiv.symm n).2, Mem.mem_dom_iff, hx]; simp
    have hnd : x ∉ Mem.dom (p.state (Nat.pairEquiv.symm n).1) := by
      rw [p.dom_valid]
      exact fun hc ↦ Set.disjoint_left.mp hdisj hc hxd
    rw [Mem.union_apply_of_notMem_dom hnd, hx]

end ProbSpace

namespace OProp

/--
Two separately owned certainties can be combined into a certainty about their conjunction.

(The converse fails in general: splitting a probability space into two independent factors
is not always possible.)
-/
lemma sure_and {P Q : MProp} : iprop(⌈P⌉ ∗ ⌈Q⌉) ⊢ ⌈P ∧ Q⌉ := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, ⟨g, hg⟩, hP, hQ⟩ n hn
  obtain ⟨h1, h2⟩ := ProbSpace.mem_support_product_iff.mp (hg.mem_support hn)
  have hst : (𝓟₁ ⊗ 𝓟₂).state (g n) ≤ 𝓟.state n := hg.state n hn
  exact ⟨P.upcl ((ProbSpace.state_le_product_left 𝓟₁ 𝓟₂ (g n)).trans hst) (hP h1),
    Q.upcl ((ProbSpace.state_le_product_right hdisj (g n)).trans hst) (hQ h2)⟩

lemma sure_weaken {P Q : MProp} (h : P ⊢ Q) : ⌈P⌉ ⊢ ⌈Q⌉ := by
  intro 𝓟 hP i hi; apply Set.mem_preimage.mpr
  exact hP hi |> Set.mem_preimage.mp |> h _

/-- Two separately owned certainties give a certainty about their separating conjunction. -/
lemma sure_sep_intro {P Q : MProp} : iprop(⌈P⌉ ∗ ⌈Q⌉) ⊢ ⌈ iprop(P ∗ Q) ⌉ := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, ⟨g, hg⟩, hP, hQ⟩ n hn
  obtain ⟨h1, h2⟩ := ProbSpace.mem_support_product_iff.mp (hg.mem_support hn)
  refine ⟨_, _, ?_, ?_, hP h1, hQ h2⟩
  · rw [𝓟₁.dom_valid, 𝓟₂.dom_valid]; exact hdisj
  · have := hg.state n hn
    rwa [ProbSpace.product_state] at this

lemma sure_sep {P Q : MProp} :
    ⌈ iprop(P ∗ Q) ⌉ ⊣⊢ ⌈P⌉ ∗ ⌈Q⌉ := by
  constructor
  · intro 𝓟 hsure; sorry
  · exact sure_sep_intro

/-- A frame can be pushed into the branches of an outcome conjunction. -/
lemma oplus_distrib {ι : Type} (ξ : PMF ι) (φ : ι → OProp) (ψ : OProp) :
    (⨁[ ξ ] φ) ∗ ψ ⊢ ⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ) := by
  rintro 𝓟 ⟨m₁, m₂, hd, hle, ⟨𝓠, V, hdsj, hdom, hsum, hφ⟩, hψ⟩
  have hV : V ⊆ m₁.dom := ProbSpace.dom_mono hsum
  refine ⟨fun v ↦ 𝓠 v ⊗ m₂, V ∪ m₂.dom, ProbSpace.sum_prod_disjoint m₂ hdsj,
    ProbSpace.sum_prod_dom m₂ hdom, ?_, fun v hv ↦ ?_⟩
  · exact (ProbSpace.sumProd_le_sum_product ξ 𝓠 m₂ V hdsj hdom).trans
      ((ProbSpace.product_mono_left hsum hd).trans hle)
  · exact ⟨𝓠 v, m₂, (hdom v).symm ▸ hd.mono_left hV, le_refl _, hφ v hv, hψ⟩

lemma oplus_distrib' {ι : Type} (ξ : PMF ι) (φ : ι → OProp) (ψ : OProp) (h : ψ.Precise) :
    (⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ)) ⊢ (⨁[ ξ ] φ) ∗ ψ := by
  sorry

lemma oplus_weaken {ξ : PMF Val} {φ ψ : Val → OProp} (h : ∀ v ∈ ξ.support, φ v ⊢ ψ v) :
    (⨁[ξ] φ) ⊢ ⨁[ξ] ψ := by
  intro 𝓟 ⟨𝓠, V, hdsj, hdom, hsum, hφ⟩
  refine ⟨𝓠, V, hdsj, hdom, hsum, ?_⟩
  intro v hv; exact h v hv (𝓠 v) <| hφ v hv

/-- `oplus_weaken`, for an arbitrary index type. -/
lemma oplus_weaken' {ι : Type} {ξ : PMF ι} {φ ψ : ι → OProp}
    (h : ∀ v ∈ ξ.support, φ v ⊢ ψ v) : (⨁[ξ] φ) ⊢ ⨁[ξ] ψ := by
  intro 𝓟 ⟨𝓠, V, hdsj, hdom, hsum, hφ⟩
  exact ⟨𝓠, V, hdsj, hdom, hsum, fun v hv ↦ h v hv (𝓠 v) (hφ v hv)⟩

/-- Nondeterministic choice is monotone. -/
lemma nondet_weaken {ι : Type} {φ ψ : ι → OProp} (h : ∀ i, φ i ⊢ ψ i) : (& φ) ⊢ & ψ := by
  rintro 𝓟 ⟨ξ, hξ⟩
  exact ⟨ξ, oplus_weaken' (fun v _ ↦ h v) 𝓟 hξ⟩

/-- A frame can be pushed into the branches of a nondeterministic choice. -/
lemma nondet_distrib {ι : Type} (φ : ι → OProp) (ψ : OProp) :
    iprop((& φ) ∗ ψ) ⊢ & fun v ↦ iprop(φ v ∗ ψ) := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, ⟨ξ, hξ⟩, hψ⟩
  exact ⟨ξ, oplus_distrib ξ φ ψ 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, hξ, hψ⟩⟩

/-- A precise frame can be pulled out of the branches of a nondeterministic choice. -/
lemma nondet_distrib' {ι : Type} (φ : ι → OProp) (ψ : OProp) (h : ψ.Precise) :
    (& fun v ↦ iprop(φ v ∗ ψ)) ⊢ iprop((& φ) ∗ ψ) := by
  rintro 𝓟 ⟨ξ, hξ⟩
  obtain ⟨𝓟₁, 𝓟₂, hdisj, hle, h₁, h₂⟩ := oplus_distrib' ξ φ ψ h 𝓟 hξ
  exact ⟨𝓟₁, 𝓟₂, hdisj, hle, ⟨ξ, h₁⟩, h₂⟩

/--
A precise assertion is closed under probabilistic mixtures: if every summand of a
probabilistic sum satisfies the precise assertion `ψ`, then so does the sum itself.

This is the special case of `oplus_distrib'` where the family is the unit of the separating
conjunction.
-/
lemma oplus_collapse {ι : Type} {ξ : PMF ι} {ψ : OProp} (h : ψ.Precise) :
    (⨁[ξ] fun _ ↦ ψ) ⊢ ψ := by
  refine Iris.BI.Entails.trans (oplus_weaken' (φ := fun _ ↦ ψ)
    (ψ := fun _ ↦ iprop(Iris.BI.BIBase.emp ∗ ψ)) (fun _ _ ↦ Iris.BI.emp_sep.2)) ?_
  exact Iris.BI.Entails.trans (oplus_distrib' ξ (fun _ ↦ iprop(Iris.BI.BIBase.emp)) ψ h)
    Iris.BI.sep_elim_right

/-- A precise assertion is closed under nondeterministic mixtures. -/
lemma nondet_collapse {ι : Type} {ψ : OProp} (h : ψ.Precise) : nondet (fun (_ : ι) => ψ) ⊢ ψ := by
  rintro 𝓟 ⟨ξ, hξ⟩
  exact oplus_collapse h 𝓟 hξ

/--
Reindexing a probabilistic sum along a bijection of the index type that preserves the
distribution.
-/
lemma oplus_reindex {ι : Type} {ξ : PMF ι} (e : ι ≃ ι) (hξ : ∀ i, ξ (e i) = ξ i)
    (φ : ι → OProp) : (⨁[ξ] fun v ↦ φ (e v)) ⊢ ⨁[ξ] φ := by
  rintro 𝓟 ⟨𝓠, V, hdsj, hdom, hsum, hφ⟩
  refine ⟨fun w ↦ 𝓠 (e.symm w), V, ?_, fun i ↦ hdom _, ?_, ?_⟩
  · intro i j hij
    exact hdsj (fun hc ↦ hij (by rw [← e.apply_symm_apply i, hc, e.apply_symm_apply]))
  · exact le_trans (ProbSpace.sum_reindex_le ξ e hξ 𝓠 V hdsj hdom _ _) hsum
  · intro w hw
    have hmem : e.symm w ∈ ξ.support := by
      rw [PMF.mem_support_iff, ← hξ (e.symm w), e.apply_symm_apply]
      exact PMF.mem_support_iff _ _ |>.mp hw
    have hh : φ (e (e.symm w)) (𝓠 (e.symm w)) := hφ (e.symm w) hmem
    rwa [e.apply_symm_apply] at hh

end OProp

namespace MProp

/-- The pure assertion `P` only talks about the variables `V`: it requires them to be
allocated, and only depends on their values. -/
def Footprint (P : MProp) (V : Set Var) : Prop :=
  ∀ σ, P σ ↔ V ⊆ σ.dom ∧ P (σ.restrict V)

namespace Footprint

lemma emp : (Iris.BI.BIBase.emp : MProp).Footprint ∅ :=
  fun _ ↦ ⟨fun _ ↦ ⟨Set.empty_subset _, trivial⟩, fun _ ↦ trivial⟩

lemma var_equals_literal (x : Var) (v : Val) : ($ x == Expr.literal v).Footprint {x} := by
  intro σ
  rw [Expr.var_equals_literal_iff, Expr.var_equals_literal_iff,
    Mem.restrict_apply_of_mem _ (Set.mem_singleton x)]
  exact ⟨fun h ↦ ⟨Set.singleton_subset_iff.mpr (Mem.mem_dom_of_eq_some h), h⟩, fun h ↦ h.2⟩

lemma own_var (x : Var) : (own ($ x)).Footprint {x} := by
  intro σ
  rw [own_var_iff, own_var_iff, Mem.restrict_apply_of_mem _ (Set.mem_singleton x)]
  refine ⟨fun h ↦ ⟨Set.singleton_subset_iff.mpr ?_, h⟩, fun h ↦ h.2⟩
  exact Mem.mem_dom_iff.mpr (Option.isSome_iff_ne_none.mp h)

/-- An equation between an expression and a literal only talks about the variables that the
expression reads. -/
lemma equals_literal {e : Expr} {V : Set Var} (hmono : Expr.Mono e)
    (hread : ∀ σ, e σ = e (σ.restrict V)) (hdef : ∀ σ, (e σ).isSome → V ⊆ σ.dom) (c : Val) :
    (e == Expr.literal c).Footprint V := by
  intro σ
  rw [Expr.equals_iff hmono (Expr.literal_mono c), Expr.equals_iff hmono (Expr.literal_mono c),
    ← hread σ]
  exact ⟨fun h ↦ ⟨hdef σ h.1, h⟩, fun h ↦ h.2⟩

lemma and {P Q : MProp} {V W : Set Var} (hP : P.Footprint V) (hQ : Q.Footprint W) :
    iprop(P ∧ Q).Footprint (V ∪ W) := by
  intro σ
  change P σ ∧ Q σ ↔ V ∪ W ⊆ σ.dom ∧ (P (σ.restrict (V ∪ W)) ∧ Q (σ.restrict (V ∪ W)))
  rw [hP σ, hQ σ, hP (σ.restrict (V ∪ W)), hQ (σ.restrict (V ∪ W)), Mem.restrict_restrict,
    Mem.restrict_restrict, Mem.restrict_dom,
    Set.inter_eq_right.mpr (Set.subset_union_left : V ⊆ V ∪ W),
    Set.inter_eq_right.mpr (Set.subset_union_right : W ⊆ V ∪ W)]
  simp only [Set.union_subset_iff, Set.subset_inter_iff]
  tauto

end Footprint

end MProp

namespace Precise

/-- An almost sure assertion is precise, provided that the pure assertion only talks about a
fixed finite set of variables (in the paper, `⌈P⌉` is interpreted over
the variables of `P`).  Its least model records which memories over those variables are
possible, but no probabilities. -/
lemma sure {P : MProp} {V : Set Var} (hP : P.Footprint V) (hV : V.Finite) :
    (OProp.sure P).Precise := by
  classical
  intro 𝓠₀ h₀
  have hsat : ∃ σ, P σ := by
    obtain ⟨k, hk⟩ := ProbSpace.support_nonempty 𝓠₀
    exact ⟨_, h₀ hk⟩
  let S : Set Mem := {τ | τ.dom = V ∧ P τ}
  have hcount : S.Countable := by
    haveI : Finite V := hV.to_subtype
    refine Set.Countable.mono (s₂ := {τ : Mem | τ.dom = V}) (fun τ h ↦ h.1) ?_
    have hinj : Function.Injective
        (fun (τ : {τ : Mem | τ.dom = V}) ↦ fun (x : V) ↦ τ.val x) := by
      intro τ τ' h; apply Subtype.ext; funext x
      by_cases hx : x ∈ V
      · exact congrFun h ⟨x, hx⟩
      · have h₁ : x ∉ τ.val.dom := by rw [τ.2]; exact hx
        have h₂ : x ∉ τ'.val.dom := by rw [τ'.2]; exact hx
        rw [Mem.notMem_dom_iff.mp h₁, Mem.notMem_dom_iff.mp h₂]
    exact Set.countable_coe_iff.mp hinj.countable
  obtain ⟨σ, hσ⟩ := hsat
  have hσS : σ.restrict V ∈ S :=
    ⟨by rw [Mem.restrict_dom]; exact Set.inter_eq_right.mpr ((hP σ).mp hσ).1,
      ((hP σ).mp hσ).2⟩
  obtain ⟨f, hf⟩ := hcount.exists_eq_range ⟨_, hσS⟩
  have hfS : ∀ i, f i ∈ S := fun i ↦ hf ▸ Set.mem_range_self i
  refine ⟨ProbSpace.trivialOn V f (fun i ↦ (hfS i).1), fun 𝓠 ↦ ⟨?_, fun h ↦ ?_⟩⟩
  · rintro ⟨g, hg⟩ k hk
    exact P.upcl (hg.state k hk) (hfS (g k)).2
  · obtain ⟨k0, hk0⟩ := ProbSpace.support_nonempty 𝓠
    have hdom : V ⊆ 𝓠.dom := by
      rw [← 𝓠.dom_valid k0]; exact ((hP _).mp (h hk0)).1
    have hmem : ∀ i ∈ 𝓠.support, (𝓠.state i).restrict V ∈ Set.range f := by
      intro i hi
      rw [← hf]
      refine ⟨?_, ((hP _).mp (h hi)).2⟩
      rw [Mem.restrict_dom, 𝓠.dom_valid]; exact Set.inter_eq_right.mpr hdom
    let g : ℕ → ℕ := fun i ↦ if hi : i ∈ 𝓠.support then (hmem i hi).choose else 0
    refine ProbSpace.trivialOn_le hdom g (fun i hi ↦ ?_)
    simp only [g, dif_pos hi]
    rw [(hmem i hi).choose_spec]
    exact Mem.restrict_le _ _

/-- Separating conjunctions of precise assertions are precise: the least model is the product
of the least models. -/
lemma sep {φ ψ : OProp} (hφ : φ.Precise) (hψ : ψ.Precise) : iprop(φ ∗ ψ).Precise := by
  rintro 𝓠 ⟨m₁, m₂, hd, -, h₁, h₂⟩
  obtain ⟨𝓟₁, hP₁⟩ := hφ m₁ h₁
  obtain ⟨𝓟₂, hP₂⟩ := hψ m₂ h₂
  have hd' : Disjoint 𝓟₁.dom 𝓟₂.dom :=
    (hd.mono_left (ProbSpace.dom_mono ((hP₁ m₁).mpr h₁))).mono_right
      (ProbSpace.dom_mono ((hP₂ m₂).mpr h₂))
  refine ⟨𝓟₁ ⊗ 𝓟₂, fun 𝓠' ↦ ⟨fun hle ↦ ?_, ?_⟩⟩
  · exact ⟨𝓟₁, 𝓟₂, hd', hle, (hP₁ 𝓟₁).mp (le_refl _), (hP₂ 𝓟₂).mp (le_refl _)⟩
  · rintro ⟨n₁, n₂, hdn, hle, hn₁, hn₂⟩
    exact (ProbSpace.product_mono ((hP₁ n₁).mpr hn₁) ((hP₂ n₂).mpr hn₂)
      (hdn.mono_right (ProbSpace.dom_mono ((hP₂ n₂).mpr hn₂)))).trans hle

lemma oplus {ι : Type} {ξ : PMF ι} {φ : ι → OProp} (h : ∀ v ∈ ξ.support, (φ v).Precise) :
    (⨁[ξ] φ).Precise := by sorry

end Precise

end Pcol
