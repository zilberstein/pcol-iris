import PcolIris.OProp.OProp
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.OProp.ProductLaws
import PcolIris.OProp.TrivialSpace
import PcolIris.OProp.SumLaws

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

lemma sep {P Q : MProp} {V W : Set Var} (hP : P.Footprint V) (hQ : Q.Footprint W) :
    iprop(P ∗ Q).Footprint (V ∪ W) := by
  intro σ
  constructor
  · rintro ⟨σ₁, σ₂, hd, hle, h₁, h₂⟩
    have hle₁ : σ₁ ≤ σ := (Mem.le_union_left σ₁ σ₂).trans hle
    have hle₂ : σ₂ ≤ σ := (Mem.le_union_right hd).trans hle
    refine ⟨Set.union_subset (((hP σ₁).mp h₁).1.trans (Mem.dom_mono hle₁))
      (((hQ σ₂).mp h₂).1.trans (Mem.dom_mono hle₂)),
      σ₁.restrict V, σ₂.restrict W, ?_, ?_, ((hP σ₁).mp h₁).2, ((hQ σ₂).mp h₂).2⟩
    · exact hd.mono (Mem.dom_mono (Mem.restrict_le σ₁ V)) (Mem.dom_mono (Mem.restrict_le σ₂ W))
    · refine Mem.union_le (Mem.le_restrict ((Mem.restrict_le σ₁ V).trans hle₁) ?_)
        (Mem.le_restrict ((Mem.restrict_le σ₂ W).trans hle₂) ?_)
      · exact (Mem.dom_restrict_subset σ₁ V).trans Set.subset_union_left
      · exact (Mem.dom_restrict_subset σ₂ W).trans Set.subset_union_right
  · rintro ⟨-, h⟩
    exact iprop(P ∗ Q).upcl (Mem.restrict_le σ (V ∪ W)) h

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

/-- A certainty about a separating conjunction can be split into independent certainties, when
the two assertions talk about fixed sets of variables: the two parts are the spaces without
probabilistic information over those variables. -/
lemma sure_sep_elim {P Q : MProp} {V W : Set Var} (hP : P.Footprint V) (hQ : Q.Footprint W) :
    ⌈ iprop(P ∗ Q) ⌉ ⊢ iprop(⌈P⌉ ∗ ⌈Q⌉) := by
  intro 𝓟 h
  -- The components of a memory satisfying `P ∗ Q` satisfy `P` and `Q`
  have hsplit : ∀ k ∈ 𝓟.support, P (𝓟.state k) ∧ Q (𝓟.state k) := by
    intro k hk
    obtain ⟨σ₁, σ₂, hd, hle, h₁, h₂⟩ := h hk
    exact ⟨P.upcl ((Mem.le_union_left σ₁ σ₂).trans hle) h₁,
      Q.upcl ((Mem.le_union_right hd).trans hle) h₂⟩
  obtain ⟨k₀, hk₀⟩ := ProbSpace.support_nonempty 𝓟
  obtain ⟨σ₁, σ₂, hd, hle, h₁, h₂⟩ := h hk₀
  have hV : V ⊆ 𝓟.dom := by
    rw [← 𝓟.dom_valid k₀]; exact ((hP _).mp (hsplit k₀ hk₀).1).1
  have hW : W ⊆ 𝓟.dom := by
    rw [← 𝓟.dom_valid k₀]; exact ((hQ _).mp (hsplit k₀ hk₀).2).1
  have hVW : Disjoint V W := hd.mono ((hP _).mp h₁).1 ((hQ _).mp h₂).1
  refine ⟨ProbSpace.forget 𝓟 V hV, ProbSpace.forget 𝓟 W hW, hVW,
    ProbSpace.product_forget_le (ProbSpace.forget_le 𝓟 hV) hW, fun k _ ↦ ?_, fun k _ ↦ ?_⟩
  · obtain ⟨k', hk', heq⟩ := ProbSpace.forget_state_restrict 𝓟 hV k
    change P ((ProbSpace.forget 𝓟 V hV).state k)
    rw [heq]; exact ((hP _).mp (hsplit k' hk').1).2
  · obtain ⟨k', hk', heq⟩ := ProbSpace.forget_state_restrict 𝓟 hW k
    change Q ((ProbSpace.forget 𝓟 W hW).state k)
    rw [heq]; exact ((hQ _).mp (hsplit k' hk').2).2

/-- An almost sure assertion with footprint `V` holds of the part of the space over `V`. -/
lemma sure_forget {P : MProp} {V : Set Var} (hP : P.Footprint V) {𝓟 : ProbSpace}
    (h : sure P 𝓟) : ∃ hV : V ⊆ 𝓟.dom, sure P (ProbSpace.forget 𝓟 V hV) := by
  obtain ⟨k₀, hk₀⟩ := ProbSpace.support_nonempty 𝓟
  have hV : V ⊆ 𝓟.dom := by rw [← 𝓟.dom_valid k₀]; exact ((hP _).mp (h hk₀)).1
  refine ⟨hV, fun k _ ↦ ?_⟩
  obtain ⟨k', hk', heq⟩ := ProbSpace.forget_state_restrict 𝓟 hV k
  change P ((ProbSpace.forget 𝓟 V hV).state k)
  rw [heq]; exact ((hP _).mp (h hk')).2

lemma sure_sep {P Q : MProp} {V W : Set Var} (hP : P.Footprint V) (hQ : Q.Footprint W) :
    ⌈ iprop(P ∗ Q) ⌉ ⊣⊢ ⌈P⌉ ∗ ⌈Q⌉ :=
  ⟨sure_sep_elim hP hQ, sure_sep_intro⟩

/-- A frame can be pushed into the branches of an outcome conjunction. -/
lemma oplus_distrib {ι : Type} [Countable ι] (ξ : PMF ι) (φ : ι → OProp) (ψ : OProp) :
    (⨁[ ξ ] φ) ∗ ψ ⊢ ⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ) := by
  rintro 𝓟 ⟨m₁, m₂, hd, hle, ⟨𝓠, V, hdsj, hdom, hsum, hφ⟩, hψ⟩
  have hV : V ⊆ m₁.dom := ProbSpace.dom_mono hsum
  refine ⟨fun v ↦ 𝓠 v ⊗ m₂, V ∪ m₂.dom, ProbSpace.sum_prod_disjoint m₂ hdsj,
    ProbSpace.sum_prod_dom m₂ hdom, ?_, fun v hv ↦ ?_⟩
  · exact (ProbSpace.sumProd_le_sum_product ξ 𝓠 m₂ V hdsj hdom).trans
      ((ProbSpace.product_mono_left hsum hd).trans hle)
  · exact ⟨𝓠 v, m₂, (hdom v).symm ▸ hd.mono_left hV, le_refl _, hφ v hv, hψ⟩

/-- A precise frame can be pulled out of the branches of an outcome conjunction.  The frame
is satisfied by the same (least) space in every branch, and the rest of each branch, completed
by the variables it does not constrain, is independent of it. -/
lemma oplus_distrib' {ι : Type} [Countable ι] (ξ : PMF ι) (φ : ι → OProp) (ψ : OProp)
    (h : ψ.Precise) : (⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ)) ⊢ (⨁[ ξ ] φ) ∗ ψ := by
  classical
  rintro 𝓟 ⟨𝓡, W, hdsj, hdom, hsum, hφψ⟩
  obtain ⟨v₀, hv₀⟩ := ξ.support_nonempty
  choose m₁ m₂ hd hle h₁ h₂ using hφψ
  obtain ⟨𝓠, hQ⟩ := h _ (h₂ v₀ hv₀)
  have hQle : ∀ v (hv : v ∈ ξ.support), 𝓠 ≤ m₂ v hv := fun v hv ↦ (hQ _).mpr (h₂ v hv)
  have hsubW : ∀ v (hv : v ∈ ξ.support), (m₁ v hv).dom ∪ (m₂ v hv).dom ⊆ W := fun v hv ↦ by
    rw [← hdom v]; exact ProbSpace.dom_mono (hle v hv)
  have hQW : 𝓠.dom ⊆ W :=
    (ProbSpace.dom_mono (hQle v₀ hv₀)).trans (Set.subset_union_right.trans (hsubW v₀ hv₀))
  set D := W \ 𝓠.dom with hD
  have hm₁Q : ∀ v (hv : v ∈ ξ.support), Disjoint (m₁ v hv).dom 𝓠.dom :=
    fun v hv ↦ (hd v hv).mono_right (ProbSpace.dom_mono (hQle v hv))
  have hm₁D : ∀ v (hv : v ∈ ξ.support), (m₁ v hv).dom ⊆ D := fun v hv x hx ↦
    ⟨Set.subset_union_left.trans (hsubW v hv) hx, Set.disjoint_left.mp (hm₁Q v hv) hx⟩
  have hDR : ∀ v, D \ ∅ ⊆ (𝓡 v).dom := fun v ↦ by
    rw [hdom v, Set.diff_empty]; exact Set.diff_subset
  -- In each branch, the part of the space that does not belong to the frame
  let A : ∀ v, v ∈ ξ.support → ProbSpace := fun v hv ↦
    m₁ v hv ⊗ ProbSpace.forget (𝓡 v) (D \ (m₁ v hv).dom)
      ((Set.diff_subset_diff_right (Set.empty_subset _)).trans (hDR v))
  have hAdom : ∀ v hv, (A v hv).dom = D := fun v hv ↦ Set.union_diff_cancel (hm₁D v hv)
  have hAφ : ∀ v hv, φ v (A v hv) := fun v hv ↦
    (φ v).mono (ProbSpace.le_product_left _ _) (h₁ v hv)
  have hAQ : ∀ v hv, (A v hv ⊗ 𝓠) ≤ 𝓡 v := by
    intro v hv
    have hF : Disjoint 𝓠.dom (D \ (m₁ v hv).dom) :=
      Set.disjoint_left.mpr fun x hx hx' ↦ hx'.1.2 hx
    refine (ProbSpace.product_swap_right hF ?_).trans ?_
    · exact Set.disjoint_union_right.mpr ⟨hm₁Q v hv,
        Set.disjoint_left.mpr fun x hx hx' ↦ hx'.2 hx⟩
    · exact ProbSpace.product_forget_le
        ((ProbSpace.product_mono_right (hQle v hv) (hm₁Q v hv)).trans (hle v hv)) _
  let A' : ι → ProbSpace := fun v ↦ if hv : v ∈ ξ.support then A v hv else A v₀ hv₀
  have hA'dom : ∀ v, (A' v).dom = D := fun v ↦ by
    simp only [A']; split_ifs with hv
    · exact hAdom v hv
    · exact hAdom v₀ hv₀
  obtain ⟨code, hcode⟩ := Countable.exists_injective_nat ι
  let S : ι → ProbSpace := fun v ↦ (A' v).shift (code v)
  have hSdisj : ∀ {i j : ι}, i ≠ j → Disjoint (S i).support (S j).support :=
    fun hij ↦ ProbSpace.disjoint_support_shift _ _ (hcode.ne hij)
  have hSdom : ∀ v, (S v).dom = D := hA'dom
  refine ⟨ProbSpace.sum ξ S D hSdisj hSdom, 𝓠, Set.disjoint_sdiff_left, ?_,
    ⟨S, D, hSdisj, hSdom, le_refl _, fun v hv ↦ ?_⟩, (hQ 𝓠).mp (le_refl _)⟩
  · refine (ProbSpace.sum_product_le_sumProd ξ S 𝓠 D hSdisj hSdom).trans
      ((ProbSpace.sum_mono (ProbSpace.sum_prod_disjoint 𝓠 hSdisj) hdsj
        (ProbSpace.sum_prod_dom 𝓠 hSdom) hdom (Set.union_subset Set.diff_subset hQW)
        fun v hv ↦ ?_).trans hsum)
    have hv' : v ∈ ξ.support := (PMF.mem_support_iff _ _).mpr hv
    have hA' : A' v = A v hv' := dif_pos hv'
    refine (ProbSpace.product_mono_left (ProbSpace.shift_le _ _) ?_).trans ?_
    · rw [hA'dom]; exact Set.disjoint_sdiff_left
    · rw [hA']; exact hAQ v hv'
  · have hA' : A' v = A v hv := dif_pos hv
    exact (φ v).mono (ProbSpace.le_shift _ _) (hA' ▸ hAφ v hv)

lemma oplus_weaken {ξ : PMF Val} {φ ψ : Val → OProp} (h : ∀ v ∈ ξ.support, φ v ⊢ ψ v) :
    (⨁[ξ] φ) ⊢ ⨁[ξ] ψ := by
  intro 𝓟 ⟨𝓠, V, hdsj, hdom, hsum, hφ⟩
  refine ⟨𝓠, V, hdsj, hdom, hsum, ?_⟩
  intro v hv; exact h v hv (𝓠 v) <| hφ v hv

/-- `oplus_weaken`, for an arbitrary index type. -/
lemma oplus_weaken' {ι : Type} [Countable ι] {ξ : PMF ι} {φ ψ : ι → OProp}
    (h : ∀ v ∈ ξ.support, φ v ⊢ ψ v) : (⨁[ξ] φ) ⊢ ⨁[ξ] ψ := by
  intro 𝓟 ⟨𝓠, V, hdsj, hdom, hsum, hφ⟩
  exact ⟨𝓠, V, hdsj, hdom, hsum, fun v hv ↦ h v hv (𝓠 v) (hφ v hv)⟩

/-- Nondeterministic choice is monotone. -/
lemma nondet_weaken {ι : Type} [Countable ι] {φ ψ : ι → OProp} (h : ∀ i, φ i ⊢ ψ i) : (& φ) ⊢ & ψ := by
  rintro 𝓟 ⟨ξ, hξ⟩
  exact ⟨ξ, oplus_weaken' (fun v _ ↦ h v) 𝓟 hξ⟩

/-- A frame can be pushed into the branches of a nondeterministic choice. -/
lemma nondet_distrib {ι : Type} [Countable ι] (φ : ι → OProp) (ψ : OProp) :
    iprop((& φ) ∗ ψ) ⊢ & fun v ↦ iprop(φ v ∗ ψ) := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, ⟨ξ, hξ⟩, hψ⟩
  exact ⟨ξ, oplus_distrib ξ φ ψ 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, hξ, hψ⟩⟩

/-- A precise frame can be pulled out of the branches of a nondeterministic choice. -/
lemma nondet_distrib' {ι : Type} [Countable ι] (φ : ι → OProp) (ψ : OProp) (h : ψ.Precise) :
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
lemma oplus_collapse {ι : Type} [Countable ι] {ξ : PMF ι} {ψ : OProp} (h : ψ.Precise) :
    (⨁[ξ] fun _ ↦ ψ) ⊢ ψ := by
  refine Iris.BI.Entails.trans (oplus_weaken' (φ := fun _ ↦ ψ)
    (ψ := fun _ ↦ iprop(Iris.BI.BIBase.emp ∗ ψ)) (fun _ _ ↦ Iris.BI.emp_sep.2)) ?_
  exact Iris.BI.Entails.trans (oplus_distrib' ξ (fun _ ↦ iprop(Iris.BI.BIBase.emp)) ψ h)
    Iris.BI.sep_elim_right

/-- A precise assertion is closed under nondeterministic mixtures. -/
lemma nondet_collapse {ι : Type} [Countable ι] {ψ : OProp} (h : ψ.Precise) : nondet (fun (_ : ι) => ψ) ⊢ ψ := by
  rintro 𝓟 ⟨ξ, hξ⟩
  exact oplus_collapse h 𝓟 hξ

/--
Reindexing a probabilistic sum along a bijection of the index type that preserves the
distribution.
-/
lemma oplus_reindex {ι : Type} [Countable ι] {ξ : PMF ι} (e : ι ≃ ι) (hξ : ∀ i, ξ (e i) = ξ i)
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


namespace Precise

/-- An almost sure assertion is precise, provided that the pure assertion only talks about a
fixed finite set of variables (in the paper, `⌈P⌉` is interpreted over
the variables of `P`).  Its least model records which memories over those variables are
possible, but no probabilities. -/
lemma sureDom {P : MProp} {V : Set Var} (hP : P.Footprint V) (hV : V.Finite) :
    (OProp.sure P).PreciseDom V := by
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
  refine ⟨ProbSpace.trivialOn V f (fun i ↦ (hfS i).1), rfl, fun 𝓠 ↦ ⟨?_, fun h ↦ ?_⟩⟩
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

lemma sure {P : MProp} {V : Set Var} (hP : P.Footprint V) (hV : V.Finite) :
    (OProp.sure P).Precise :=
  (sureDom hP hV).precise

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

/-- Outcome conjunctions of precise assertions owning the same variables are precise: the
least model is the sum of the least models of the branches (moved to disjoint outcomes).
Thanks to the indexed model, no partitioning side condition is needed. -/
lemma oplusDom {ι : Type} [Countable ι] {ξ : PMF ι} {φ : ι → OProp} {V : Set Var}
    (h : ∀ v ∈ ξ.support, (φ v).PreciseDom V) : (⨁[ξ] φ).PreciseDom V := by
  classical
  rintro 𝓠 ⟨𝓡, W, -, -, -, hφ⟩
  obtain ⟨v₀, hv₀⟩ := ξ.support_nonempty
  have hmin : ∀ v ∈ ξ.support, ∃ 𝓟 : ProbSpace, 𝓟.dom = V ∧ ∀ 𝓠', 𝓟 ≤ 𝓠' ↔ φ v 𝓠' :=
    fun v hv ↦ h v hv _ (hφ v hv)
  let P : ι → ProbSpace := fun v ↦
    if hv : v ∈ ξ.support then (hmin v hv).choose else (hmin v₀ hv₀).choose
  have hPdom : ∀ v, (P v).dom = V := by
    intro v; simp only [P]; split_ifs with hv
    · exact (hmin v hv).choose_spec.1
    · exact (hmin v₀ hv₀).choose_spec.1
  have hPmin : ∀ v ∈ ξ.support, ∀ 𝓠', P v ≤ 𝓠' ↔ φ v 𝓠' := by
    intro v hv; simp only [P, dif_pos hv]; exact (hmin v hv).choose_spec.2
  obtain ⟨code, hcode⟩ := Countable.exists_injective_nat ι
  let S : ι → ProbSpace := fun v ↦ (P v).shift (code v)
  have hSdisj : ∀ {i j : ι}, i ≠ j → Disjoint (S i).support (S j).support :=
    fun hij ↦ ProbSpace.disjoint_support_shift _ _ (hcode.ne hij)
  have hSdom : ∀ v, (S v).dom = V := hPdom
  refine ⟨ProbSpace.sum ξ S V hSdisj hSdom, rfl, fun 𝓠' ↦ ⟨fun hle ↦ ?_, ?_⟩⟩
  · refine ⟨S, V, hSdisj, hSdom, hle, fun v hv ↦ ?_⟩
    exact (hPmin v hv (S v)).mp (ProbSpace.le_shift _ _)
  · rintro ⟨𝓡', W', hdisj', hdom', hsum', hφ'⟩
    have hVW : V ⊆ W' := by
      rw [← hPdom v₀, ← hdom' v₀]
      exact ProbSpace.dom_mono ((hPmin v₀ hv₀ _).mpr (hφ' v₀ hv₀))
    refine (ProbSpace.sum_mono hSdisj hdisj' hSdom hdom' hVW fun v hv ↦ ?_).trans hsum'
    exact (ProbSpace.shift_le _ _).trans ((hPmin v (PMF.mem_support_iff _ _ |>.mpr hv) _).mpr
      (hφ' v (PMF.mem_support_iff _ _ |>.mpr hv)))

end Precise

end Pcol
