import PcolIris.OProp.OProp
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.OProp.SumProd

namespace Pcol

namespace ProbSpace

/-- Enlarging a probability space can only shrink its support: a smaller space has fewer
measurable sets, hence fewer sets of full measure to intersect. -/
lemma support_anti {p q : ProbSpace} (h : p ≤ q) : q.support ⊆ p.support := by
  intro n hn
  rw [ProbSpace.support_eq]
  intro E hE
  obtain ⟨hEm, hE1⟩ := hE
  refine ProbSpace.support_subset (h.mspace E hEm) ?_ hn
  rw [← ProbSpace.μ_eq_one_iff] at hE1 ⊢
  rw [← h.μ E hEm]; exact hE1

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
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, hP, hQ⟩ n hn
  have hn' : n ∈ (𝓟₁ ⊗ 𝓟₂).support := ProbSpace.support_anti hle hn
  obtain ⟨h1, h2⟩ := ProbSpace.mem_support_product_iff.mp hn'
  have hst : (𝓟₁ ⊗ 𝓟₂).state n ≤ 𝓟.state n := hle.state n
  exact ⟨P.upcl ((ProbSpace.state_le_product_left 𝓟₁ 𝓟₂ n).trans hst) (hP h1),
    Q.upcl ((ProbSpace.state_le_product_right hdisj n).trans hst) (hQ h2)⟩

lemma sure_weaken {P Q : MProp} (h : P ⊢ Q) : ⌈P⌉ ⊢ ⌈Q⌉ := by
  intro 𝓟 hP i hi; apply Set.mem_preimage.mpr
  exact hP hi |> Set.mem_preimage.mp |> h _

lemma sure_sep {P Q : MProp} :
    ⌈ iprop(P ∗ Q) ⌉ ⊣⊢ ⌈P⌉ ∗ ⌈Q⌉ := by
  constructor
  · intro 𝓟 hsure; sorry
  · intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, hP, hQ⟩ k hk
    sorry

lemma oplus_distrib {ι : Type} (ξ : PMF ι) (φ : ι → OProp) (ψ : OProp) :
    (⨁[ ξ ] φ) ∗ ψ ⊢ ⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ) := sorry

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

namespace Precise

lemma sure (P : MProp) : (OProp.sure P).Precise := sorry

lemma sep {φ ψ : OProp} (hφ : φ.Precise) (hψ : ψ.Precise) : iprop(φ ∗ ψ).Precise := by sorry

lemma oplus {ι : Type} {ξ : PMF ι} {φ : ι → OProp} (h : ∀ v ∈ ξ.support, (φ v).Precise) :
    (⨁[ξ] φ).Precise := by sorry

end Precise

end Pcol
