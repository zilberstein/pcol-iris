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

end Framed

end Pcol
