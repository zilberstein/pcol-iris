/-
Distributions that refine a precondition together with a frame and the invariant.

This is the shape of the assumption on the initial distribution, and of the guarantee on the
final distribution, in the definition of the weakest precondition (Definition 5.1 of the
paper).
-/
import PcolIris.OProp.OProp
import PcolIris.OProp.ProductLaws
import PcolIris.Semantics.Invariant

namespace Pcol

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

end Framed

end Pcol
