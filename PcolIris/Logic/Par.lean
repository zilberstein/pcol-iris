import ConvexPowerset.MinProb
import Pom.Operations.Par

import PcolIris.Semantics.Invariant

namespace Lpofin

open Pcol

variable {act test : Type}

def HasInv (α : Lpofin (Label (WithInv act) test)) (𝓘 : Inv) : Prop :=
  ∀ x ∈ α.nodes, match α.lab x with
  | Label.act a => a.inv = 𝓘
  | _ => true

noncomputable def par {x : Node} {α β : Lpofin (Label act test)}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes) :
    Lpofin (Label act test) :=
  ⟨Lpo.par hx hx' hd Label.fork_ne_bot,
    Set.finite_insert.mpr (Set.finite_union.mpr ⟨α.property, β.property⟩)⟩

end Lpofin

namespace Pcol

open Linearization

variable
  {α β : Lpofin (Label (WithInv Act) Test)}
  {root : Node} (hr₁ : root ∉ α.nodes) (hr₂ : root ∉ β.nodes)
  {𝓘 : Inv}
  (hdn : Disjoint α.nodes β.nodes)
  (A B : Set Mem)

def Mem.sep (A B : Set Mem) : Set Mem :=
    { σ | ∃ σ₁ ∈ A, ∃ σ₂ ∈ B, σ = σ₁.union σ₂ }

-- Lemma C.3 from POPL'26
theorem par_comp_fin
    {σ₁ : Mem} {σ₂ : Mem} {τ τ₁ τ₂ : Mem} {𝓘 : Inv}
    (hτ : 𝓘.prop τ) (hτ₁ : 𝓘.prop τ₁) (hτ₂ : 𝓘.prop τ₂)
    (hinv₁ : α.HasInv 𝓘) (hinv₂ : β.HasInv 𝓘)
    (hd₁ : Disjoint τ.dom σ₁.dom) (hd₂ : Disjoint τ.dom σ₂.dom)
    (hd : Disjoint σ₁.dom σ₂.dom) :
    ConvexPowerset.minProb
      (Lpofin.lin
        (Lpofin.par hr₁ hr₂ hdn)
        (σ₁.union (σ₂.union τ)))
      (Mem.sep A (Mem.sep B 𝓘.prop)) ≥
      ConvexPowerset.minProb (Lpofin.lin α (σ₁.union τ₁)) (Mem.sep A 𝓘.prop) *
      ConvexPowerset.minProb (Lpofin.lin β (σ₂.union τ₂)) (Mem.sep B 𝓘.prop) := by
  sorry

end Pcol
