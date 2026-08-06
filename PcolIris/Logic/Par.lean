import ConvexPowerset.MinProb
import DomainTheory.OmegaCompletePartialOrder.Instances
import Pom.Operations.Par

import PcolIris.Semantics.Invariant

namespace Lpo

open Pcol

def HasInv {act test : Type} (α : Lpo (Label (WithInv act) test)) (𝓘 : Inv) : Prop :=
  ∀ x ∈ α.nodes, match α.lab x with
  | Label.act a => a.inv = 𝓘
  | _ => true

end Lpo

namespace Lpofin

open Pcol

variable {act test : Type}

def HasInv (α : Lpofin (Label (WithInv act) test)) (𝓘 : Inv) : Prop :=
  α.val.HasInv 𝓘

noncomputable def par {x : Node} {α β : Lpofin (Label act test)}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes) :
    Lpofin (Label act test) :=
  ⟨Lpo.par hx hx' hd Label.fork_ne_bot,
    Set.finite_insert.mpr (Set.finite_union.mpr ⟨α.property, β.property⟩)⟩

end Lpofin

namespace Pom

open Pcol

variable {act test : Type}

def HasInv (p : Pom (Label (WithInv act) test)) (𝓘 : Inv) : Prop :=
  ∀ α ∈ p, α.HasInv 𝓘

namespace HasInv

lemma to_lpo_trunc {p : Pom (Label (WithInv act) test)} {α : Lpo (Label (WithInv act) test)}
    {𝓘 : Inv} (h : p.HasInv 𝓘) (hmem : α ∈ p) {n : ℕ} :
    (α.trunc n).HasInv 𝓘 := by
  intro x ⟨hx, _⟩; by_cases hlev : α.rel.lev x < n
  · conv => arg 2; exact if_pos hlev
    exact h α hmem x hx
  · conv => arg 2; exact if_neg hlev

end HasInv

end Pom

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

namespace Lpofin

-- Lemma C.3 from POPL'26
theorem par_comp
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

end Lpofin

namespace Pom

open OmegaCompletePartialOrder

lemma par_trunc {x : Node} {α β : Lpo (Label (WithInv Act) Test)}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes} {hd : Disjoint α.nodes β.nodes}
    (n : ℕ) :
    (Lpo.par hx hx' hd Label.fork_ne_bot).trunc (n + 1) =
    Lpofin.par
      (fun h ↦ hx <| (α.trunc_le n).nodes h)
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes) := Subtype.ext <| Lpo.par_trunc n

lemma ωSup_mul (f g : Chain ENNReal) :
    ωSup f * ωSup g = ωSup {
      toFun n := f n * g n
      monotone' := sorry
     } := by sorry

theorem par_comp
    {σ₁ : Mem} {σ₂ : Mem} {τ τ₁ τ₂ : Mem} {𝓘 : Inv}
    (hτ : 𝓘.prop τ) (hτ₁ : 𝓘.prop τ₁) (hτ₂ : 𝓘.prop τ₂)
    (p q : Pom (Label (WithInv Act) Test))
    (hinv₁ : p.HasInv 𝓘) (hinv₂ : q.HasInv 𝓘)
    (hd₁ : Disjoint τ.dom σ₁.dom) (hd₂ : Disjoint τ.dom σ₂.dom)
    (hd : Disjoint σ₁.dom σ₂.dom) :
    ConvexPowerset.minProb
      (Pom.lin (Pom.Semantics.par p q) (σ₁.union (σ₂.union τ)))
      (Mem.sep A (Mem.sep B 𝓘.prop)) ≥
      ConvexPowerset.minProb (Pom.lin p (σ₁.union τ₁)) (Mem.sep A 𝓘.prop) *
      ConvexPowerset.minProb (Pom.lin q (σ₂.union τ₂)) (Mem.sep B 𝓘.prop) := by
  obtain ⟨α, β, x, hx, hx', hdn, rfl, rfl, hmem⟩ := Pom.exists_rep_par Label.fork_ne_bot p q
  unfold Pom.Semantics.par; rw [hmem, Pom.lin_mk, Pom.lin_mk, Pom.lin_mk]
  rw [Chain.ωSup_shift]; simp only [Chain.shift, DFunLike.coe]
  conv in Lpo.trunc _ _ => exact par_trunc _
  conv => lhs; exact (ConvexPowerset.minProb_ωScottContinuous _).map_ωSup _
  conv => rhs; lhs; exact (ConvexPowerset.minProb_ωScottContinuous _).map_ωSup _
  conv => rhs; rhs; exact (ConvexPowerset.minProb_ωScottContinuous _).map_ωSup _
  conv => rhs; exact ωSup_mul _ _
  refine ωSup_le_ωSup_of_le fun n ↦ ⟨n, ?_⟩
  exact Lpofin.par_comp _ _ _ A B hτ hτ₁ hτ₂
    (hinv₁.to_lpo_trunc rfl)
    (hinv₂.to_lpo_trunc rfl)
    hd₁ hd₂ hd


end Pom

end Pcol
