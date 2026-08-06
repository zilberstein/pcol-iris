import ConvexPowerset.MinProb
import DomainTheory.OmegaCompletePartialOrder.Instances
import Pom.Operations.Par

import PcolIris.Logic.ParComp
import PcolIris.Semantics.Invariant

namespace Pcol

open Linearization

namespace Pom

def ThreadLocal (p : Pom (Label (WithInv Act) Test)) (V : Set Var) (𝓘 : Inv) : Prop :=
  ∀ α ∈ p, Pcol.ThreadLocal α V 𝓘

namespace ThreadLocal

lemma to_lpo_trunc {p : Pom (Label (WithInv Act) Test)} {α : Lpo (Label (WithInv Act) Test)} {n : ℕ}
    {V : Set Var} {𝓘 : Inv}
    (h : ThreadLocal p V 𝓘) (hmem : α ∈ p) : Pcol.ThreadLocal (α.trunc n) V 𝓘 := by
  intro x ⟨hx, _⟩; by_cases hlev : α.rel.lev x < n
  · conv => arg 2; exact if_pos hlev
    exact h α hmem x hx
  · conv => arg 2; exact if_neg hlev
    trivial

end ThreadLocal

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
    {σ₁ : Mem} {σ₂ : Mem} {τ τ₁ τ₂ : Mem} {𝓘 : Inv} {A B : Set Mem}
    (hτ : 𝓘.prop τ) (hτ₁ : 𝓘.prop τ₁) (hτ₂ : 𝓘.prop τ₂)
    (p q : Pom (Label (WithInv Act) Test))
    (hinv₁ : p.HasInv 𝓘) (hinv₂ : q.HasInv 𝓘)
    (hloc₁ : Pom.ThreadLocal p σ₁.dom 𝓘) (hloc₂ : Pom.ThreadLocal q σ₂.dom 𝓘)
    (hA : ∀ σ ∈ A, Mem.dom σ = σ₁.dom) (hB : ∀ σ ∈ B, Mem.dom σ = σ₂.dom)
    (hd₁ : Disjoint τ.dom σ₁.dom) (hd₂ : Disjoint τ.dom σ₂.dom)
    (hd : Disjoint σ₁.dom σ₂.dom) :
    ConvexPowerset.minProb
      (𝓛 (Pom.Semantics.par p q) (σ₁.union (σ₂.union τ)))
      (Mem.sep A (Mem.sep B 𝓘.prop)) ≥
    ConvexPowerset.minProb (𝓛 p (σ₁.union τ₁)) (Mem.sep A 𝓘.prop) *
    ConvexPowerset.minProb (𝓛 q (σ₂.union τ₂)) (Mem.sep B 𝓘.prop) := by
  -- Get a canonical Lpo representation of the parallel composition
  obtain ⟨α, β, x, hx, hx', hdn, rfl, rfl, hmem⟩ := Pom.exists_rep_par Label.fork_ne_bot p q
  -- Rewrite the linearizations in terms of suprema of finite Lpos
  unfold Pom.Semantics.par; rw [hmem, Pom.lin_mk, Pom.lin_mk, Pom.lin_mk]
  -- Convert the truncation of parallel compositions into a parallel composition of truncations
  rw [Chain.ωSup_shift]; simp only [Chain.shift, DFunLike.coe]
  conv in Lpo.trunc _ _ => exact par_trunc _
  -- Apply Scott Continuity of `minProb` to move the suprema to the outside
  conv => lhs; exact (ConvexPowerset.minProb_ωScottContinuous _).map_ωSup _
  conv => rhs; lhs; exact (ConvexPowerset.minProb_ωScottContinuous _).map_ωSup _
  conv => rhs; rhs; exact (ConvexPowerset.minProb_ωScottContinuous _).map_ωSup _
  conv => rhs; exact ωSup_mul _ _
  -- Apply `Lpofin.par_comp` for each level in the chains
  refine ωSup_le_ωSup_of_le fun n ↦ ⟨n, ?_⟩
  refine par_comp_fin_local
    (hinv₁.to_lpo_trunc rfl)
    (hinv₂.to_lpo_trunc rfl)
    (hloc₁.to_lpo_trunc rfl)
    (hloc₂.to_lpo_trunc rfl)
    hA hB hτ hτ₁ hτ₂ hd₁ hd₂ hd

end Pom

end Pcol
