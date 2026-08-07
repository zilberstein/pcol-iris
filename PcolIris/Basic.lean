/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Authors: Noam Zilberstein
-/
import PcolIris.Logic.WeakestPre
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.Semantics.Invariant
import PcolIris.Semantics.Semantics
import PcolIris.OProp.OProp

namespace Pcol

lemma wp_weaken {𝓘 : Inv} {c : Cmd Act} {φ ψ : OProp}
    (h : φ ⊢ ψ) : wp 𝓘 c φ ⊢ wp 𝓘 c ψ := by
  intro 𝓟 hc μ 𝓟fr hre ν hν
  have ⟨𝓠, hre', hφ⟩ := hc μ 𝓟fr hre ν hν
  refine ⟨𝓠, hre', ?_⟩; exact h 𝓠 hφ

lemma wp_skip {𝓘 : Inv} (c : Cmd Act) (φ : OProp) :
    φ ⊣⊢ wp 𝓘 Cmd.skip φ := by
  constructor
  · intro 𝓟 hφ μ 𝓟fr hre ν hν
    refine ⟨𝓟, ?_, hφ⟩
    rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_skip, bind_pure] at hν
    obtain ⟨μ, rfl⟩ := PMF.to_distr_inv hre.bot_0
    have heq : ν = μ.to_distr := sorry
    rwa [heq]
  · intro 𝓟 hφ; sorry

lemma wp_seq {𝓘 : Inv} {c₁ c₂ : Cmd Act} {ψ : OProp} :
    wp 𝓘 c₁ (wp 𝓘 c₂ ψ) ⊢ wp 𝓘 (Cmd.seq c₁ c₂) ψ := by
  intro 𝓟 h μ 𝓟fr href ν; rw [Cmd.withInv, Cmd.to_pom, Pom.lin_seq, ← bind_assoc]
  intro hν; rcases ConvexPowerset.mem_bind.mp hν with ⟨ξ, hξ, f, hf, rfl⟩
  have ⟨𝓡, href', h'⟩ := h μ 𝓟fr href ξ hξ
  refine h' ξ 𝓟fr href' _ ?_
  exact ConvexPowerset.mem_bind.mpr ⟨ξ, ConvexPowerset.self_mem_singleton' _, f, hf, rfl⟩

def Expr.equals (e₁ e₂ : Expr) : MProp := {
  prop σ := (e₁ σ).isSome ∧ e₁ σ = e₂ σ
  upcl := sorry
}
infixr:66 " == " => Expr.equals

lemma wp_if_true {𝓘 : Inv} {b : Expr} {c₁ c₂ : Cmd Act} {φ ψ : OProp} :
     ⌈b == Expr.literal 1⌉ ∧ wp 𝓘 c₁ ψ ⊢ wp 𝓘 (Cmd.if_stmt b c₁ c₂) ψ := by
  intro 𝓟 ⟨htrue, hwp⟩ μ 𝓟fr href ν hν; rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_if_stmt] at hν
  sorry

-- This mostly follows from invariant monotonicity, but we need a few more properties about
-- assertions, etc
lemma wp_share {𝓘 : Inv} {c : Cmd Act} {ψ : OProp} :
    OProp.sure 𝓘.to_MProp ∗ wp 𝓘 c ψ ⊢ wp Inv.emp c iprop(ψ ∗ OProp.sure 𝓘.to_MProp) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h𝓘, hwp⟩ μ 𝓟fr hre ν hν
  have hν' : ν ∈ ConvexPowerset.singleton' μ >>= Pom.lin (c.withInv 𝓘).to_pom := by
    refine le_iff_supset.mp ?_ hν
    apply ConvexPowerset.bind_monotone (le_refl _)
    apply (Pom.lin_continuous (act := WithInv Act) (test := Test)).monotone
    apply Cmd.withInv_monotone; refine ⟨Set.empty_subset _, ?_⟩
    intro σ; sorry
  have ⟨𝓠, hre', hψ⟩ := hwp μ 𝓟fr sorry ν sorry
  refine ⟨𝓠 ⊗ ProbSpace.trivial 𝓘.to_MProp, ?_, ?_⟩
  · sorry
  · refine ⟨_, _, ?_, le_refl _, hψ, ?_⟩
    · -- Need some lemmas about domain being contractive after `wp`
      sorry
    · -- This should also be a lemma
      sorry

lemma wp_assign {𝓘 : Inv} (x : Var) (e : Expr) (ψ : OProp) (v : Val) :
  (OProp.sure ($ x == Expr.literal v) ∗ (OProp.sure ($ x == (fun σ ↦ e (σ.extend x v))) -∗ ψ)) ⊢
  wp 𝓘 (x ::= e) ψ := sorry

lemma example_proof :
    (OProp.sure <| $"x" == 0) ⊢ wp Inv.emp ("x" ::= $"x" + 1) (OProp.sure <| $"x" == 1) := by
  iintro h
  iapply wp_assign _ _ _ 0
  iframe; iintro h; sorry


end Pcol
