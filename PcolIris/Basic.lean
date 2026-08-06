/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Authors: Noam Zilberstein
-/
import PcolIris.Logic.LemmaC6
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.Semantics.Invariant
import PcolIris.Semantics.Semantics
import PcolIris.OProp.OProp

namespace Pcol

def wp (𝓘 : Inv) (c : Cmd Act) (ψ : OProp) : OProp :=
  fun 𝓟 ↦
    ∀ (μ : Distr Mem) (𝓟fr : ProbSpace Mem),
      -- The initial distribution `μ` is a refinement of the precondition
      -- `𝓟`, the frame `𝓟fr`, and the invariant `𝓘`
      ((𝓟 ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.prop) ≼ μ) →
      -- Take any `ν` that results from running the program
      ∀ ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 (c.withInv 𝓘).to_pom,
      -- Then `ν` refines some probability space `𝓠`, which satisfies the postcondition `ψ`
        ∃ 𝓠, ((𝓠 ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.prop) ≼ ν) ∧ ψ 𝓠

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

lemma wp_if_true {𝓘 : Inv} {b : Expr} {c₁ c₂ : Cmd Act} {φ ψ : OProp}
    (hb : φ ⊢ OProp.sure fun σ ↦ b σ = some 1)
    (h : φ ⊢ wp 𝓘 c₁ ψ) :
    φ ⊢ wp 𝓘 (Cmd.if_stmt b c₁ c₂) ψ := by
  intro 𝓟 hφ μ 𝓟fr href ν hν; rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_if_stmt] at hν
  rcases ConvexPowerset.mem_bind.mp hν with ⟨ξ, hξ, f, hf, rfl⟩; clear hν
  obtain ⟨μ, rfl⟩ := PMF.to_distr_inv href.bot_0
  have heq : ξ = μ.to_distr := by sorry
  subst heq; clear hξ
  refine h 𝓟 hφ _ 𝓟fr href _ ?_
  refine ConvexPowerset.mem_bind.mpr ⟨_, ConvexPowerset.self_mem_singleton' _, f, ?_, rfl⟩
  simp only [Set.mem_pi, PMF.mem_support_iff, ne_eq]; intro σ hsupp
  cases σ with
  | bot =>
    exfalso; apply hsupp; rfl
  | coe σ =>
    simp only [Option.elim, Function.comp_apply]
    have hf := Set.mem_pi.mp hf _ hsupp; simp only [Option.elim, Function.comp_apply] at hf
    have heq :
        Linearization.Sem.sem (Test.lift b) σ =
        (pure Bool.true : ConvexPowerset Bool) := sorry
    simp only [heq, pure_bind, cond_true] at hf; exact hf

def Expr.equals (e₁ e₂ : Expr) : Mem → Prop :=
  fun σ ↦ (e₁ σ).isSome ∧ e₁ σ = e₂ σ
infixr:66 " == " => Expr.equals

-- This mostly follows from invariant monotonicity, but we need a few more properties about
-- assertions, etc
lemma wp_share {𝓘 : Inv} {c : Cmd Act} {ψ : OProp} :
    OProp.sure 𝓘.prop ∗ wp 𝓘 c ψ ⊢ wp Inv.emp c iprop(ψ ∗ OProp.sure 𝓘.prop) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hle, h𝓘, hwp⟩ μ 𝓟fr hre ν hν
  have hν' : ν ∈ ConvexPowerset.singleton' μ >>= Pom.lin (c.withInv 𝓘).to_pom := by
    refine le_iff_supset.mp ?_ hν
    apply ConvexPowerset.bind_monotone (le_refl _)
    apply (Pom.lin_continuous (act := WithInv Act) (test := Test)).monotone
    apply Cmd.withInv_monotone; refine ⟨Set.empty_subset _, ?_⟩
    intro σ; sorry
  have ⟨𝓠, hre', hψ⟩ := hwp μ 𝓟fr sorry ν sorry
  refine ⟨𝓠 ⊗ ProbSpace.trivial 𝓘.prop, ?_, ?_⟩
  · sorry
  · refine ⟨_, _, le_refl _, hψ, sorry⟩

/-- The parallel composition rule; see `PcolIris/Logic/WeakestPre.lean` for the same proof
in the refactored development. -/
lemma wp_par {𝓘 : Inv} {c₁ c₂ : Cmd Act} {ψ₁ ψ₂ : OProp}
    (hψ₁ : ψ₁.Precise) (hψ₂ : ψ₂.Precise) :
    wp 𝓘 c₁ ψ₁ ∗ wp 𝓘 c₂ ψ₂ ⊢ wp 𝓘 (c₁.par c₂) iprop(ψ₁ ∗ ψ₂) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hle, h₁, h₂⟩ μ 𝓟fr hre ν hν
  obtain ⟨𝓠₁, hQ₁⟩ := hψ₁
  obtain ⟨𝓠₂, hQ₂⟩ := hψ₂
  refine ⟨𝓠₁ ⊗ 𝓠₂, ?_,
    ⟨𝓠₁, 𝓠₂, le_refl _, (hQ₁ 𝓠₁).mp (le_refl _), (hQ₂ 𝓠₂).mp (le_refl _)⟩⟩
  have hμ : ((𝓟₁ ⊗ 𝓟₂ ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.prop) ≼ μ) :=
    Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left hle)) hre
  have hthread₁ : ∀ (𝓕 : ProbSpace Mem) (μ₁ : Distr Mem),
      ((𝓟₁ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.prop) ≼ μ₁) →
      ∀ ν₁ ∈ ConvexPowerset.singleton' μ₁ >>= 𝓛 (c₁.withInv 𝓘).to_pom,
        ((𝓠₁ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.prop) ≼ ν₁) := by
    intro 𝓕 μ₁ hre₁ ν₁ hν₁
    obtain ⟨𝓠, href, hψ⟩ := h₁ μ₁ 𝓕 hre₁ ν₁ hν₁
    exact Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left ((hQ₁ 𝓠).mpr hψ))) href
  have hthread₂ : ∀ (𝓕 : ProbSpace Mem) (μ₂ : Distr Mem),
      ((𝓟₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.prop) ≼ μ₂) →
      ∀ ν₂ ∈ ConvexPowerset.singleton' μ₂ >>= 𝓛 (c₂.withInv 𝓘).to_pom,
        ((𝓠₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.prop) ≼ ν₂) := by
    intro 𝓕 μ₂ hre₂ ν₂ hν₂
    obtain ⟨𝓠, href, hψ⟩ := h₂ μ₂ 𝓕 hre₂ ν₂ hν₂
    exact Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left ((hQ₂ 𝓠).mpr hψ))) href
  rw [Cmd.withInv, Cmd.to_pom] at hν
  exact fun {_} hE ↦ lemma_C6 hμ hthread₁ hthread₂ ν hν hE

lemma wp_assign {𝓘 : Inv} (x : Var) (e : Expr) (ψ : OProp) (v : Val) :
  (OProp.sure ($ x == Expr.literal v) ∗ (OProp.sure ($ x == (fun σ ↦ e (σ.extend x v))) -∗ ψ)) ⊢
  wp 𝓘 (x ::= e) ψ := sorry

lemma example_proof :
    (OProp.sure <| $"x" == 0) ⊢ wp Inv.emp ("x" ::= $"x" + 1) (OProp.sure <| $"x" == 1) := by
  iintro h
  iapply wp_assign _ _ _ 0
  iframe; iintro h; sorry


end Pcol
