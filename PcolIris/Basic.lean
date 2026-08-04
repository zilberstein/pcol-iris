/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Authors: Noam Zilberstein
-/
import PcolIris.Semantics.Semantics
import PcolIris.OProp.OProp

namespace Pcol

def wp (c : Cmd) (ψ : OProp) : OProp :=
  fun 𝓟 ↦
    ∀ (μ : Distr Mem) (𝓟fr : ProbSpace Mem),
      (𝓟.product 𝓟fr ≼ μ) →
      ∀ ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 c.to_pom,
        ∃ 𝓠, (𝓠.product 𝓟fr ≼ ν) ∧ ψ 𝓠

lemma ConvexPowerset.mem_bind {α β : Type} {s : ConvexPowerset α}
    {k : α → ConvexPowerset β} {ν : Distr β} :
    ν ∈ s >>= k ↔
    ∃ μ ∈ s,
      ∃ f ∈ μ.support.pi fun x ↦ Option.elim x Set.univ (ConvexPowerset.set ∘ k),
        ν = μ.bind f := by
  constructor
  · rintro ⟨⟨ξ, f⟩, ⟨_, ⟨_, rfl⟩, _, ⟨hξ, rfl⟩, rfl, hf⟩, rfl⟩
    refine ⟨ξ, hξ, f, hf, ?_⟩; rfl
  · rintro ⟨ξ, hξ, f, hf, rfl⟩; refine ⟨⟨ξ, f⟩, ?_⟩
    simp only [Set.mem_iUnion, exists_prop, Function.uncurry_apply_pair]
    exact ⟨⟨ξ, hξ, Set.mem_singleton _, hf⟩, True.intro⟩

lemma wp_skip (c : Cmd) (φ : OProp) :
    φ ⊣⊢ wp Cmd.skip φ := by
  constructor
  · intro 𝓟 hφ μ 𝓟fr hre ν hν
    refine ⟨𝓟, ?_, hφ⟩
    rw [Cmd.to_pom, Pom.Semantics.lin_skip, bind_pure] at hν
    obtain ⟨μ, rfl⟩ := PMF.to_distr_inv hre.bot_0
    have heq : ν = μ.to_distr := sorry
    rwa [heq]
  · intro 𝓟 hφ; sorry

lemma wp_seq {c₁ c₂ : Cmd} {φ ψ ϑ : OProp}
    (h₁ : φ ⊢ wp c₁ ψ) (h₂ : ψ ⊢ wp c₂ ϑ) :
    φ ⊢ wp (Cmd.seq c₁ c₂) ϑ := by
  intro 𝓟 hφ μ 𝓟fr href ν; rw [Cmd.to_pom, Pom.lin_seq, ← bind_assoc]
  intro hν; rcases ConvexPowerset.mem_bind.mp hν with ⟨ξ, hξ, f, hf, rfl⟩
  have ⟨𝓡, href', hψ⟩ := h₁ 𝓟 hφ μ 𝓟fr href ξ hξ
  refine h₂ 𝓡 hψ ξ 𝓟fr href' _ ?_
  exact ConvexPowerset.mem_bind.mpr ⟨ξ, ConvexPowerset.self_mem_singleton' _, f, hf, rfl⟩

lemma wp_if_true {b : Expr} {c₁ c₂ : Cmd} {φ ψ : OProp}
    (hb : φ ⊢ OProp.sure fun σ ↦ b σ = some 1)
    (h : φ ⊢ wp c₁ ψ) :
    φ ⊢ wp (Cmd.if_stmt b c₁ c₂) ψ := by
  intro 𝓟 hφ μ 𝓟fr href ν hν; rw [Cmd.to_pom, Pom.Semantics.lin_if_stmt] at hν
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


end Pcol
