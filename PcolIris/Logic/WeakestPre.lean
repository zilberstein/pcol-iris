import PcolIris.Logic.Par
import PcolIris.Logic.LemmaC6
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.Semantics.Invariant
import PcolIris.Semantics.Semantics
import PcolIris.OProp.OProp

namespace Pcol

def wp (𝓘 : Inv) (c : Cmd Act) (ψ : OProp) : OProp :=
  fun 𝓟 ↦
    ∀ (μ : Distr Mem) (𝓟fr : ProbSpace),
      -- The initial distribution `μ` is a refinement of the precondition
      -- `𝓟`, the frame `𝓟fr`, and the invariant `𝓘`
      ((𝓟 ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ) →
      -- Take any `ν` that results from running the program
      ∀ ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 (c.withInv 𝓘).to_pom,
      -- Then `ν` refines some probability space `𝓠`, which satisfies the postcondition `ψ`
        ∃ 𝓠, ((𝓠 ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν) ∧ ψ 𝓠

notation 𝓘 " ⊢{{" φ "}} " c " {{" ψ "}}" => φ ⊢ wp 𝓘 c ψ

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

lemma wp_atom {𝓘 : Inv} {a : Act} {ψ : OProp} :
    (OProp.sure 𝓘.to_MProp -∗ wp Inv.emp (Cmd.act a) (iprop(ψ ∗ OProp.sure 𝓘.to_MProp)))
    ⊢ wp 𝓘 (Cmd.act a) ψ := by
  sorry

lemma wp_assign {𝓘 : Inv} (x : Var) (e : Expr) (ψ : OProp) (v : Val) :
  (OProp.sure ($ x == Expr.literal v) ∗ (OProp.sure ($ x == (fun σ ↦ e (σ.extend x v))) -∗ ψ)) ⊢
  wp 𝓘 (x ::= e) ψ := sorry

lemma wp_assign' {𝓘 : Inv} (x : Var) (e : Expr) {ψ : OProp} :
  (OProp.sure (MProp.own ($ x))) ∗ (OProp.sure ($ x == e) -∗ ψ) ⊢
  wp 𝓘 (x ::= e) ψ := sorry

/-- **The parallel composition rule.**  If the postconditions `ψ₁` and `ψ₂` are precise, then
the weakest preconditions of two threads can be combined with the separating conjunction.

The proof follows the `Par` case of the soundness theorem of the pcOL paper: precision
provides least probability spaces `𝓠₁` and `𝓠₂` satisfying the two postconditions, each
thread is shown to take any frame-respecting refinement of its precondition to a refinement
of `𝓠ₖ`, and the two threads are then combined by `lemma_C6`. -/
lemma wp_par {𝓘 : Inv} {c₁ c₂ : Cmd Act} {ψ₁ ψ₂ : OProp}
    (hψ₁ : ψ₁.Precise) (hψ₂ : ψ₂.Precise) :
    wp 𝓘 c₁ ψ₁ ∗ wp 𝓘 c₂ ψ₂ ⊢ wp 𝓘 (c₁.par c₂) iprop(ψ₁ ∗ ψ₂) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h₁, h₂⟩ μ 𝓟fr hre ν hν
  -- `𝓠₁` and `𝓠₂` are the least probability spaces satisfying `ψ₁` and `ψ₂`
  obtain ⟨𝓠₁, hQ₁⟩ := hψ₁
  obtain ⟨𝓠₂, hQ₂⟩ := hψ₂
  -- We need to somehow prove that `𝓠₁.dom ⊆ 𝓟₁.dom` in order to establish disjointness
  -- of the postconditions
  refine ⟨𝓠₁ ⊗ 𝓠₂, ?_,
    ⟨𝓠₁, 𝓠₂, sorry, le_refl _, (hQ₁ 𝓠₁).mp (le_refl _), (hQ₂ 𝓠₂).mp (le_refl _)⟩⟩
  -- The initial distribution refines the two preconditions, the frame and the invariant
  have hμ : ((𝓟₁ ⊗ 𝓟₂ ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ) :=
    Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left hle)) hre
  -- Each thread, run in isolation with an arbitrary frame, establishes its postcondition;
  -- by precision, the least such postcondition space is `𝓠ₖ`
  have hthread₁ : ∀ (𝓕 : ProbSpace) (μ₁ : Distr Mem),
      ((𝓟₁ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ₁) →
      ∀ ν₁ ∈ ConvexPowerset.singleton' μ₁ >>= 𝓛 (c₁.withInv 𝓘).to_pom,
        ((𝓠₁ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν₁) := by
    intro 𝓕 μ₁ hre₁ ν₁ hν₁
    obtain ⟨𝓠, href, hψ⟩ := h₁ μ₁ 𝓕 hre₁ ν₁ hν₁
    exact Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left ((hQ₁ 𝓠).mpr hψ))) href
  have hthread₂ : ∀ (𝓕 : ProbSpace) (μ₂ : Distr Mem),
      ((𝓟₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ₂) →
      ∀ ν₂ ∈ ConvexPowerset.singleton' μ₂ >>= 𝓛 (c₂.withInv 𝓘).to_pom,
        ((𝓠₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν₂) := by
    intro 𝓕 μ₂ hre₂ ν₂ hν₂
    obtain ⟨𝓠, href, hψ⟩ := h₂ μ₂ 𝓕 hre₂ ν₂ hν₂
    exact Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left ((hQ₂ 𝓠).mpr hψ))) href
  -- The parallel composition is handled by Lemma C.6
  rw [Cmd.withInv, Cmd.to_pom] at hν
  exact lemma_C6 hμ hthread₁ hthread₂ ν hν

lemma wp_split {𝓘 : Inv} {c : Cmd Act} {ξ : PMF Val} {ψ : Val → OProp} :
    (⨁[ ξ ] fun v ↦ wp 𝓘 c (ψ v)) ⊢ wp 𝓘 c (⨁[ ξ ] ψ) := by
  intro 𝓟 ⟨𝓟', V, hdsj, hdom, hsum, hwp⟩ μ 𝓟fr hre ν hν
  obtain ⟨k, rfl, hk⟩ :
      ∃ k,
        μ = ξ.bind k ∧
        ∀ v ∈ ξ.support, (𝓟' v ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ k v :=
    sorry
  obtain ⟨ξ', _, f, hf, rfl⟩ := ConvexPowerset.mem_bind.mp hν
  have : ξ' = ξ.bind k := sorry; subst this
  have h v hv := hwp v hv (k v) 𝓟fr (hk v hv) ((k v).bind f) sorry
  choose 𝓠 h𝓠 using h
  classical
  let 𝓠' v := if h : v ∈ ξ.support then 𝓠 v h else ProbSpace.trivial Iris.BI.BIBase.emp
  -- Also need to permute indices to make the `𝓠'`s disjoint
  refine ⟨ProbSpace.sum ξ 𝓠' V sorry sorry, ?_, ?_⟩
  · sorry
  · refine ⟨𝓠', V, sorry, sorry, le_refl _, ?_⟩
    intro v hv; unfold 𝓠'; rw [dif_pos hv]
    exact h𝓠 v hv |>.2

end Pcol
