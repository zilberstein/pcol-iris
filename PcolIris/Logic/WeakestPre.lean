import PcolIris.Logic.Par
import PcolIris.Logic.LemmaC6
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.OProp.Laws
import PcolIris.Semantics.Invariant
import PcolIris.Semantics.Semantics
import PcolIris.OProp.OProp

namespace Pcol

open MProp

def wp_base (𝓘 : Inv) (F : ProbSpace → Prop) (c : Cmd Act) (ψ : OProp) : OProp :=
  fun 𝓟 ↦
    ∀ (μ : Distr Mem) (𝓟fr : ProbSpace),
      -- The frame validity predicate holds
      F 𝓟fr →
      -- The initial distribution `μ` is a refinement of the precondition
      -- `𝓟`, the frame `𝓟fr`, and the invariant `𝓘`
      ((𝓟 ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ) →
      -- Take any `ν` that results from running the program
      ∀ ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 (c.withInv 𝓘).to_pom,
      -- Then `ν` refines some probability space `𝓠`, which satisfies the postcondition `ψ`
        ∃ 𝓠, ((𝓠 ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν) ∧ ψ 𝓠

/-- The standard "strong" wp allows any frame -/
def wp (𝓘 : Inv) : Cmd Act → OProp → OProp := wp_base 𝓘 (fun _ ↦ True)

/-- The "weak" wp only preserves frames for trivial probability spaces,
where every event has probability exactly 0 or 1 -/
def wp_weak (𝓘 : Inv) : Cmd Act → OProp → OProp := wp_base 𝓘 fun 𝓟fr ↦
  ∀ E, 𝓟fr.mspace.MeasurableSet' E → 𝓟fr.μ E = 0 ∨ 𝓟fr.μ E = 1

notation 𝓘 " ⊢{{" φ "}} " c " {{" ψ "}}" => φ ⊢ wp 𝓘 c ψ

/- BASIC COMMAND RULES -/

variable {𝓘 : Inv} {F : ProbSpace → Prop} {c : Cmd Act}

lemma wp_skip (φ : OProp) :
    φ ⊣⊢ wp_base 𝓘 F Cmd.skip φ := by
  constructor
  · intro 𝓟 hφ μ 𝓟fr _ hre ν hν
    refine ⟨𝓟, ?_, hφ⟩
    rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_skip, bind_pure] at hν
    obtain ⟨μ, rfl⟩ := PMF.to_distr_inv hre.bot_0
    have heq : ν = μ.to_distr := sorry
    rwa [heq]
  · intro 𝓟 hφ; sorry

lemma wp_seq {c₁ c₂ : Cmd Act} {ψ : OProp} :
    wp_base 𝓘 F c₁ (wp_base 𝓘 F c₂ ψ) ⊢ wp_base 𝓘 F (Cmd.seq c₁ c₂) ψ := by
  intro 𝓟 h μ 𝓟fr hF href ν; rw [Cmd.withInv, Cmd.to_pom, Pom.lin_seq, ← bind_assoc]
  intro hν; rcases ConvexPowerset.mem_bind.mp hν with ⟨ξ, hξ, f, hf, rfl⟩
  have ⟨𝓡, href', h'⟩ := h μ 𝓟fr hF href ξ hξ
  refine h' ξ 𝓟fr hF href' _ ?_
  exact ConvexPowerset.mem_bind.mpr ⟨ξ, ConvexPowerset.self_mem_singleton' _, f, hf, rfl⟩

lemma wp_if_true {b : Expr} {c₁ c₂ : Cmd Act} {φ ψ : OProp} :
     ⌈b == Expr.literal 1⌉ ∧ wp_base 𝓘 F c₁ ψ ⊢ wp_base 𝓘 F (Cmd.if_stmt b c₁ c₂) ψ := by
  intro 𝓟 ⟨htrue, hwp⟩ μ 𝓟fr hF href ν hν; rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_if_stmt] at hν
  sorry

lemma wp_assign (x : Var) (e : Expr) (ψ : OProp) (v : Val) :
  ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗ ((⌈$ x == Expr.literal v ∧ own e⌉) -∗ ψ) ⊢
   wp_base 𝓘 F (x ::= e) ψ := sorry

lemma wp_bern (x : Var) (e : Expr) (v : Val) {ψ : OProp} :
    ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗ (($ x ~ Bern v ∧ ⌈own e⌉) -∗ ψ) ⊢
    wp_base 𝓘 F (x :≈ PExpr.Bern e) ψ := by sorry

lemma wp_bounded_rank {ℓ h : ℕ} (hle : ℓ ≤ h) {φ : Set.Icc ℓ h → OProp} {b rank : Expr} {p : ℚ} (hp : p > 0)
    (hrank : ∀ r, φ r ⊢ ⌈rank == Expr.literal r⌉)
    (hexit : φ ⟨ℓ, le_refl _, hle⟩ ⊢ ⌈b == Expr.literal 0⌉)
    (hloop : ∀ {r}, r.val > ℓ → φ r ⊢ ⌈b == Expr.literal 1⌉)
    (hprec : (φ ⟨ℓ, le_refl _, hle⟩).Precise) :
    (∀ r, ⌜r.val > 0⌝ -∗ φ r -∗
      wp_base 𝓘 F c
        (⨁[Bern p] fun x ↦
          if x = 1 then
            (& fun (s : Set.Ico ℓ r) ↦
              φ ⟨s.val, s.property.1, (le_of_lt s.property.2).trans r.property.2⟩)
          else
            (& φ)))
      ⊢ & φ -∗ wp 𝓘 (while( b ){ c }) (φ ⟨ℓ, le_refl _, hle⟩) := sorry

/-- CONCURRNCY RULES -/

-- This mostly follows from invariant monotonicity, but we need a few more properties about
-- assertions, etc
lemma wp_share {𝓘 : Inv} {F : ProbSpace → Prop} {c : Cmd Act} {ψ : OProp} :
    OProp.sure 𝓘.to_MProp ∗ wp_base 𝓘 F c ψ ⊢ wp_base Inv.emp F c iprop(ψ ∗ OProp.sure 𝓘.to_MProp) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h𝓘, hwp⟩ μ 𝓟fr hF hre ν hν
  have hν' : ν ∈ ConvexPowerset.singleton' μ >>= Pom.lin (c.withInv 𝓘).to_pom := by
    refine le_iff_supset.mp ?_ hν
    apply ConvexPowerset.bind_monotone (le_refl _)
    apply (Pom.lin_continuous (act := WithInv Act) (test := Test)).monotone
    apply Cmd.withInv_monotone; refine ⟨Set.empty_subset _, ?_⟩
    intro σ; sorry
  have ⟨𝓠, hre', hψ⟩ := hwp μ 𝓟fr hF sorry ν sorry
  refine ⟨𝓠 ⊗ ProbSpace.trivial 𝓘.to_MProp, ?_, ?_⟩
  · sorry
  · refine ⟨_, _, ?_, le_refl _, hψ, ?_⟩
    · -- Need some lemmas about domain being contractive after `wp`
      sorry
    · -- This should also be a lemma
      sorry

lemma wp_atom {𝓘 : Inv} {F : ProbSpace → Prop} {a : Act} {ψ : OProp} :
    (OProp.sure 𝓘.to_MProp -∗ wp_base Inv.emp F (Cmd.act a) (iprop(ψ ∗ OProp.sure 𝓘.to_MProp)))
    ⊢ wp_base 𝓘 F (Cmd.act a) ψ := by
  sorry

/-- **The parallel composition rule.**  If the postconditions `ψ₁` and `ψ₂` are precise, then
the weakest preconditions of two threads can be combined with the separating conjunction.

The proof follows the `Par` case of the soundness theorem of the pcOL paper: precision
provides least probability spaces `𝓠₁` and `𝓠₂` satisfying the two postconditions, each
thread is shown to take any frame-respecting refinement of its precondition to a refinement
of `𝓠ₖ`, and the two threads are then combined by `lemma_C6`. -/
lemma wp_par {𝓘 : Inv} {c₁ c₂ : Cmd Act} {ψ₁ ψ₂ : OProp}
    (hψ₁ : ψ₁.Precise) (hψ₂ : ψ₂.Precise) :
    wp 𝓘 c₁ ψ₁ ∗ wp 𝓘 c₂ ψ₂ ⊢ wp 𝓘 (c₁.par c₂) iprop(ψ₁ ∗ ψ₂) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h₁, h₂⟩ μ 𝓟fr _ hre ν hν
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
    obtain ⟨𝓠, href, hψ⟩ := h₁ μ₁ 𝓕 True.intro hre₁ ν₁ hν₁
    exact Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left ((hQ₁ 𝓠).mpr hψ))) href
  have hthread₂ : ∀ (𝓕 : ProbSpace) (μ₂ : Distr Mem),
      ((𝓟₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ μ₂) →
      ∀ ν₂ ∈ ConvexPowerset.singleton' μ₂ >>= 𝓛 (c₂.withInv 𝓘).to_pom,
        ((𝓠₂ ⊗ 𝓕 ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ ν₂) := by
    intro 𝓕 μ₂ hre₂ ν₂ hν₂
    obtain ⟨𝓠, href, hψ⟩ := h₂ μ₂ 𝓕 True.intro hre₂ ν₂ hν₂
    exact Distr.Refines.mono
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left ((hQ₂ 𝓠).mpr hψ))) href
  -- The parallel composition is handled by Lemma C.6
  rw [Cmd.withInv, Cmd.to_pom] at hν
  exact lemma_C6 hμ hthread₁ hthread₂ ν hν

/- STRUCTURAL RULES -/

variable {ι : Type} {𝓘 : Inv} {F : ProbSpace → Prop} {c : Cmd Act} {ξ : PMF ι} {φ ψ : OProp}

lemma wp_conseq (h : φ ⊢ ψ) : wp_base 𝓘 F c φ ⊢ wp_base 𝓘 F c ψ := by
  intro 𝓟 hc μ 𝓟fr F hre ν hν
  have ⟨𝓠, hre', hφ⟩ := hc μ 𝓟fr F hre ν hν
  refine ⟨𝓠, hre', ?_⟩; exact h 𝓠 hφ

lemma wp_split {ψ : ι → OProp} :
    (⨁[ ξ ] fun v ↦ wp_base 𝓘 F c (ψ v)) ⊢ wp_base 𝓘 F c (⨁[ ξ ] ψ) := by
  intro 𝓟 ⟨𝓟', V, hdsj, hdom, hsum, hwp⟩ μ 𝓟fr hF hre ν hν
  obtain ⟨k, rfl, hk⟩ :
      ∃ k,
        μ = ξ.bind k ∧
        ∀ v ∈ ξ.support, (𝓟' v ⊗ 𝓟fr ⊗ ProbSpace.trivial 𝓘.to_MProp) ≼ k v :=
    sorry
  obtain ⟨ξ', _, f, hf, rfl⟩ := ConvexPowerset.mem_bind.mp hν
  have : ξ' = ξ.bind k := sorry; subst this
  have h v hv := hwp v hv (k v) 𝓟fr hF (hk v hv) ((k v).bind f) sorry
  choose 𝓠 h𝓠 using h
  classical
  let 𝓠' v := if h : v ∈ ξ.support then 𝓠 v h else ProbSpace.trivial Iris.BI.BIBase.emp
  -- Also need to permute indices to make the `𝓠'`s disjoint
  refine ⟨ProbSpace.sum ξ 𝓠' V sorry sorry, ?_, ?_⟩
  · sorry
  · refine ⟨𝓠', V, sorry, sorry, le_refl _, ?_⟩
    intro v hv; unfold 𝓠'; rw [dif_pos hv]
    exact h𝓠 v hv |>.2

lemma wp_nsplit {ψ : ι → OProp} :
    (& fun v ↦ wp_base 𝓘 F c (ψ v)) ⊢ wp_base 𝓘 F c (& ψ) := by sorry

lemma wp_weaken :
    wp 𝓘 c ψ ⊢ wp_weak 𝓘 c ψ := by
  intro 𝓟 hwp μ 𝓕 _ hre ν hν
  exact hwp μ 𝓕 True.intro hre ν hν

lemma wp_strengthen (h : ψ.Precise) :
    wp_weak 𝓘 c ψ ⊢ wp 𝓘 c ψ := by
  sorry

lemma wp_frame :
    φ ∗ wp 𝓘 c ψ ⊢ wp 𝓘 c iprop(φ ∗ ψ) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdsj, hle, hφ, hwp⟩ μ 𝓕 _ hre ν hν
  have ⟨𝓠, hre', hψ⟩ := hwp μ (𝓕 ⊗ 𝓟₁) True.intro ?_ ν hν
  · refine ⟨𝓠 ⊗ 𝓟₁, ?_, 𝓟₁, 𝓠, ?_, ?_, hφ, hψ⟩
    · sorry
    · sorry
    · sorry
  · sorry

/--
**Assignment rule that preserves the value of the assigned expression.**

If writing to `x` cannot change the value of `e` (hypothesis `he`), then the value of `e` is
still known after the assignment.  This is a strengthening of `wp_assign`, which only
returns the ownership of `e`; it is what makes it possible to re-establish an invariant that
constrains a variable read by the assignment.

After the assignment both `x` and `e` hold the value `v` deterministically, and they live in
disjoint parts of the memory, so the two certainties are returned as separate resources.
-/
lemma wp_assign_pres {𝓘 : Inv} {F : ProbSpace → Prop} (x : Var) (e : Expr) (ψ : OProp) (v : Val)
    (he : ∀ (σ : Mem) (w : Val), e (σ.extend x w) = e σ) :
    ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗
      ((iprop(⌈$ x == Expr.literal v⌉ ∗ ⌈e == Expr.literal v⌉)) -∗ ψ) ⊢
    wp_base 𝓘 F (x ::= e) ψ := sorry

/-- **Elimination of a nondeterministic choice in the precondition.**

If the postcondition is precise, then it is enough to establish the weakest precondition in
each branch of a nondeterministic choice. -/
lemma wp_nondet {κ : Type} {ψ : OProp} (h : ψ.Precise) :
    OProp.nondet (fun (_ : κ) => wp_base 𝓘 F c ψ) ⊢ wp_base 𝓘 F c ψ :=
  Iris.BI.Entails.trans wp_nsplit (wp_conseq (OProp.nondet_collapse h))

lemma wp_exists {ι : Type} {P : ι → MProp} :
    ((& fun i ↦ ⌈P i⌉) -∗ wp_base 𝓘 F c ψ)
    ⊢ ⌈ iprop( ∃ i, P i ) ⌉ -∗ wp_weak 𝓘 c ψ := by
  sorry

end Pcol
