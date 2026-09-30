import PcolIris.Logic.Par
import PcolIris.Logic.LemmaC6
import PcolIris.Logic.Framed
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.OProp.Laws
import PcolIris.Semantics.Invariant
import PcolIris.Semantics.Semantics
import PcolIris.OProp.OProp

namespace Pcol

open MProp

def wp_base (𝓘 : Inv) (F : ProbSpace → Prop) (c : Cmd Act) (ψ : OProp) : OProp where
  prop 𝓟 :=
    ∀ (μ : Distr Mem) (𝓟fr 𝓙 : ProbSpace),
      -- The frame validity predicate holds
      F 𝓟fr →
      -- The initial distribution `μ` refines the precondition `𝓟`, the frame `𝓟fr`, and a
      -- space `𝓙` satisfying the invariant `𝓘`
      Framed 𝓘 𝓟 𝓟fr 𝓙 μ →
      -- Take any `ν` that results from running the program
      ∀ ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 (c.withInv 𝓘).to_pom,
      -- Then `ν` refines some probability space `𝓠`, which satisfies the postcondition `ψ`,
      -- together with the same frame and a space satisfying the invariant
        ∃ 𝓠 𝓙', Framed 𝓘 𝓠 𝓟fr 𝓙' ν ∧ ψ 𝓠
  upcl := fun hle h μ 𝓟fr 𝓙 hF hf ν hν ↦ h μ 𝓟fr 𝓙 hF (hf.mono hle) ν hν

/-- The standard "strong" wp allows any frame -/
def wp (𝓘 : Inv) : Cmd Act → OProp → OProp := wp_base 𝓘 (fun _ ↦ True)

/-- The "weak" wp only preserves frames for trivial probability spaces,
where every event has probability exactly 0 or 1 -/
def wp_weak (𝓘 : Inv) : Cmd Act → OProp → OProp := wp_base 𝓘 fun 𝓟fr ↦
  ∀ E, 𝓟fr.mspace.MeasurableSet' E → 𝓟fr.μ E = 0 ∨ 𝓟fr.μ E = 1

notation 𝓘 " ⊢{{" φ "}} " c " {{" ψ "}}" => φ ⊢ wp 𝓘 c ψ

/- BASIC COMMAND RULES -/

variable {𝓘 : Inv} {F : ProbSpace → Prop} {c : Cmd Act}

/-- The `Skip` rule. -/
lemma wp_skip (φ : OProp) :
    φ ⊢ wp_base 𝓘 F Cmd.skip φ := by
  intro 𝓟 hφ μ 𝓟fr 𝓙 _ hf ν hν
  refine ⟨𝓟, 𝓙, ?_, hφ⟩
  rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_skip, bind_pure] at hν
  have hle : μ ≤ ν := by
    have : ν ∈ (ConvexPowerset.singleton' μ).set := hν
    rwa [ConvexPowerset.singleton'_set_eq] at this
  rwa [← proper_dist_maximal hf.refines.bot_0 hle]

lemma wp_seq {c₁ c₂ : Cmd Act} {ψ : OProp} :
    wp_base 𝓘 F c₁ (wp_base 𝓘 F c₂ ψ) ⊢ wp_base 𝓘 F (Cmd.seq c₁ c₂) ψ := by
  intro 𝓟 h μ 𝓟fr 𝓙 hF href ν; rw [Cmd.withInv, Cmd.to_pom, Pom.lin_seq, ← bind_assoc]
  intro hν; rcases ConvexPowerset.mem_bind.mp hν with ⟨ξ, hξ, f, hf, rfl⟩
  have ⟨𝓡, 𝓙', href', h'⟩ := h μ 𝓟fr 𝓙 hF href ξ hξ
  refine h' ξ 𝓟fr 𝓙' hF href' _ ?_
  exact ConvexPowerset.mem_bind.mpr ⟨ξ, ConvexPowerset.self_mem_singleton' _, f, hf, rfl⟩

lemma wp_if_true {b : Expr} {c₁ c₂ : Cmd Act} {φ ψ : OProp} :
     ⌈b == Expr.literal 1⌉ ∧ wp_base 𝓘 F c₁ ψ ⊢ wp_base 𝓘 F (Cmd.if_stmt b c₁ c₂) ψ := by
  intro 𝓟 ⟨htrue, hwp⟩ μ 𝓟fr 𝓙 hF href ν hν; rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_if_stmt] at hν
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
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h𝓘, hwp⟩ μ 𝓟fr 𝓙 hF hf ν hν
  have hν' : ν ∈ ConvexPowerset.singleton' μ >>= Pom.lin (c.withInv 𝓘).to_pom := by
    refine le_iff_supset.mp ?_ hν
    apply ConvexPowerset.bind_monotone (le_refl _)
    apply (Pom.lin_continuous (act := WithInv Act) (test := Test)).monotone
    exact Cmd.withInv_monotone c (Inv.le_emp 𝓘)
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
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h₁, h₂⟩ μ 𝓟fr 𝓙 _ hf ν hν
  -- Running each thread alone shows that `ψ₁` and `ψ₂` are satisfiable, so by precision
  -- they have least models `𝓠₁` and `𝓠₂`
  have hf' := hf.mono hle
  obtain ⟨ν₁, hν₁⟩ := (ConvexPowerset.singleton' μ >>= 𝓛 (c₁.withInv 𝓘).to_pom).nonempty
  obtain ⟨ν₂, hν₂⟩ := (ConvexPowerset.singleton' μ >>= 𝓛 (c₂.withInv 𝓘).to_pom).nonempty
  obtain ⟨_, _, -, hψ₁'⟩ := h₁ μ _ 𝓙 True.intro (hf'.left hdisj) ν₁ hν₁
  obtain ⟨_, _, -, hψ₂'⟩ := h₂ μ _ 𝓙 True.intro (hf'.right hdisj) ν₂ hν₂
  obtain ⟨𝓠₁, hQ₁⟩ := hψ₁ _ hψ₁'
  obtain ⟨𝓠₂, hQ₂⟩ := hψ₂ _ hψ₂'
  -- Each thread, run in isolation with an arbitrary frame, establishes its postcondition;
  -- by precision, the least such postcondition space is `𝓠ₖ`
  have hthread₁ : ∀ (𝓕 𝓙₁ : ProbSpace) (μ₁ : Distr Mem), Framed 𝓘 𝓟₁ 𝓕 𝓙₁ μ₁ →
      ∀ ν₁ ∈ ConvexPowerset.singleton' μ₁ >>= 𝓛 (c₁.withInv 𝓘).to_pom,
        ∃ 𝓙₁', Framed 𝓘 𝓠₁ 𝓕 𝓙₁' ν₁ := by
    intro 𝓕 𝓙₁ μ₁ hf₁ ν₁ hν₁
    obtain ⟨𝓠, 𝓙₁', hf', hψ⟩ := h₁ μ₁ 𝓕 𝓙₁ True.intro hf₁ ν₁ hν₁
    exact ⟨𝓙₁', hf'.mono ((hQ₁ 𝓠).mpr hψ)⟩
  have hthread₂ : ∀ (𝓕 𝓙₂ : ProbSpace) (μ₂ : Distr Mem), Framed 𝓘 𝓟₂ 𝓕 𝓙₂ μ₂ →
      ∀ ν₂ ∈ ConvexPowerset.singleton' μ₂ >>= 𝓛 (c₂.withInv 𝓘).to_pom,
        ∃ 𝓙₂', Framed 𝓘 𝓠₂ 𝓕 𝓙₂' ν₂ := by
    intro 𝓕 𝓙₂ μ₂ hf₂ ν₂ hν₂
    obtain ⟨𝓠, 𝓙₂', hf', hψ⟩ := h₂ μ₂ 𝓕 𝓙₂ True.intro hf₂ ν₂ hν₂
    exact ⟨𝓙₂', hf'.mono ((hQ₂ 𝓠).mpr hψ)⟩
  -- The parallel composition is handled by Lemma C.6
  rw [Cmd.withInv, Cmd.to_pom] at hν
  obtain ⟨𝓙', hf''⟩ := lemma_C6 hf' hthread₁ hthread₂ ν hν
  -- We still need to prove that `𝓠₁` and `𝓠₂` own disjoint variables, which requires
  -- knowing that the footprint of a postcondition is contained in that of the precondition
  exact ⟨𝓠₁ ⊗ 𝓠₂, 𝓙', hf'',
    𝓠₁, 𝓠₂, sorry, le_refl _, (hQ₁ 𝓠₁).mp (le_refl _), (hQ₂ 𝓠₂).mp (le_refl _)⟩

/- STRUCTURAL RULES -/

variable {ι : Type} [Countable ι] {𝓘 : Inv} {F : ProbSpace → Prop} {c : Cmd Act} {ξ : PMF ι} {φ ψ : OProp}

lemma wp_conseq (h : φ ⊢ ψ) : wp_base 𝓘 F c φ ⊢ wp_base 𝓘 F c ψ := by
  intro 𝓟 hc μ 𝓟fr 𝓙 hF hf ν hν
  have ⟨𝓠, 𝓙', hf', hφ⟩ := hc μ 𝓟fr 𝓙 hF hf ν hν
  exact ⟨𝓠, 𝓙', hf', h 𝓠 hφ⟩

lemma wp_split {ψ : ι → OProp} :
    (⨁[ ξ ] fun v ↦ wp_base 𝓘 F c (ψ v)) ⊢ wp_base 𝓘 F c (⨁[ ξ ] ψ) := by
  -- Plan: decompose `μ` along the summands of the precondition, run each summand
  -- separately, and recombine the results with `ProbSpace.sum` (relabeling the outcomes of
  -- the summands so that their supports are disjoint).
  sorry

lemma wp_nsplit {ψ : ι → OProp} :
    (& fun v ↦ wp_base 𝓘 F c (ψ v)) ⊢ wp_base 𝓘 F c (& ψ) := by sorry

lemma wp_weaken :
    wp 𝓘 c ψ ⊢ wp_weak 𝓘 c ψ := by
  intro 𝓟 hwp μ 𝓕 𝓙 _ hf ν hν
  exact hwp μ 𝓕 𝓙 True.intro hf ν hν

lemma wp_strengthen (h : ψ.Precise) :
    wp_weak 𝓘 c ψ ⊢ wp 𝓘 c ψ := by
  sorry

lemma wp_frame :
    φ ∗ wp 𝓘 c ψ ⊢ wp 𝓘 c iprop(φ ∗ ψ) := by
  -- Plan: run the program with the frame `𝓕 ⊗ 𝓟₁`, and rearrange the products.
  sorry

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
lemma wp_nondet {κ : Type} [Countable κ] {ψ : OProp} (h : ψ.Precise) :
    OProp.nondet (fun (_ : κ) => wp_base 𝓘 F c ψ) ⊢ wp_base 𝓘 F c ψ :=
  Iris.BI.Entails.trans wp_nsplit (wp_conseq (OProp.nondet_collapse h))

lemma wp_exists {ι : Type} [Countable ι] {P : ι → MProp} :
    ((& fun i ↦ ⌈P i⌉) -∗ wp_base 𝓘 F c ψ)
    ⊢ ⌈ iprop( ∃ i, P i ) ⌉ -∗ wp_weak 𝓘 c ψ := by
  sorry

end Pcol
