/-
# The von Neumann trick

This file formalises the example of Section 6.4 (with the derivation of Appendix F.6) of the
pcOL paper: the program

    x := 0 ⨟ y := 0 ⨟ while x = y do (p' := p ⨟ x :≈ Ber(p') ⨟ y :≈ Ber(p'))

turns a coin of unknown bias `p` into a fair coin, even when the bias is changed
concurrently by the environment between two iterations, as long as it always stays in
`[eps, 1 - eps]`.  The bias is a shared resource, governed by the resource invariant `inv`;
the loop is verified with the `BoundedRank` rule, using the loop invariant
`loopInv = phi0 ∨ phi1` of the paper, whose rank is the value of the guard.

The derivation uses the rules of `PcolIris.Logic.WeakestPre`, several of which are
themselves still unproven in the development.  In addition, a handful of laws used by the
paper's derivation are not available at all; they are collected, stated and documented in
the section "Laws of pcOL that this development does not provide yet" below, and are the
only assumptions this file adds.
-/
import PcolIris.Logic.WeakestPre
import PcolIris.OProp.Laws

namespace Pcol

open MProp
open OProp

namespace VonNeumann

/-! ### The program -/

/-- The test `e₁ = e₂`, as an expression evaluating to `1` (true) or `0` (false). -/
def eqTest (e₁ e₂ : Expr) : Expr :=
  fun σ ↦ do
    let v₁ ← e₁ σ
    let v₂ ← e₂ σ
    pure <| if v₁ = v₂ then 1 else 0

/-- The body of the loop of the von Neumann trick: the current bias is read from the shared
variable `p` into the local variable `p'`, and two coins with that bias are flipped. -/
noncomputable def body : Cmd Act :=
  "p'" ::= $"p" ⨟
  "x" :≈ PExpr.Bern ($"p'") ⨟
  "y" :≈ PExpr.Bern ($"p'")

/-- The von Neumann trick: two coins of the (shared, unknown) bias `p` are flipped until
they disagree; the value of `x` is then a fair coin flip. -/
noncomputable def vonNeumann : Cmd Act :=
  "x" ::= 0 ⨟
  "y" ::= 0 ⨟
  while( eqTest ($"x") ($"y") ){ body }

/-! ### The resource invariant and the loop invariant -/

/-- The resource invariant `I = (p ∈ L)`: the shared variable `p` holds one of the finitely
many admissible biases.  In the paper `L` is the finite list `[ε, 1 - ε]_Δ` of biases that
are bounded away from `0` and `1`. -/
def inv (L : Finset ℚ) : Inv where
  dom := {"p"}
  prop σ := σ.dom = {"p"} ∧ ∃ v ∈ L, σ "p" = some v
  dom_finite := Set.finite_singleton _
  dom_valid := by rintro σ ⟨h, -⟩; exact h
  prop_finite := by
    have hsingle : ∀ {σ : Mem} {v : Val}, σ.dom = {"p"} → σ "p" = some v →
        σ = Mem.singleton "p" v := by
      intro σ v hdom hp
      funext z
      by_cases hz : "p" = z
      · subst hz; simpa [Mem.singleton, Mem.extend] using hp
      · have hzdom : z ∉ σ.dom := by rw [hdom]; exact fun h ↦ hz h.symm
        rw [Mem.notMem_dom_iff.mp hzdom]
        simp [Mem.singleton, Mem.extend, Mem.emp, hz]
    refine ((L.finite_toSet).image fun v ↦ Mem.singleton "p" v).subset ?_
    rintro σ ⟨hdom, v, hv, hσ⟩
    exact ⟨v, hv, (hsingle hdom hσ).symm⟩

/-- `φ₀`: the two coin flips disagree and `x` is a fair coin flip.  This is the loop
invariant at rank `0`, i.e. when the loop has terminated. -/
def phi0 : OProp :=
  ⨁[Bern 0.5] fun b ↦ ⌈($"x" == Expr.literal b) ∧ ($"y" == Expr.literal (1 - b))⌉

/-- `φ₁`: the two coin flips agree (so the loop keeps going) and the local variable `p'` is
owned.  This is the loop invariant at rank `1`. -/
def phi1 : OProp := ⌈($"x" == $"y") ∧ own ($"p'")⌉

/-- The loop invariant `φ = φ₀ ∨ φ₁` of the paper, presented as a family indexed by the
rank `R ∈ {0, 1}`. -/
def loopInv : Set.Icc (0 : ℕ) 1 → OProp := fun r ↦ if (r : ℕ) = 0 then phi0 else phi1

/-! ### The Bernoulli distribution -/

/-- Only the two bits `0` and `1` are in the support of a Bernoulli distribution. -/
lemma Bern_support {p : ℚ} {w : Val} (hw : w ∈ (Bern p).support) : w = 0 ∨ w = 1 := by
  unfold Bern at hw
  rw [PMF.mem_support_map_iff] at hw
  obtain ⟨b, -, rfl⟩ := hw
  cases b <;> simp

/-- The weights of a Bernoulli distribution with parameter at most `1`. -/
lemma Bern_apply {p : ℚ} (hp1 : p ≤ 1) (w : Val) :
    Bern p w =
      if w = 1 then ENNReal.ofReal (p : ℝ)
      else if w = 0 then 1 - ENNReal.ofReal (p : ℝ) else 0 := by
  have hle : ENNReal.ofReal ((p : ℝ)) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]; exact_mod_cast hp1
  have hq : min 1 (ENNReal.ofReal ((p : ℝ))) = ENNReal.ofReal (p : ℝ) := min_eq_right hle
  unfold Bern
  rw [PMF.map_apply]
  simp only [PMF.ofFintype_apply, tsum_bool, hq]
  by_cases h1 : w = 1
  · simp [h1]
  · by_cases h0 : w = 0
    · simp [h0]
    · simp [h0, h1]

/-! ### The guard and the rank -/

lemma eqTest_eval {σ : Mem} {a b : Val} (hx : σ "x" = some a) (hy : σ "y" = some b) :
    eqTest ($"x") ($"y") σ = some (if a = b then 1 else 0) := by
  simp [eqTest, Expr.var, hx, hy]

/-- When the two coins disagree, the guard of the loop is false. -/
lemma guard_false {b : Val} (hb : b = 0 ∨ b = 1) :
    (iprop(($"x" == Expr.literal b) ∧ ($"y" == Expr.literal (1 - b))) : MProp) ⊢
      (eqTest ($"x") ($"y") == Expr.literal 0) := by
  rintro σ ⟨⟨-, hx⟩, -, hy⟩
  have hx' : σ "x" = some b := hx
  have hy' : σ "y" = some (1 - b) := hy
  have hne : b ≠ 1 - b := by rcases hb with rfl | rfl <;> norm_num
  have h := eqTest_eval (σ := σ) (a := b) (b := 1 - b) hx' hy'
  rw [if_neg hne] at h
  exact ⟨by rw [h]; rfl, by rw [h]; rfl⟩

/-- When the two coins agree, the guard of the loop is true. -/
lemma guard_true :
    (iprop(($"x" == $"y") ∧ own ($"p'")) : MProp) ⊢
      (eqTest ($"x") ($"y") == Expr.literal 1) := by
  rintro σ ⟨⟨hs, hxy⟩, -⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  have ha' : σ "x" = some a := ha
  have hy : σ "y" = some a := hxy.symm.trans ha
  have h := eqTest_eval (σ := σ) ha' hy
  rw [if_pos rfl] at h
  exact ⟨by rw [h]; rfl, by rw [h]; rfl⟩

/-- `φ₀` is precise. -/
lemma phi0_precise : phi0.Precise := Precise.oplus fun _ _ ↦ Precise.sure _

/-- After the loop, `x` is a fair coin flip. -/
lemma phi0_fair : phi0 ⊢ ($"x") ~ Bern 0.5 :=
  OProp.oplus_weaken' fun _ _ ↦ OProp.sure_weaken Iris.BI.and_elim_l

/-- The loop invariant determines the rank, which is the value of the guard. -/
lemma loopInv_rank (r : Set.Icc (0 : ℕ) 1) :
    loopInv r ⊢ ⌈eqTest ($"x") ($"y") == Expr.literal (r : ℕ)⌉ := by
  unfold loopInv
  by_cases h : (r : ℕ) = 0
  · rw [if_pos h, h]
    have h1 : phi0 ⊢ (⨁[Bern 0.5] (fun (_ : Val) => ⌈eqTest ($"x") ($"y") == Expr.literal 0⌉)) :=
      OProp.oplus_weaken' fun b hb ↦ OProp.sure_weaken (guard_false (Bern_support hb))
    have h2 := Iris.BI.Entails.trans h1 (OProp.oplus_collapse (Precise.sure _))
    rw [Nat.cast_zero]
    exact h2
  · have h1 : (r : ℕ) = 1 := le_antisymm r.2.2 (Nat.one_le_iff_ne_zero.mpr h)
    rw [if_neg h, h1, Nat.cast_one]
    exact OProp.sure_weaken guard_true

/-! ### Memory bookkeeping -/

lemma mem_restrict_le (σ : Mem) (X : Set Var) : σ.restrict X ≤ σ := by
  intro z
  by_cases hz : z ∈ X
  · rw [Mem.restrict_apply_of_mem σ hz]
    cases σ z <;> simp
  · rw [Mem.restrict_apply_of_notMem σ hz]
    trivial

lemma mem_union_le {σ₁ σ₂ σ : Mem} (h₁ : σ₁ ≤ σ) (h₂ : σ₂ ≤ σ) : (σ₁ ⊎ σ₂) ≤ σ := by
  intro z
  specialize h₁ z; specialize h₂ z
  cases h : σ₁ z with
  | none =>
    rw [Mem.union_apply_of_notMem_dom (Mem.notMem_dom_iff.mpr h)]
    exact h₂
  | some v =>
    rw [Mem.union_apply_of_mem_dom (Mem.mem_dom_iff.mpr (by rw [h]; simp)), h]
    rw [h] at h₁
    exact h₁

lemma mem_restrict_mono (σ : Mem) {X Y : Set Var} (h : X ⊆ Y) : σ.restrict X ≤ σ.restrict Y := by
  intro z
  by_cases hz : z ∈ X
  · rw [Mem.restrict_apply_of_mem σ hz, Mem.restrict_apply_of_mem σ (h hz)]
    cases σ z <;> simp
  · rw [Mem.restrict_apply_of_notMem σ hz]
    trivial

lemma own_var_restrict {σ : Mem} {x : Var} {X : Set Var} (hx : x ∈ X) (h : (σ x).isSome) :
    (own (Expr.var x) : MProp) (σ.restrict X) := by
  change (((σ.restrict X) x)).isSome
  rw [Mem.restrict_apply_of_mem σ hx]
  exact h

lemma restrict_disjoint (σ : Mem) {X Y : Set Var} (h : Disjoint X Y) :
    Disjoint (σ.restrict X).dom (σ.restrict Y).dom := by
  rw [Mem.restrict_dom, Mem.restrict_dom]
  exact Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right h

/-- The loop invariant at rank `1` owns the three variables that the loop body writes. -/
lemma phi1_resources :
    (iprop(($"x" == $"y") ∧ own ($"p'")) : MProp) ⊢
      iprop(own ($"p'") ∗ (own ($"x") ∗ own ($"y"))) := by
  rintro σ ⟨⟨hs, hxy⟩, hp⟩
  have hxs : (σ "x").isSome := hs
  have hxy' : σ "x" = σ "y" := hxy
  have hys : (σ "y").isSome := hxy' ▸ hxs
  have hps : (σ "p'").isSome := hp
  refine ⟨σ.restrict {"p'"}, σ.restrict {"x", "y"}, ?_, ?_, ?_, ?_⟩
  · exact restrict_disjoint σ (by simp)
  · exact mem_union_le (mem_restrict_le σ _) (mem_restrict_le σ _)
  · exact own_var_restrict rfl hps
  · refine ⟨σ.restrict {"x"}, σ.restrict {"y"}, restrict_disjoint σ (by simp), ?_, ?_, ?_⟩
    · exact mem_union_le (mem_restrict_mono σ (by simp)) (mem_restrict_mono σ (by simp))
    · exact own_var_restrict rfl hxs
    · exact own_var_restrict rfl hys

/-! ### Convexity

The `NSplit2` rule of the paper eliminates a nondeterministic choice in the precondition,
provided the postcondition is *convex*, i.e. closed under probabilistic mixtures.  The
development only provides the version of the rule for *precise* postconditions
(`wp_nondet`), which is too strong here: the postcondition of the loop body is a
nondeterministic mixture.  We therefore introduce convexity and derive the corresponding
rule from `wp_nsplit`. -/

/-- An assertion is convex when it is closed under probabilistic mixtures. -/
def Convex (ψ : OProp) : Prop := ∀ {ι : Type} (ξ : PMF ι), (⨁[ξ] (fun (_ : ι) => ψ)) ⊢ ψ

/-- A precise assertion is convex. -/
lemma Convex.of_precise {ψ : OProp} (h : ψ.Precise) : Convex ψ := fun _ ↦ OProp.oplus_collapse h

/-- Weakest preconditions of convex postconditions are convex. -/
lemma Convex.wp {ψ : OProp} {J : Inv} {F : ProbSpace → Prop} {c : Cmd Act} (h : Convex ψ) :
    Convex (wp_base J F c ψ) :=
  fun ξ ↦ Iris.BI.Entails.trans wp_split (wp_conseq (h ξ))

/-- The separating conjunction of a convex assertion and a precise one is convex. -/
lemma Convex.sep_precise {φ ψ : OProp} (hφ : Convex φ) (hψ : ψ.Precise) :
    Convex iprop(φ ∗ ψ) := fun ξ ↦
  Iris.BI.Entails.trans (OProp.oplus_distrib' ξ (fun _ ↦ φ) ψ hψ)
    (Iris.BI.sep_mono_left (hφ ξ))

/-- A nondeterministic choice between copies of a convex assertion collapses. -/
lemma nondet_collapse_convex {ι : Type} {ψ : OProp} (h : Convex ψ) :
    OProp.nondet (fun (_ : ι) ↦ ψ) ⊢ ψ := by
  rintro P ⟨ξ, hξ⟩
  exact h ξ P hξ

/-- **The `NSplit2` rule**: a nondeterministic choice in the precondition can be analysed
branch by branch, provided the postcondition is convex. -/
lemma wp_nsplit2 {ι : Type} {ψ : OProp} {J : Inv} {F : ProbSpace → Prop} {c : Cmd Act}
    (h : Convex ψ) : OProp.nondet (fun (_ : ι) ↦ wp_base J F c ψ) ⊢ wp_base J F c ψ :=
  Iris.BI.Entails.trans wp_nsplit (wp_conseq (nondet_collapse_convex h))

/-! ### Opening and re-establishing the resource invariant -/

/-- If `p` holds one of the admissible biases, then the resource invariant holds. -/
lemma inv_of_p_eq {L : Finset ℚ} (v : Val) (hv : v ∈ L) :
    ($"p" == Expr.literal v) ⊢ (inv L).to_MProp := by
  intro σ hσ
  have hp : σ "p" = some v := hσ.2
  have hmem : "p" ∈ (inv L).dom := rfl
  refine ⟨?_, v, hv, ?_⟩
  · rw [Mem.restrict_dom]
    refine Set.inter_eq_right.mpr ?_
    rintro z rfl
    exact Mem.mem_dom_iff.mpr (by rw [hp]; exact Option.some_ne_none v)
  · rw [Mem.restrict_apply_of_mem σ hmem, hp]

/-- The resource invariant guarantees that `p` holds one of the admissible biases. -/
lemma exists_p_of_inv (L : Finset ℚ) :
    (inv L).to_MProp ⊢ iprop(∃ (v : {v : ℚ // v ∈ L}), ($"p") == Expr.literal v.val) := by
  intro σ hσ
  have hmem : "p" ∈ (inv L).dom := rfl
  obtain ⟨-, v, hv, hp⟩ := hσ
  rw [Mem.restrict_apply_of_mem σ hmem] at hp
  exact ⟨_, ⟨⟨v, hv⟩, rfl⟩, ⟨by simp [Expr.var, hp], by simp [Expr.var, Expr.literal, hp]⟩⟩

/-- The two-coin mixture: with probability `q` the two coins disagree, in which case `x` is
a fair coin flip (`phi0`); otherwise they agree and another iteration starts (`phi1`). -/
def bodyMix (q : ℚ) : OProp := ⨁[Bern q] fun t ↦ if t = 1 then phi0 else phi1

/-! ### Laws of pcOL that this development does not provide yet

The derivation below is carried out with the rules of `PcolIris.Logic.WeakestPre`.  A few
ingredients of the paper's proof are missing from the development; they are stated here (and
left unproven) so that the shape of the derivation is exactly the one of Appendix F.6.  The
structural laws about mixtures (`nondet_intro`, `Convex.nondet`, `Convex.oplus`,
`oplus_bern_shift`) all amount to regrouping a probabilistic mixture, which the current
model of `OProp` does not support: `ProbSpace.sum` requires the summands to have pairwise
disjoint supports *and* to be pointwise below the ambient probability space even at null
points, so a probability space cannot in general be re-presented as a mixture.  This is the
same defect that the development itself documents for `sum_prod_distribute`. -/

/-- **Introduction of a nondeterministic choice**: every branch of a nondeterministic choice
entails the choice itself.  (In the semantics of the paper `&` is a union of sets of
probability spaces, so this is immediate.) -/
lemma nondet_intro {iota : Type} {phi : iota → OProp} (i : iota) : phi i ⊢ OProp.nondet phi :=
  sorry

/-- Nondeterministic choices are convex: a mixture of unions of mixtures is again one. -/
lemma Convex.nondet {iota : Type} {phi : iota → OProp} : Convex (OProp.nondet phi) := sorry

/-- A probabilistic mixture of convex assertions is convex. -/
lemma Convex.oplus {iota : Type} {xi : PMF iota} {phi : iota → OProp}
    (h : ∀ i, Convex (phi i)) : Convex (⨁[xi] phi) := sorry

/-- **Weakening of the probability of a two-branch mixture**, i.e. the passage from the
mixture `⊕_q` to the mixture `⊕_{≥ p}` of the paper (`p ≤ q`): the excess probability
`q - p` of the first branch is moved to the second branch, which is legitimate as soon as
both branches entail the assertion `chi` of the second branch. -/
lemma oplus_bern_shift {p q : ℚ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1)
    {phi psi chi : OProp} (h1 : phi ⊢ chi) (h2 : psi ⊢ chi) :
    (⨁[Bern q] fun t ↦ if t = 1 then phi else psi) ⊢
      ⨁[Bern p] fun t ↦ if t = 1 then phi else chi := sorry

/-- **The sampling rule of the paper (`Samp`), which keeps the value of the parameter of the
distribution.**  This is to `wp_bern` what `wp_assign_pres` is to `wp_assign`: if writing to
`x` cannot change the value of `e`, then the value of `e` is still known after the sampling,
and it is independent of the sampled value. -/
lemma wp_bern_pres {J : Inv} {F : ProbSpace → Prop} {psi : OProp}
    (x : Var) (e : Expr) (v : Val)
    (he : ∀ (σ : Mem) (w : Val), e (σ.extend x w) = e σ) :
    ⌈e == Expr.literal v ∧ own (Expr.var x)⌉ ∗
        (((Expr.var x ~ Bern v) ∗ ⌈e == Expr.literal v⌉) -∗ psi) ⊢
      wp_base J F (x :≈ PExpr.Bern e) psi := sorry

/-- **The first half of implication (23) of Appendix F.6.**  Two independent coins with the
same bias `X` disagree with probability `2 * X * (1 - X)`, and conditioned on disagreeing
the first one is a fair coin flip; otherwise the two coins agree.  The probabilistic content
of this implication is proved below (`bern_disagree_prob` and `bern_disagree_fair`); what is
assumed here is only the passage from the two independent samples to the joint mixture,
which the current model of `OProp` does not support. -/
lemma body_split (X : ℚ) (hX0 : 0 ≤ X) (hX1 : X ≤ 1) :
    iprop((($"x") ~ Bern X) ∗ ((($"y") ~ Bern X) ∗ ⌈own ($"p'")⌉)) ⊢
      bodyMix (2 * X * (1 - X)) := sorry

/-! ### The probability of exiting the loop -/

/-- The probability that two independent coins with the same bias disagree is at most `1`
(it is in fact at most `1 / 2`). -/
lemma two_mul_one_sub_le_one (X : ℚ) : 2 * X * (1 - X) ≤ 1 := by
  nlinarith [sq_nonneg (2 * X - 1)]

/-- **The second half of implication (23):** if the bias is in `[eps, 1 - eps]`, then the
probability that the two coins disagree is at least `2 * eps * (1 - eps)`. -/
lemma two_mul_one_sub_mono {eps X : ℚ} (hX : eps ≤ X) (hX' : X ≤ 1 - eps) :
    2 * eps * (1 - eps) ≤ 2 * X * (1 - X) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr (by linarith : eps ≤ 1 - X))]

lemma exit_prob_nonneg {eps : ℚ} (heps : 0 < eps) (heps' : eps ≤ 1 / 2) :
    0 ≤ 2 * eps * (1 - eps) := by nlinarith

/-- **The probability of the two coins disagreeing.**  Two independent coins with the same
bias `X` disagree with probability `2 * X * (1 - X)`; this is the probability with which the
loop exits, and it is the mathematical content of implication (23). -/
lemma bern_disagree_prob (X : ℚ) (h0 : 0 ≤ X) (h1 : X ≤ 1) :
    Bern X 0 * Bern X 1 + Bern X 1 * Bern X 0 = ENNReal.ofReal ((2 * X * (1 - X) : ℚ) : ℝ) := by
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h0
  have hX1 : (0 : ℝ) ≤ 1 - (X : ℝ) := by
    have : (X : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  rw [Bern_apply h1 0, Bern_apply h1 1]
  norm_num
  rw [show (1 : ENNReal) - ENNReal.ofReal (X : ℝ) = ENNReal.ofReal ((1 : ℝ) - (X : ℝ)) by
    rw [ENNReal.ofReal_sub _ hX0, ENNReal.ofReal_one]]
  rw [← ENNReal.ofReal_mul hX1, ← ENNReal.ofReal_mul hX0,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- **Why the trick works.**  The two ways for two independent coins of the same bias to
disagree are equally likely, so conditioned on disagreement the first coin is fair -- whatever
the bias `X` is. -/
lemma bern_disagree_fair (X : ℚ) :
    2 * (Bern X 0 * Bern X 1) = Bern X 0 * Bern X 1 + Bern X 1 * Bern X 0 := by
  rw [two_mul, mul_comm (Bern X 1) (Bern X 0)]

/-! ### The loop body -/

/-- The postcondition of the loop body, in the form in which it is established: with
probability `p` the loop exits with `x` a fair coin flip, and otherwise the loop invariant
holds at some rank. -/
def bodyPost' (p : ℚ) : OProp := ⨁[Bern p] fun t ↦ if t = 1 then phi0 else (& loopInv)

/-- The postcondition of the loop body demanded by the `BoundedRank` rule. -/
def bodyPost (q : ℚ) (r : Set.Icc (0 : ℕ) 1) : OProp :=
  ⨁[Bern q] fun t ↦
    if t = 1 then
      (& fun (s : Set.Ico (0 : ℕ) (r : ℕ)) ↦
        loopInv ⟨s.val, s.property.1, (le_of_lt s.property.2).trans r.property.2⟩)
    else
      (& loopInv)

lemma phi0_loopInv : phi0 ⊢ & loopInv := by
  have h : phi0 = loopInv ⟨0, le_refl 0, zero_le_one⟩ := by simp [loopInv]
  rw [h]; exact nondet_intro _

lemma phi1_loopInv : phi1 ⊢ & loopInv := by
  have h : phi1 = loopInv ⟨1, Nat.zero_le 1, le_refl 1⟩ := by simp [loopInv]
  rw [h]; exact nondet_intro _

/-- The postcondition of the loop body is convex, which is the side condition of the
`NSplit2` rule of the paper. -/
lemma bodyPost'_convex (p : ℚ) : Convex (bodyPost' p) :=
  Convex.oplus fun t ↦ by
    by_cases h : t = 1
    · rw [if_pos h]; exact Convex.of_precise phi0_precise
    · rw [if_neg h]; exact Convex.nondet

/-- Implication (23) of Appendix F.6: the two-coin mixture entails the postcondition of the
loop body, with the exit probability weakened to `2 * eps * (1 - eps)`. -/
lemma bodyMix_bodyPost' {eps X : ℚ} (heps : 0 < eps) (heps' : eps ≤ 1 / 2)
    (hX : eps ≤ X) (hX' : X ≤ 1 - eps) :
    bodyMix (2 * X * (1 - X)) ⊢ bodyPost' (2 * eps * (1 - eps)) :=
  oplus_bern_shift (exit_prob_nonneg heps heps') (two_mul_one_sub_mono hX hX')
    (two_mul_one_sub_le_one X) phi0_loopInv phi1_loopInv

/-- At rank `1` the postcondition of the loop body is the one demanded by the `BoundedRank`
rule: the rank can only decrease to `0`, where the loop invariant is `phi0`. -/
lemma bodyPost'_bodyPost (p : ℚ) (r : Set.Icc (0 : ℕ) 1) (hr : (r : ℕ) = 1) :
    bodyPost' p ⊢ bodyPost p r := by
  refine OProp.oplus_weaken' fun t _ ↦ ?_
  by_cases h : t = 1
  · rw [if_pos h, if_pos h]
    exact nondet_intro (phi := fun (s : Set.Ico (0 : ℕ) (r : ℕ)) ↦
      loopInv ⟨s.val, s.property.1, (le_of_lt s.property.2).trans r.property.2⟩)
      ⟨0, le_refl 0, by rw [hr]; exact Nat.zero_lt_one⟩
  · rw [if_neg h, if_neg h]

/-- The second coin flip.  The first coin has already been sampled with the bias `X` held by
`p'`; sampling the second one gives the two-coin mixture of the paper. -/
lemma wp_sample_y {L : Finset ℚ} {F : ProbSpace → Prop} (eps X : ℚ)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 2) (hX : eps ≤ X) (hX' : X ≤ 1 - eps) :
    iprop((($"x") ~ Bern X) ∗ (⌈($"p'") == Expr.literal X⌉ ∗ ⌈own ($"y")⌉)) ⊢
      wp_base (inv L) F ("y" :≈ PExpr.Bern ($"p'")) (bodyPost' (2 * eps * (1 - eps))) := by
  iintro ⟨hx, hp, hy⟩
  iapply wp_bern_pres "y" ($"p'") X (by intro σ w; simp [Expr.var, Mem.extend])
  isplitl [hp hy]
  · iapply sure_and; isplitl [hp]
    · iapply hp
    · iapply hy
  · iintro ⟨hyb, hp'⟩
    ihave hp'' := sure_weaken (P := iprop(($"p'") == Expr.literal X))
      (Q := iprop(own ($"p'"))) (fun σ h ↦ h.1) $$ hp'
    iapply bodyMix_bodyPost' heps heps' hX hX'
    iapply body_split X (by linarith) (by linarith)
    iframe

/-- Both coin flips: the two coins are sampled with the bias `X` held by `p'`. -/
lemma wp_sample_xy {L : Finset ℚ} {F : ProbSpace → Prop} (eps X : ℚ)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 2) (hX : eps ≤ X) (hX' : X ≤ 1 - eps) :
    iprop(⌈($"p'") == Expr.literal X⌉ ∗ (⌈own ($"x")⌉ ∗ ⌈own ($"y")⌉)) ⊢
      wp_base (inv L) F ("x" :≈ PExpr.Bern ($"p'") ⨟ "y" :≈ PExpr.Bern ($"p'"))
        (bodyPost' (2 * eps * (1 - eps))) := by
  iintro ⟨hp, hx, hy⟩
  iapply wp_seq
  iapply wp_bern_pres "x" ($"p'") X (by intro σ w; simp [Expr.var, Mem.extend])
  isplitl [hp hx]
  · iapply sure_and; isplitl [hp]
    · iapply hp
    · iapply hx
  · iintro ⟨hxb, hp'⟩
    iapply wp_sample_y eps X heps heps' hX hX'
    iframe

/-- The loop body, in the branch where the resource invariant guarantees the value `X` for
the shared bias `p`.  Reading `p` into `p'` both starts the two coin flips and lets the
resource invariant be re-established. -/
lemma wp_body_branch {L : Finset ℚ} {F : ProbSpace → Prop} (eps X : ℚ)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 2) (hXL : X ∈ L) (hX : eps ≤ X) (hX' : X ≤ 1 - eps) :
    iprop(⌈($"p") == Expr.literal X⌉ ∗ (⌈own ($"p'")⌉ ∗ (⌈own ($"x")⌉ ∗ ⌈own ($"y")⌉))) ⊢
      wp_base Inv.emp F ("p'" ::= $"p")
        iprop(wp_base (inv L) F ("x" :≈ PExpr.Bern ($"p'") ⨟ "y" :≈ PExpr.Bern ($"p'"))
            (bodyPost' (2 * eps * (1 - eps))) ∗ ⌈(inv L).to_MProp⌉) := by
  iintro ⟨hp, hpp, hx, hy⟩
  iapply wp_assign_pres "p'" ($"p") _ X (by intro σ w; simp [Expr.var, Mem.extend])
  isplitl [hp hpp]
  · iapply sure_and; isplitl [hp]
    · iapply hp
    · iapply hpp
  · iintro ⟨h1, h2⟩
    isplitl [h1 hx hy]
    · iapply wp_sample_xy eps X heps heps' hX hX'
      iframe
    · irevert h2
      iapply sure_weaken (inv_of_p_eq X hXL)

/-- The loop body, given only the nondeterministic knowledge that `p` holds one of the
admissible biases. -/
lemma wp_body_nondet {L : Finset ℚ} {F : ProbSpace → Prop} (eps : ℚ)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 2) (hL : ∀ v ∈ L, eps ≤ v ∧ v ≤ 1 - eps) :
    iprop((& fun (v : {v : ℚ // v ∈ L}) => ⌈($"p") == Expr.literal v.val⌉) ∗
        (⌈own ($"p'")⌉ ∗ (⌈own ($"x")⌉ ∗ ⌈own ($"y")⌉))) ⊢
      wp_base Inv.emp F ("p'" ::= $"p")
        iprop(wp_base (inv L) F ("x" :≈ PExpr.Bern ($"p'") ⨟ "y" :≈ PExpr.Bern ($"p'"))
            (bodyPost' (2 * eps * (1 - eps))) ∗ ⌈(inv L).to_MProp⌉) := by
  refine Iris.BI.Entails.trans (OProp.nondet_distrib _ _) ?_
  refine Iris.BI.Entails.trans (OProp.nondet_weaken (fun v ↦
    wp_body_branch (F := F) eps v.val heps heps' v.2 (hL v.val v.2).1 (hL v.val v.2).2)) ?_
  exact wp_nsplit2 (Convex.sep_precise (Convex.wp (bodyPost'_convex _)) (Precise.sure _))

/-- The loop invariant at rank `1` provides the ownership of the three variables written by
the loop body. -/
lemma phi1_split : phi1 ⊢ iprop(⌈own ($"p'")⌉ ∗ (⌈own ($"x")⌉ ∗ ⌈own ($"y")⌉)) :=
  Iris.BI.Entails.trans (OProp.sure_weaken phi1_resources)
    (Iris.BI.Entails.trans OProp.sure_sep.1 (Iris.BI.sep_mono_right OProp.sure_sep.1))

/-- **The loop body.**  Starting from the loop invariant at rank `1`, one iteration of the
loop exits with probability at least `2 * eps * (1 - eps)`. -/
lemma wp_body {L : Finset ℚ} (eps : ℚ)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 2) (hL : ∀ v ∈ L, eps ≤ v ∧ v ≤ 1 - eps) :
    phi1 ⊢ wp_weak (inv L) body (bodyPost' (2 * eps * (1 - eps))) := by
  refine Iris.BI.Entails.trans phi1_split ?_
  unfold body wp_weak
  iintro ⟨hpp, hx, hy⟩
  iapply wp_seq
  iapply wp_atom
  iintro hinv
  rw [← wp_weak]
  ihave hinv := sure_weaken (exists_p_of_inv L) $$ hinv
  irevert hinv
  iapply wp_exists (F := fun 𝓟fr ↦ ∀ E, 𝓟fr.mspace.MeasurableSet' E →
    𝓟fr.μ E = 0 ∨ 𝓟fr.μ E = 1)
  iintro hp
  iapply wp_body_nondet eps heps heps' hL
  iframe

/-! ### The loop -/

/-- The loop body, at the only rank at which the loop is entered. -/
lemma wp_body_rank {L : Finset ℚ} (eps : ℚ)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 2) (hL : ∀ v ∈ L, eps ≤ v ∧ v ≤ 1 - eps)
    (r : Set.Icc (0 : ℕ) 1) (hr : (r : ℕ) = 1) :
    loopInv r ⊢ wp_weak (inv L) body (bodyPost (2 * eps * (1 - eps)) r) := by
  have h1 : loopInv r = phi1 := by simp [loopInv, hr]
  rw [h1]
  exact Iris.BI.Entails.trans (wp_body eps heps heps' hL)
    (wp_conseq (bodyPost'_bodyPost _ r hr))

/-- **The loop.**  By the `BoundedRank` rule, the loop terminates almost surely (each
iteration exits with probability at least `2 * eps * (1 - eps) > 0`) in the state described
by the loop invariant at rank `0`, namely `phi0`. -/
lemma wp_loop {L : Finset ℚ} (eps : ℚ)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 2) (hL : ∀ v ∈ L, eps ≤ v ∧ v ≤ 1 - eps) :
    (& loopInv) ⊢ wp (inv L) (while( eqTest ($"x") ($"y") ){ body }) phi0 := by
  have hq : (2 * eps * (1 - eps) : ℚ) > 0 := by nlinarith
  have hexit : loopInv ⟨0, le_refl 0, zero_le_one⟩ ⊢
      ⌈eqTest ($"x") ($"y") == Expr.literal 0⌉ := by
    simpa using loopInv_rank ⟨0, le_refl 0, zero_le_one⟩
  have hloopg : ∀ {r : Set.Icc (0 : ℕ) 1}, r.val > 0 →
      loopInv r ⊢ ⌈eqTest ($"x") ($"y") == Expr.literal 1⌉ := by
    intro r hr
    have hr1 : (r : ℕ) = 1 := le_antisymm r.2.2 hr
    simpa [hr1] using loopInv_rank r
  have hpost : loopInv ⟨0, le_refl 0, zero_le_one⟩ = phi0 := by simp [loopInv]
  have hprec : (loopInv ⟨0, le_refl 0, zero_le_one⟩).Precise := by
    rw [hpost]; exact phi0_precise
  have hrule := wp_bounded_rank (𝓘 := inv L)
      (F := fun 𝓟fr ↦ ∀ E, 𝓟fr.mspace.MeasurableSet' E → 𝓟fr.μ E = 0 ∨ 𝓟fr.μ E = 1)
      (c := body) (zero_le_one) (φ := loopInv) (b := eqTest ($"x") ($"y"))
      (rank := eqTest ($"x") ($"y")) hq loopInv_rank hexit hloopg hprec
  rw [hpost] at hrule
  refine Iris.BI.Entails.trans Iris.BI.emp_sep.2
    (Iris.BI.wand_elim (Iris.BI.Entails.trans ?_ hrule))
  refine Iris.BI.forall_intro fun r ↦ Iris.BI.wand_intro ?_
  refine Iris.BI.Entails.trans Iris.BI.emp_sep.1 (Iris.BI.pure_elim' fun hpos ↦ ?_)
  refine Iris.BI.wand_intro (Iris.BI.Entails.trans Iris.BI.sep_elim_right ?_)
  exact wp_body_rank eps heps heps' hL r (le_antisymm r.2.2 hpos)

/-! ### The initialisation -/

/-- After the two initialising assignments, the two coins agree. -/
lemma xy_zero_eq {P Q : MProp} :
    (iprop(((($"x") == Expr.literal 0) ∧ P) ∧ (((($"y") == Expr.literal 0) ∧ Q) ∧
      own ($"p'"))) : MProp) ⊢ iprop((($"x") == ($"y")) ∧ own ($"p'")) := by
  rintro σ ⟨⟨⟨hs, hx⟩, -⟩, ⟨⟨-, hy⟩, -⟩, hp⟩
  exact ⟨⟨hs, hx.trans hy.symm⟩, hp⟩

/-- After the two initialising assignments, the loop invariant holds (at rank `1`). -/
lemma loopInv_init {P Q : MProp} :
    iprop(⌈(($"x") == Expr.literal 0) ∧ P⌉ ∗
        (⌈(($"y") == Expr.literal 0) ∧ Q⌉ ∗ ⌈own ($"p'")⌉)) ⊢ & loopInv := by
  refine Iris.BI.Entails.trans ?_ (nondet_intro (phi := loopInv) ⟨1, Nat.zero_le 1, le_refl 1⟩)
  have h1 : loopInv ⟨1, Nat.zero_le 1, le_refl 1⟩ = phi1 := by simp [loopInv]
  rw [h1]
  unfold phi1
  refine Iris.BI.Entails.trans ?_ (OProp.sure_weaken (xy_zero_eq (P := P) (Q := Q)))
  exact Iris.BI.Entails.trans (Iris.BI.sep_mono_right sure_and) sure_and

/-! ### The specification of the von Neumann trick -/

/-- **The von Neumann trick** (Section 6.4 of the pcOL paper).  Subject to the resource
invariant that the shared bias `p` always holds one of finitely many values in
`[eps, 1 - eps]`, the program almost surely terminates, and on termination the variable `x`
is distributed like a fair coin flip -- even though the bias `p` may be changed
concurrently by the environment between two iterations. -/
theorem vonNeumann_spec (L : Finset ℚ) (eps : ℚ) (heps : 0 < eps) (heps' : eps ≤ 1 / 2)
    (hL : ∀ v ∈ L, eps ≤ v ∧ v ≤ 1 - eps) :
    inv L ⊢{{ iprop(⌈own ($"x")⌉ ∗ ⌈own ($"y")⌉ ∗ ⌈own ($"p'")⌉) }}
      vonNeumann
    {{ ($"x") ~ Bern 0.5 }} := by
  unfold vonNeumann
  iintro ⟨hx, hy, hpp⟩
  unfold wp
  iapply wp_seq
  iapply wp_assign "x" 0 _ 0
  isplitl [hx]
  · irevert hx; iapply sure_weaken; iintro hx
    isplit
    · intro _ _; exact ⟨rfl, rfl⟩
    · iapply hx
  · iintro hx0
    iapply wp_seq
    iapply wp_assign "y" 0 _ 0
    isplitl [hy]
    · irevert hy; iapply sure_weaken; iintro hy
      isplit
      · intro _ _; exact ⟨rfl, rfl⟩
      · iapply hy
    · iintro hy0
      iapply wp_conseq phi0_fair
      rw [← wp]
      iapply wp_loop eps heps heps' hL
      iapply loopInv_init
      iframe

end VonNeumann

end Pcol
