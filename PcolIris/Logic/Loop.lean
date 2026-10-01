import PcolIris.Semantics.Semantics
import PcolIris.Semantics.Invariant
import ConvexPowerset.MinProb

/-!
# Loops

The semantics of a loop is the least fixpoint of its unrolling, i.e. the limit of the finite
unrollings. In the convex powerdomain, a limit is an intersection, so the outcomes of a loop
are exactly the distributions that are outcomes of every finite unrolling.
-/

namespace Pcol

open OmegaCompletePartialOrder

/-- The `n`-th finite unrolling of a loop with guard `e` and body semantics `f`. -/
noncomputable def loopIter (e : Expr) (f : Mem → ConvexPowerset Mem) (n : ℕ) :
    Mem → ConvexPowerset Mem :=
  (Pom.Semantics.while_sem (Test.lift e) f)^[n] ⊥

lemma mem_while_iff {e : Expr} {c : Cmd Act} {𝓘 : Inv} {μ : Distr Mem} {ν : Distr Mem} :
    ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 ((Cmd.while_loop e c).withInv 𝓘).to_pom ↔
      ∀ n, ν ∈ ConvexPowerset.singleton' μ >>= loopIter e (𝓛 (c.withInv 𝓘).to_pom) n := by
  rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_while]
  let cf : Chain (Mem → ConvexPowerset Mem) :=
    fixedPoints.iterateChain ⟨_, Pom.Semantics.while_sem_monotone (Test.lift e)
      (𝓛 (c.withInv 𝓘).to_pom)⟩ ⊥ bot_le
  have h := ConvexPowerset.bind_continuous (OmegaCompletePartialOrder.const (ConvexPowerset.singleton' μ)) cf
  rw [OmegaCompletePartialOrder.ωSup_const] at h
  change ν ∈ (ConvexPowerset.singleton' μ).bind (ωSup cf) ↔ _
  rw [← h, mem_ωSup]
  rfl

lemma loopIter_zero (e : Expr) (f : Mem → ConvexPowerset Mem) : loopIter e f 0 = ⊥ := rfl

/-- One more unrolling: test the guard, and either run the body and continue, or stop. -/
lemma loopIter_succ (e : Expr) (f : Mem → ConvexPowerset Mem) (n : ℕ) (σ : Mem) :
    loopIter e f (n + 1) σ =
      (Linearization.Sem.sem (Test.lift e) σ : ConvexPowerset Bool) >>= fun r ↦
        bif r then f σ >>= loopIter e f n else pure σ := by
  unfold loopIter
  rw [Function.iterate_succ', Function.comp_apply]
  rfl

/-- An unrolling stops where the guard is false. -/
lemma loopIter_succ_of_false {e : Expr} {σ : Mem} (he : e σ = some 0)
    (f : Mem → ConvexPowerset Mem) (n : ℕ) : loopIter e f (n + 1) σ = pure σ := by
  rw [loopIter_succ]
  have : (Linearization.Sem.sem (Test.lift e) σ : ConvexPowerset Bool) = pure false := by
    change (match e σ with
      | some q => pure (decide (q ≠ 0))
      | none => ⊥ : ConvexPowerset Bool) = _
    rw [he]; norm_num
  rw [this, ConvexPowerset.pure_bind]
  rfl

/-- An unrolling runs the body where the guard is true. -/
lemma loopIter_succ_of_true {e : Expr} {σ : Mem} (he : e σ = some 1)
    (f : Mem → ConvexPowerset Mem) (n : ℕ) :
    loopIter e f (n + 1) σ = f σ >>= loopIter e f n := by
  rw [loopIter_succ]
  have : (Linearization.Sem.sem (Test.lift e) σ : ConvexPowerset Bool) = pure true := by
    change (match e σ with
      | some q => pure (decide (q ≠ 0))
      | none => ⊥ : ConvexPowerset Bool) = _
    rw [he]; norm_num
  rw [this, ConvexPowerset.pure_bind]
  rfl

/-- The finite unrollings increase. -/
lemma loopIter_mono (e : Expr) (f : Mem → ConvexPowerset Mem) :
    Monotone (loopIter e f) := by
  intro m n hmn
  have hf := Pom.Semantics.while_sem_monotone (st := Mem) (t := ConvexPowerset)
    (Test.lift e) f
  exact (fixedPoints.iterateChain ⟨_, hf⟩ ⊥ bot_le).monotone hmn

/-- The probability that the outcome of a loop lies in `E` (counting nontermination as not
lying in `E`) is the limit of the corresponding probabilities for its unrollings. -/
lemma minProb_while {e : Expr} {c : Cmd Act} {𝓘 : Inv} (μ : Distr Mem) (E : Set Mem) :
    ConvexPowerset.minProb
        (ConvexPowerset.singleton' μ >>= 𝓛 ((Cmd.while_loop e c).withInv 𝓘).to_pom) E =
      ⨆ n, ConvexPowerset.minProb
        (ConvexPowerset.singleton' μ >>= loopIter e (𝓛 (c.withInv 𝓘).to_pom) n) E := by
  rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_while]
  let cf : Chain (Mem → ConvexPowerset Mem) :=
    fixedPoints.iterateChain ⟨_, Pom.Semantics.while_sem_monotone (Test.lift e)
      (𝓛 (c.withInv 𝓘).to_pom)⟩ ⊥ bot_le
  have h := ConvexPowerset.bind_continuous (OmegaCompletePartialOrder.const
    (ConvexPowerset.singleton' μ)) cf
  rw [OmegaCompletePartialOrder.ωSup_const] at h
  change ConvexPowerset.minProb ((ConvexPowerset.singleton' μ).bind (ωSup cf)) E = _
  rw [← h, (ConvexPowerset.minProb_ωScottContinuous E).map_ωSup]
  rfl

namespace ConvexPowerset

/-- The divergent computation reaches no event. -/
lemma minProb_bot {α : Type} (E : Set α) : ConvexPowerset.minProb (⊥ : ConvexPowerset α) E = 0 :=
  le_antisymm ((iInf₂_le (PMF.pure ⊥) (Set.mem_univ _)).trans
    (le_of_eq (ConvexPowerset.prob_bot_distr E))) bot_le

open Classical in
lemma apply_of_mem_pure {α : Type} {x : α} {μ : Distr α}
    (h : μ ∈ (pure x : ConvexPowerset α)) (y : α) : μ (some y) = if y = x then 1 else 0 := by
  rw [ConvexPowerset.mem_pure] at h; subst h
  by_cases h : y = x
  · subst h; rw [if_pos rfl]; exact PMF.pure_apply_self _
  · rw [if_neg h]; exact PMF.pure_apply_of_ne _ _ fun h' ↦ h (Option.some_injective _ h')

/-- A terminating deterministic computation reaches the events that contain its result. -/
lemma minProb_pure {α : Type} (x : α) (E : Set α) [Decidable (x ∈ E)] :
    ConvexPowerset.minProb (pure x : ConvexPowerset α) E = if x ∈ E then 1 else 0 := by
  classical
  have hval : ∀ μ ∈ (pure x : ConvexPowerset α),
      ∑' y : E, μ (some (y : α)) = if x ∈ E then 1 else 0 := by
    intro μ hμ
    simp_rw [apply_of_mem_pure hμ]
    split_ifs with h
    · rw [tsum_eq_single (⟨x, h⟩ : E) fun y hy ↦ if_neg fun h' ↦ hy (Subtype.ext h')]
      exact if_pos rfl
    · exact ENNReal.tsum_eq_zero.mpr fun y ↦ if_neg fun (h' : (y : α) = x) ↦ h (h' ▸ y.2)
  have hx : PMF.pure (some x) ∈ (pure x : ConvexPowerset α) := (ConvexPowerset.mem_pure x).mpr rfl
  unfold ConvexPowerset.minProb
  exact le_antisymm ((iInf₂_le _ hx).trans (hval _ hx).le) (le_iInf₂ fun μ hμ ↦ (hval μ hμ).ge)

/-- Running a computation from a fixed initial distribution: the worst case is attained by
resolving the nondeterminism separately in each initial state, so the probability of reaching
`E` is the average of the probabilities from each initial state. -/
lemma minProb_singleton'_bind {α β : Type} (μ : Distr α) (g : α → ConvexPowerset β)
    (E : Set β) :
    ConvexPowerset.minProb (ConvexPowerset.singleton' μ >>= g) E =
      ∑' x : α, μ (some x) * ConvexPowerset.minProb (g x) E := by
  rw [ConvexPowerset.minProb_bind]
  refine le_antisymm ((iInf₂_le μ (ConvexPowerset.self_mem_singleton' μ)).trans
    (le_of_eq (ConvexPowerset.tsum_support_weights μ g E))) (le_iInf₂ fun ν hν ↦ ?_)
  have hle : μ ≤ ν := by
    have h : ν ∈ (ConvexPowerset.singleton' μ).set := hν
    rwa [ConvexPowerset.singleton'_set_eq] at h
  rw [ConvexPowerset.tsum_support_weights]
  exact ENNReal.tsum_le_tsum fun x ↦ mul_le_mul_left (hle x) _

end ConvexPowerset

/-- The probability of reaching `E` in one more unrolling, where the guard is false. -/
lemma minProb_loopIter_succ_of_false {e : Expr} {σ : Mem} (he : e σ = some 0)
    (f : Mem → ConvexPowerset Mem) (n : ℕ) (E : Set Mem) [Decidable (σ ∈ E)] :
    ConvexPowerset.minProb (loopIter e f (n + 1) σ) E = if σ ∈ E then 1 else 0 := by
  rw [loopIter_succ_of_false he, ConvexPowerset.minProb_pure]

/-- The probability of reaching `E` in one more unrolling, where the guard is true: the worst
case, over the outcomes of the body, of the average probability of reaching `E` in the
remaining unrollings. -/
lemma minProb_loopIter_succ_of_true {e : Expr} {σ : Mem} (he : e σ = some 1)
    (f : Mem → ConvexPowerset Mem) (n : ℕ) (E : Set Mem) :
    ConvexPowerset.minProb (loopIter e f (n + 1) σ) E =
      ⨅ μ ∈ f σ, ∑' x : { x : Mem | WithBot.some x ∈ μ.support },
        μ x * ConvexPowerset.minProb (loopIter e f n x) E := by
  rw [loopIter_succ_of_true he, ConvexPowerset.minProb_bind]

section D1

open _root_.ConvexPowerset

/-- The probability of reaching `E` from a distribution, through `g`. -/
noncomputable abbrev avgMin (g : Mem → ConvexPowerset Mem) (ν : Distr Mem) (E : Set Mem) :
    ENNReal :=
  ∑' x : Mem, ν (some x) * minProb (g x) E

lemma minProb_bind_eq_iInf (s : ConvexPowerset Mem) (g : Mem → ConvexPowerset Mem)
    (E : Set Mem) : minProb (s >>= g) E = ⨅ ν : {ν // ν ∈ s}, avgMin g ν E := by
  rw [minProb_bind, iInf_subtype']
  congr 1; funext ν
  exact tsum_support_weights _ _ _

/-- **Lemma D.1, abstractly.**  Suppose that, from every distribution satisfying the loop
invariant `Inv` (where the guard holds), every outcome of the body is a mixture of a
distribution satisfying `Inv` and a terminated one satisfying `Post` (where the guard fails),
and that the terminated distributions all give the event `E` the same probability `q`.  Then,
at every unrolling, the probability of terminating in `E` is the probability of terminating
times `q`. -/
theorem minProb_loopIter_eq_mul {e : Expr} {f : Mem → ConvexPowerset Mem}
    {Inv Post : Distr Mem → Prop} {E : Set Mem} {q : ENNReal} (hq : q ≤ 1)
    (hInv : ∀ μ, Inv μ → ∀ x, μ (some x) ≠ 0 → e x = some 1)
    (hPost : ∀ ν, Post ν → ∀ x, ν (some x) ≠ 0 → e x = some 0)
    (hPostE : ∀ ν, Post ν → ∑' x : Mem, ν (some x) * E.indicator 1 x = q)
    (hPost1 : ∀ ν, Post ν → ∑' x : Mem, ν (some x) = 1)
    (hstep : ∀ μ, Inv μ → ∀ ν ∈ singleton' μ >>= f, ∃ (ν₁ ν₂ : Distr Mem) (t : ENNReal), t ≤ 1 ∧
      Inv ν₁ ∧ Post ν₂ ∧ ∀ x, ν (some x) = t * ν₁ (some x) + (1 - t) * ν₂ (some x)) :
    ∀ n μ, Inv μ →
      avgMin (loopIter e f n) μ E = avgMin (loopIter e f n) μ Set.univ * q := by
  classical
  -- Mixtures
  have hmix : ∀ (g : Mem → ConvexPowerset Mem) {ν ν₁ ν₂ : Distr Mem} {t : ENNReal}
      (_ : ∀ x, ν (some x) = t * ν₁ (some x) + (1 - t) * ν₂ (some x)) (E' : Set Mem),
      avgMin g ν E' = t * avgMin g ν₁ E' + (1 - t) * avgMin g ν₂ E' := by
    intro g ν ν₁ ν₂ t hν E'
    unfold avgMin
    simp_rw [hν, add_mul, mul_assoc]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  -- Terminated distributions
  have hpost : ∀ n ν, Post ν →
      avgMin (loopIter e f n) ν E = avgMin (loopIter e f n) ν Set.univ * q := by
    intro n ν hν
    cases n with
    | zero => simp [avgMin, loopIter_zero, Pcol.ConvexPowerset.minProb_bot]
    | succ k =>
      have h : ∀ (E' : Set Mem), avgMin (loopIter e f (k + 1)) ν E' =
          ∑' x : Mem, ν (some x) * E'.indicator 1 x := fun E' ↦ by
        refine tsum_congr fun x ↦ ?_
        by_cases hx : ν (some x) = 0
        · simp [hx]
        · rw [minProb_loopIter_succ_of_false (hPost ν hν x hx), Set.indicator_apply]
          rfl
      rw [h, h, hPostE ν hν]
      simp [hPost1 ν hν]
  -- One unrolling from the invariant
  have hunroll : ∀ n μ, Inv μ → ∀ E', avgMin (loopIter e f (n + 1)) μ E' =
      ⨅ ν : {ν // ν ∈ singleton' μ >>= f}, avgMin (loopIter e f n) ν E' := by
    intro n μ hμ E'
    have : avgMin (loopIter e f (n + 1)) μ E' =
        minProb (singleton' μ >>= fun x ↦ f x >>= loopIter e f n) E' := by
      rw [Pcol.ConvexPowerset.minProb_singleton'_bind]
      refine tsum_congr fun x ↦ ?_
      by_cases hx : μ (some x) = 0
      · simp [hx]
      · rw [loopIter_succ_of_true (hInv μ hμ x hx)]
    rw [this, ← _root_.ConvexPowerset.bind_assoc, minProb_bind_eq_iInf]
  intro n
  induction n with
  | zero => intro μ _; simp [avgMin, loopIter_zero, Pcol.ConvexPowerset.minProb_bot]
  | succ k ih =>
    intro μ hμ
    rw [hunroll k μ hμ, hunroll k μ hμ]
    have hne : Nonempty {ν // ν ∈ singleton' μ >>= f} := by
      obtain ⟨ν, hν⟩ := (singleton' μ >>= f).nonempty
      exact ⟨⟨ν, hν⟩⟩
    rw [ENNReal.iInf_mul fun h ↦ absurd (h ▸ hq) (by simp)]
    refine iInf_congr fun ⟨ν, hν⟩ ↦ ?_
    obtain ⟨ν₁, ν₂, t, -, h₁, h₂, hdec⟩ := hstep μ hμ ν hν
    rw [hmix _ hdec, hmix _ hdec, ih ν₁ h₁, hpost k ν₂ h₂]
    ring

/-- **Lemma D.2, abstractly.**  Under the hypotheses of `minProb_loopIter_eq_mul`, the
probability that the whole loop terminates in `E` is the probability that it terminates
times `q`. -/
theorem minProb_while_eq_mul {e : Expr} {c : Cmd Act} {𝓘 : Inv}
    {Inv Post : Distr Mem → Prop} {E : Set Mem} {q : ENNReal} (hq : q ≤ 1)
    (hInv : ∀ μ, Inv μ → ∀ x, μ (some x) ≠ 0 → e x = some 1)
    (hPost : ∀ ν, Post ν → ∀ x, ν (some x) ≠ 0 → e x = some 0)
    (hPostE : ∀ ν, Post ν → ∑' x : Mem, ν (some x) * E.indicator 1 x = q)
    (hPost1 : ∀ ν, Post ν → ∑' x : Mem, ν (some x) = 1)
    (hstep : ∀ μ, Inv μ → ∀ ν ∈ singleton' μ >>= 𝓛 (c.withInv 𝓘).to_pom,
      ∃ (ν₁ ν₂ : Distr Mem) (t : ENNReal), t ≤ 1 ∧
      Inv ν₁ ∧ Post ν₂ ∧ ∀ x, ν (some x) = t * ν₁ (some x) + (1 - t) * ν₂ (some x))
    {μ : Distr Mem} (hμ : Inv μ) :
    minProb (singleton' μ >>= 𝓛 ((Cmd.while_loop e c).withInv 𝓘).to_pom) E =
      minProb (singleton' μ >>= 𝓛 ((Cmd.while_loop e c).withInv 𝓘).to_pom) Set.univ * q := by
  rw [minProb_while, minProb_while, ENNReal.iSup_mul]
  refine iSup_congr fun n ↦ ?_
  rw [Pcol.ConvexPowerset.minProb_singleton'_bind, Pcol.ConvexPowerset.minProb_singleton'_bind]
  exact minProb_loopIter_eq_mul hq hInv hPost hPostE hPost1 hstep n μ hμ

end D1

section D3

open _root_.ConvexPowerset

variable {e : Expr} {f : Mem → ConvexPowerset Mem}

lemma sum_some_le_one (μ : Distr Mem) : ∑' x : Mem, μ (some x) ≤ 1 := by
  have := ENNReal.tsum_comp_le_tsum_of_injective (f := fun (x : Mem) ↦ (some x : WithBot Mem))
    (Option.some_injective _) (fun w ↦ (μ : PMF (WithBot Mem)) w)
  exact this.trans (le_of_eq (PMF.tsum_coe _))

lemma minProb_le_one (s : ConvexPowerset Mem) (E : Set Mem) : minProb s E ≤ 1 := by
  obtain ⟨μ, hμ⟩ := s.nonempty
  refine (iInf₂_le μ hμ).trans ?_
  exact (ENNReal.tsum_comp_le_tsum_of_injective (f := fun (x : E) ↦ (x : Mem))
    Subtype.val_injective (fun x ↦ μ (some x))).trans (sum_some_le_one μ)

lemma avgMin_le_one (g : Mem → ConvexPowerset Mem) (ν : Distr Mem) (E : Set Mem) :
    avgMin g ν E ≤ 1 :=
  (ENNReal.tsum_le_tsum fun _ ↦ mul_le_of_le_one_right' (minProb_le_one _ _)).trans
    (sum_some_le_one ν)

lemma avgMin_mix (g : Mem → ConvexPowerset Mem) {ν ν₁ ν₂ : Distr Mem} {t : ENNReal}
    (hν : ∀ x, ν (some x) = t * ν₁ (some x) + (1 - t) * ν₂ (some x)) (E : Set Mem) :
    avgMin g ν E = t * avgMin g ν₁ E + (1 - t) * avgMin g ν₂ E := by
  unfold avgMin
  simp_rw [hν, add_mul, mul_assoc]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

lemma avgMin_loopIter_zero (μ : Distr Mem) (E : Set Mem) :
    avgMin (loopIter e f 0) μ E = 0 := by
  simp [avgMin, loopIter_zero, Pcol.ConvexPowerset.minProb_bot]

/-- From a terminated distribution, every nonempty unrolling terminates. -/
lemma avgMin_loopIter_succ_post {ν : Distr Mem} (hν : ∀ x, ν (some x) ≠ 0 → e x = some 0)
    (h1 : ∑' x : Mem, ν (some x) = 1) (n : ℕ) :
    avgMin (loopIter e f (n + 1)) ν Set.univ = 1 := by
  classical
  rw [← h1]
  refine tsum_congr fun x ↦ ?_
  by_cases hx : ν (some x) = 0
  · simp [hx]
  · rw [minProb_loopIter_succ_of_false (hν x hx), if_pos (Set.mem_univ _), mul_one]

/-- From a distribution where the guard holds, one more unrolling runs the body first. -/
lemma avgMin_loopIter_succ_run {μ : Distr Mem} (hμ : ∀ x, μ (some x) ≠ 0 → e x = some 1)
    (n : ℕ) (E : Set Mem) :
    avgMin (loopIter e f (n + 1)) μ E =
      ⨅ ν : {ν // ν ∈ singleton' μ >>= f}, avgMin (loopIter e f n) ν E := by
  have : avgMin (loopIter e f (n + 1)) μ E =
      minProb (singleton' μ >>= fun x ↦ f x >>= loopIter e f n) E := by
    rw [Pcol.ConvexPowerset.minProb_singleton'_bind]
    refine tsum_congr fun x ↦ ?_
    by_cases hx : μ (some x) = 0
    · simp [hx]
    · rw [loopIter_succ_of_true (hμ x hx)]
  rw [this, ← _root_.ConvexPowerset.bind_assoc, minProb_bind_eq_iInf]

private lemma key (a t m A : ENNReal) (ha : a ≤ 1) (ht : t ≤ 1) (hm : m ≤ 1) (hA : A ≤ 1) :
    (1 - m) * (t * a + (1 - t) * A) + m ≤ t * ((1 - m) * a + m) + (1 - t) := by
  have h1 : ∀ x : ENNReal, x ≤ 1 → x ≠ (⊤ : ENNReal) := fun x hx ↦ ne_top_of_le_ne_top ENNReal.one_ne_top hx
  rw [← ENNReal.toReal_le_toReal (by finiteness [h1 a ha, h1 t ht, h1 m hm, h1 A hA])
    (by finiteness [h1 a ha, h1 t ht, h1 m hm])]
  rw [ENNReal.toReal_add (by finiteness [h1 a ha, h1 t ht, h1 m hm, h1 A hA]) (h1 m hm),
    ENNReal.toReal_add (by finiteness [h1 a ha, h1 t ht, h1 m hm]) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add (by finiteness [h1 a ha, h1 t ht]) (by finiteness [h1 A hA]),
    ENNReal.toReal_add (by finiteness [h1 a ha, h1 m hm]) (h1 m hm),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hm ENNReal.one_ne_top, ENNReal.toReal_sub_of_le ht ENNReal.one_ne_top]
  have ha' := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ha)
  have ht' := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ht)
  have hm' := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hm)
  have hA' := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hA)
  simp only [ENNReal.toReal_one]
  have := ENNReal.toReal_nonneg (a := a); have := ENNReal.toReal_nonneg (a := t)
  have := ENNReal.toReal_nonneg (a := m); have := ENNReal.toReal_nonneg (a := A)
  nlinarith [mul_nonneg (sub_nonneg.mpr ht') (sub_nonneg.mpr hm'),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ht') (sub_nonneg.mpr hm')) (sub_nonneg.mpr hA')]

variable {Inv Post : Distr Mem → Prop}

/-- If every distribution satisfying the invariant terminates within `k` unrollings with
probability at least `m`, then `n` more unrollings turn a termination probability `a` into
at least `(1 - m) * a + m`. -/
theorem avgMin_loopIter_add
    (hInv : ∀ μ, Inv μ → ∀ x, μ (some x) ≠ 0 → e x = some 1)
    (hPost : ∀ ν, Post ν → ∀ x, ν (some x) ≠ 0 → e x = some 0)
    (hPost1 : ∀ ν, Post ν → ∑' x : Mem, ν (some x) = 1)
    (hstep : ∀ μ, Inv μ → ∀ ν ∈ singleton' μ >>= f, ∃ (ν₁ ν₂ : Distr Mem) (t : ENNReal), t ≤ 1 ∧
      Inv ν₁ ∧ Post ν₂ ∧ ∀ x, ν (some x) = t * ν₁ (some x) + (1 - t) * ν₂ (some x))
    {k : ℕ} (hk : 1 ≤ k) {m : ENNReal} (hm : m ≤ 1)
    (hmk : ∀ ν, Inv ν → m ≤ avgMin (loopIter e f k) ν Set.univ) :
    ∀ n μ, Inv μ → (1 - m) * avgMin (loopIter e f n) μ Set.univ + m ≤
      avgMin (loopIter e f (n + k)) μ Set.univ := by
  intro n
  induction n with
  | zero => intro μ hμ; simpa [avgMin_loopIter_zero] using hmk μ hμ
  | succ n ih =>
    intro μ hμ
    obtain ⟨j, hj⟩ : ∃ j, n + k = j + 1 := ⟨n + k - 1, by omega⟩
    rw [show n + 1 + k = (n + k) + 1 by omega, avgMin_loopIter_succ_run (hInv μ hμ),
      avgMin_loopIter_succ_run (hInv μ hμ)]
    refine le_iInf fun ⟨ν, hν⟩ ↦ ?_
    obtain ⟨ν₁, ν₂, t, ht, h₁, h₂, hdec⟩ := hstep μ hμ ν hν
    calc (1 - m) * (⨅ ν : {ν // ν ∈ singleton' μ >>= f},
            avgMin (loopIter e f n) ν Set.univ) + m
        ≤ (1 - m) * avgMin (loopIter e f n) ν Set.univ + m := by
          gcongr; exact iInf_le (fun (ν : {ν // ν ∈ singleton' μ >>= f}) ↦
            avgMin (loopIter e f n) ν Set.univ) ⟨ν, hν⟩
      _ = (1 - m) * (t * avgMin (loopIter e f n) ν₁ Set.univ +
            (1 - t) * avgMin (loopIter e f n) ν₂ Set.univ) + m := by
          rw [avgMin_mix _ hdec]
      _ ≤ t * ((1 - m) * avgMin (loopIter e f n) ν₁ Set.univ + m) + (1 - t) :=
          key _ _ _ _ (avgMin_le_one _ _ _) ht hm (avgMin_le_one _ _ _)
      _ ≤ t * avgMin (loopIter e f (n + k)) ν₁ Set.univ + (1 - t) * 1 := by
          rw [mul_one]; gcongr; exact ih ν₁ h₁
      _ = avgMin (loopIter e f (n + k)) ν Set.univ := by
          rw [avgMin_mix _ hdec, hj, avgMin_loopIter_succ_post (hPost ν₂ h₂) (hPost1 ν₂ h₂), ← hj]

private lemma key2 (x c : ENNReal) (hx : x ≤ 1) (hc : c ≤ 1) :
    1 - x * (1 - c) ≤ x * c + (1 - x) := by
  have h1 : ∀ y : ENNReal, y ≤ 1 → y ≠ (⊤ : ENNReal) :=
    fun y hy ↦ ne_top_of_le_ne_top ENNReal.one_ne_top hy
  have hxc : x * (1 - c) ≤ 1 := mul_le_one' hx tsub_le_self
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness [h1 x hx, h1 c hc]),
    ENNReal.toReal_sub_of_le hxc ENNReal.one_ne_top,
    ENNReal.toReal_add (by finiteness [h1 x hx, h1 c hc]) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hc ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le hx ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one]
  nlinarith

/-- **Corollary D.3 (with a uniform horizon).**  If, from every distribution satisfying the
invariant, the loop terminates within `N` unrollings with probability at least `c > 0`, then
it terminates almost surely. -/
theorem iSup_avgMin_loopIter_eq_one
    (hInv : ∀ μ, Inv μ → ∀ x, μ (some x) ≠ 0 → e x = some 1)
    (hPost : ∀ ν, Post ν → ∀ x, ν (some x) ≠ 0 → e x = some 0)
    (hPost1 : ∀ ν, Post ν → ∑' x : Mem, ν (some x) = 1)
    (hstep : ∀ μ, Inv μ → ∀ ν ∈ singleton' μ >>= f, ∃ (ν₁ ν₂ : Distr Mem) (t : ENNReal), t ≤ 1 ∧
      Inv ν₁ ∧ Post ν₂ ∧ ∀ x, ν (some x) = t * ν₁ (some x) + (1 - t) * ν₂ (some x))
    {N : ℕ} (hN : 1 ≤ N) {c : ENNReal} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcN : ∀ ν, Inv ν → c ≤ avgMin (loopIter e f N) ν Set.univ)
    {μ : Distr Mem} (hμ : Inv μ) :
    ⨆ n, avgMin (loopIter e f n) μ Set.univ = 1 := by
  -- Termination within `(j + 1) * N` unrollings
  have hj : ∀ j : ℕ, ∀ μ, Inv μ →
      1 - (1 - c) ^ (j + 1) ≤ avgMin (loopIter e f ((j + 1) * N)) μ Set.univ := by
    intro j
    induction j with
    | zero =>
      intro μ hμ
      simpa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1] using hcN μ hμ
    | succ j ih =>
      intro μ hμ
      have hx : (1 - c) ^ (j + 1) ≤ 1 := pow_le_one₀ bot_le tsub_le_self
      have hadd := avgMin_loopIter_add hInv hPost hPost1 hstep
        (k := (j + 1) * N) (by nlinarith) (m := 1 - (1 - c) ^ (j + 1)) tsub_le_self ih N μ hμ
      rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hx,
        show N + (j + 1) * N = (j + 1 + 1) * N by ring] at hadd
      refine le_trans ?_ hadd
      rw [pow_succ]
      exact (key2 _ _ hx hc1).trans (by gcongr; exact hcN μ hμ)
  refine le_antisymm (iSup_le fun n ↦ avgMin_le_one _ _ _) ?_
  have hlim : Filter.Tendsto (fun (j : ℕ) ↦ 1 - (1 - c) ^ (j + 1)) Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun (j : ℕ) ↦ (1 - c) ^ (j + 1)) Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc0.ne')).comp
        (Filter.tendsto_add_atTop_nat 1)
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h0 (Or.inl ENNReal.one_ne_top)
  exact le_of_tendsto' hlim fun j ↦ (hj j μ hμ).trans (le_iSup (fun n ↦
    avgMin (loopIter e f n) μ Set.univ) _)

end D3
