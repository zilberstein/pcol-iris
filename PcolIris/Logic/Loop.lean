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
