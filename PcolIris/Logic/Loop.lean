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
