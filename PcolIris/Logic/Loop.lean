import PcolIris.Semantics.Semantics
import PcolIris.Semantics.Invariant

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
