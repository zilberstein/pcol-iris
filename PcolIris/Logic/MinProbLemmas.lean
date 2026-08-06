/-
General facts about `ConvexPowerset.minProb` that are used in the proof of the
parallel-composition law.  The key ingredient is the multiplicativity law
`ConvexPowerset.minProb_bind` from the ConvexPowerset library.
-/
import ConvexPowerset.MinProb
import ConvexPowerset.Monad.Laws

namespace Pcol

open ConvexPowerset

variable {α β : Type}

/-- Any distribution in `s` bounds `minProb s E` from above. -/
lemma minProb_le_mem {s : ConvexPowerset α} {E : Set α} {μ : Distr α} (hμ : μ ∈ s) :
    minProb s E ≤ ∑' x : E, μ (some (x : α)) :=
  biInf_le _ hμ

lemma minProb_pure_of_notMem {x : α} {E : Set α} (h : x ∉ E) :
    minProb (pure x) E = 0 := by
  refine le_antisymm ?_ bot_le
  refine le_of_le_of_eq (minProb_le_mem (μ := PMF.pure (some x)) rfl) ?_
  refine Eq.trans (tsum_congr (fun y ↦ ?_)) tsum_zero
  refine PMF.pure_apply_of_ne _ _ ?_
  rintro heq
  exact h (Option.some_injective _ heq ▸ y.property)

lemma minProb_pure_of_mem {x : α} {E : Set α} (h : x ∈ E) :
    minProb (pure x) E = 1 := by
  have hval : ∑' y : E, (PMF.pure (some x) : Distr α) (some y) = 1 := by
    refine Eq.trans (tsum_eq_single ⟨x, h⟩ ?_) ?_
    · rintro ⟨y, hy⟩ hne
      refine PMF.pure_apply_of_ne _ _ ?_
      rintro heq
      exact hne (Subtype.ext (Option.some_injective _ heq))
    · exact PMF.pure_apply_self _
  refine le_antisymm ?_ ?_
  · exact le_of_le_of_eq (minProb_le_mem (μ := PMF.pure (some x)) rfl) hval
  · refine le_iInf₂ ?_
    rintro μ (rfl : μ = PMF.pure (some x))
    exact le_of_eq hval.symm

/-- `minProb` of `pure x` is `1` or `0` according to whether `x ∈ E`. -/
lemma minProb_pure (x : α) (E : Set α) [Decidable (x ∈ E)] :
    minProb (pure x) E = if x ∈ E then 1 else 0 := by
  by_cases h : x ∈ E
  · rw [if_pos h, minProb_pure_of_mem h]
  · rw [if_neg h, minProb_pure_of_notMem h]

/-- **Multiplicativity along sequential composition.**  If every outcome in `E₁` is followed by
a continuation that reaches `E₂` with probability at least `q`, then `s >>= f` reaches `E₂`
with probability at least `minProb s E₁ * q`.  This is the consequence of
`ConvexPowerset.minProb_bind` used to combine the two threads of a parallel composition. -/
lemma mul_le_minProb_bind (s : ConvexPowerset α) (f : α → ConvexPowerset β)
    (E₁ : Set α) (E₂ : Set β) (q : ENNReal) (h : ∀ x ∈ E₁, q ≤ minProb (f x) E₂) :
    minProb s E₁ * q ≤ minProb (s >>= f) E₂ := by
  rw [minProb_bind]
  refine le_iInf₂ fun μ hμ ↦ ?_
  rw [tsum_support_weights]
  calc minProb s E₁ * q ≤ (∑' x : E₁, μ (some (x : α))) * q := mul_le_mul' (biInf_le _ hμ) le_rfl
    _ = ∑' x : E₁, μ (some (x : α)) * q := ENNReal.tsum_mul_right.symm
    _ ≤ ∑' x : E₁, μ (some (x : α)) * minProb (f x) E₂ :=
        ENNReal.tsum_le_tsum fun x ↦ mul_le_mul' le_rfl (h x x.2)
    _ ≤ ∑' x : α, μ (some x) * minProb (f x) E₂ := by
        refine le_of_le_of_eq (ENNReal.tsum_mono_subtype
          (fun x ↦ μ (some x) * minProb (f x) E₂) (Set.subset_univ E₁)) ?_
        exact tsum_univ (f := fun x : α ↦ μ (some x) * minProb (f x) E₂)

/-- An element of `α` that can actually be produced by `s`. -/
def Reachable (s : ConvexPowerset α) (x : α) : Prop :=
  ∃ μ ∈ s, WithBot.some x ∈ (μ : Distr α).support

/-- **Comparison of two continuations of the same convex powerset.**  If, for every reachable
outcome `x` of `s`, the continuation `F x` reaches `E` with probability at least
`minProb (G x) E' * c`, then the same bound relates `s >>= F` and `s >>= G`. -/
lemma minProb_bind_mul_mono (s : ConvexPowerset α) (F G : α → ConvexPowerset β)
    (E E' : Set β) (c : ENNReal)
    (h : ∀ x : α, Reachable s x → minProb (G x) E' * c ≤ minProb (F x) E) :
    minProb (s >>= G) E' * c ≤ minProb (s >>= F) E := by
  rw [minProb_bind, minProb_bind]
  refine le_iInf₂ fun μ hμ ↦ ?_
  calc (⨅ ν ∈ s, ∑' x : { x : α | WithBot.some x ∈ ν.support }, ν x * minProb (G x) E') * c
      ≤ (∑' x : { x : α | WithBot.some x ∈ μ.support }, μ x * minProb (G x) E') * c :=
        mul_le_mul' (biInf_le _ hμ) le_rfl
    _ = ∑' x : { x : α | WithBot.some x ∈ μ.support }, (μ x * minProb (G x) E') * c := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∑' x : { x : α | WithBot.some x ∈ μ.support }, μ x * minProb (F x) E := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        rw [mul_assoc]
        exact mul_le_mul' le_rfl (h x ⟨μ, hμ, x.2⟩)

end Pcol
