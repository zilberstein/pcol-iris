import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

import PcolIris.Semantics.Mem

namespace Pcol

structure ProbSpace (α : Type*) where
  mspace : MeasurableSpace ℕ
  μ : @MeasureTheory.ProbabilityMeasure ℕ mspace
  state : ℕ → α

namespace ProbSpace

-- The trivial/dirac measure centered on the set `P`
def trivial (P : Mem → Prop) : ProbSpace Mem := sorry

noncomputable def product (p : ProbSpace Mem) (q : ProbSpace Mem) : ProbSpace Mem := {
  mspace := (p.mspace.prod q.mspace).map Nat.pairEquiv
  μ :=
    @MeasureTheory.ProbabilityMeasure.map _ _
      (p.mspace.prod q.mspace) ((p.mspace.prod q.mspace).map Nat.pairEquiv)
      (@MeasureTheory.ProbabilityMeasure.prod _ p.mspace _ q.mspace p.μ q.μ)
      Nat.pairEquiv
      (by {
        apply @Measurable.aemeasurable _ _
          (p.mspace.prod q.mspace) ((p.mspace.prod q.mspace).map Nat.pairEquiv) _ _
        exact measurable_iff_le_map.mpr fun s a ↦ a
      })
  state k :=
    let ⟨i, j⟩ := Nat.pairEquiv.symm k
    Mem.union (p.state i) (q.state j)
}

infixl:35 " ⊗ " => product

def support {α : Type} (𝓟 : ProbSpace α) : Set ℕ :=
  Set.sInter { E | 𝓟.mspace.MeasurableSet' E ∧ 𝓟.μ E = 1 }

def sum {ι α : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace α)
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support) :
    ProbSpace α := {
  mspace := {
    MeasurableSet' E := ∀ i : ι, (𝓟 i).mspace.MeasurableSet' (E ∩ (𝓟 i).support)
    measurableSet_empty := by
      intro i; rw [Set.empty_inter]; exact (𝓟 i).mspace.measurableSet_empty
    measurableSet_compl :=  by
      intro E hE i; sorry -- Needs completeness
    measurableSet_iUnion := by
      intro f hf i; rw [Set.iUnion_inter]
      apply (𝓟 i).mspace.measurableSet_iUnion; intro n
      exact hf n i
  }
  μ := sorry
  state n := sorry
}

structure LE_ProbSpace {α : Type*} (p q : ProbSpace α) : Prop where
  mspace : p.mspace ≤ q.mspace
  μ : ∀ E, p.mspace.MeasurableSet' E → p.μ E = q.μ E
  state : ∀ i, p.state i = q.state i

instance {α : Type*} : LE (ProbSpace α) where
  le p q := LE_ProbSpace p q

instance {α : Type*} : Preorder (ProbSpace α) where
  le_refl p := ⟨le_refl _, fun _ _ ↦ rfl, fun _ ↦ rfl⟩
  le_trans p q r hpq hqr := by
    constructor
    · exact hpq.mspace.trans hqr.mspace
    · intro E hE; apply (hpq.μ E hE).trans
      exact hqr.μ E (hpq.mspace E hE)
    · intro i; exact (hpq.state i).trans <| hqr.state i

end ProbSpace

namespace Distr

def Refines {α : Type*} (ξ : Distr α) (p : ProbSpace α) : Prop :=
  ∀ {E}, p.mspace.MeasurableSet' E → p.μ E = ∑' i : E, ξ (p.state i)

namespace Refines

lemma bot_0 {α : Type*} {ξ : Distr α} {p : ProbSpace α}
    (h : Distr.Refines ξ p) : ξ ⊥ = 0 := by
    sorry

end Refines

end Distr

notation:30 p " ≼ " ξ => Distr.Refines ξ p

end Pcol
