import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

import PcolIris.OProp.MProp
import PcolIris.Semantics.Mem

namespace Pcol

@[ext]
structure ProbSpace : Type where
  mspace : MeasurableSpace ℕ
  μ : @MeasureTheory.ProbabilityMeasure ℕ mspace
  dom : Set Var
  state : ℕ → Mem
  dom_valid : ∀ i, (state i).dom = dom
  complete : @MeasureTheory.NullMeasurableSpace _ mspace μ

namespace ProbSpace



-- The trivial/dirac measure centered on the set `P`
def trivial (P : MProp) : ProbSpace := sorry

noncomputable def product (p : ProbSpace) (q : ProbSpace) : ProbSpace := {
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
  dom := p.dom ∪ q.dom
  dom_valid := by
    intro n; let ⟨i, j⟩ := Nat.pairEquiv.symm n; simp only
    rw [Mem.dom_union, p.dom_valid i, q.dom_valid j]
  complete := sorry
}

infixl:35 " ⊗ " => product

def support (𝓟 : ProbSpace) : Set ℕ :=
  Set.sInter { E | 𝓟.mspace.MeasurableSet' E ∧ 𝓟.μ E = 1 }

def sum {ι : Type} (ξ : PMF ι) (𝓟 : ι → ProbSpace) (V : Set Var)
    (h : ∀ {i j : ι}, i ≠ j → Disjoint (𝓟 i).support (𝓟 j).support)
    (hdom : ∀ i : ι, (𝓟 i).dom = V) :
    ProbSpace := {
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
  dom := V
  dom_valid := sorry
  complete := sorry
}

structure LE_ProbSpace (p q : ProbSpace) : Prop where
  mspace : p.mspace ≤ q.mspace
  μ : ∀ E, p.mspace.MeasurableSet' E → p.μ E = q.μ E
  dom : p.dom ⊆ q.dom
  state : ∀ i, p.state i ≤ q.state i

instance : LE ProbSpace where
  le p q := LE_ProbSpace p q

instance : Preorder ProbSpace where
  le_refl p := by
    constructor
    · exact le_refl _
    · intro _ _; rfl
    · exact Set.Subset.refl _
    · intro _; exact le_refl _
  le_trans p q r hpq hqr := by
    constructor
    · exact hpq.mspace.trans hqr.mspace
    · intro E hE; apply (hpq.μ E hE).trans
      exact hqr.μ E (hpq.mspace E hE)
    · exact hpq.dom.trans hqr.dom
    · intro i; exact (hpq.state i).trans <| hqr.state i

instance : Membership (Set ℕ) ProbSpace where
  mem 𝓟 := 𝓟.mspace.MeasurableSet'

end ProbSpace

namespace Distr

def Refines (ξ : Distr Mem) (𝓟 : ProbSpace) : Prop :=
  ∃ ξ' : PMF ℕ, ∃ f : ℕ → Mem,
    (∀ {E}, E ∈ 𝓟 → 𝓟.μ E = ∑' i : E, ξ' i) ∧
    (∀ i, 𝓟.state i ≤ f i) ∧
    ξ = ξ'.map (some ∘ f)

namespace Refines

lemma bot_0 {ξ : Distr Mem} {p : ProbSpace}
    (h : Distr.Refines ξ p) : ξ ⊥ = 0 := by
    sorry

end Refines

end Distr

notation:30 p " ≼ " ξ => Distr.Refines ξ p

end Pcol
