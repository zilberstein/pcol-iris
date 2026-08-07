import ConvexPowerset.Semantics

namespace Pcol

abbrev Var := String
abbrev Val := ℚ
def Mem : Type := Var → Option Val
abbrev Expr := Mem → Option Val
abbrev PExpr := Mem → Option (PMF Val)

namespace Mem

instance : LE Mem where
  le σ τ := ∀ x, match σ x with
  | none => True
  | some v => τ x = some v

instance : Preorder Mem where
  le_refl σ x := by cases σ x <;> trivial
  le_trans σ τ ρ hle₁ hle₂ x := by
    cases h : σ x
    · trivial
    · simp only; have hx := h ▸ hle₁ x
      have := hx ▸ hle₂ x; exact this

instance : PartialOrder Mem where
  le_antisymm σ τ hle hle' := by
    funext x; specialize hle x; specialize hle' x
    cases h : σ x <;> rw [h] at hle hle'
    · cases h' : τ x
      · trivial
      · rw [h'] at hle'; contradiction
    · symm; exact hle

def extend (σ : Mem) (x : Var) (v : Val) : Mem :=
  fun y ↦ if x = y then v else σ y

def dom (σ : Mem) : Set Var := { x | σ x ≠ none }

open Classical in
noncomputable def restrict (σ : Mem) (X : Set Var) : Mem:=
  fun x ↦ if x ∈ X then σ x else none

lemma restrict_dom (σ : Mem) (X : Set Var) : Mem.dom (σ.restrict X) = σ.dom ∩ X := by
  ext x; unfold dom restrict
  by_cases hX : x ∈ X <;>
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, Set.mem_setOf_eq,
      hX, true_and, Set.mem_inter_iff, and_true, false_and, and_false]

lemma restrict_self (σ : Mem) : σ.restrict σ.dom = σ := by
  funext x
  simp only [restrict, dom, ne_eq, Set.mem_setOf_eq, Classical.ite_not, ite_eq_right_iff]
  intro h; exact h.symm

lemma restrict_restrict (σ : Mem) (X Y : Set Var) :
    Mem.restrict (σ.restrict X) Y = σ.restrict (X ∩ Y) := by
  funext x; simp only [restrict, Set.mem_inter_iff]
  by_cases hY : x ∈ Y <;> by_cases hX : x ∈ X <;>
    simp only [hY, ↓reduceIte, hX, Set.mem_inter_iff, and_self, and_true, and_false]

def emp : Mem := fun _ ↦ none

/-- Left-biased union of memories. This operation does not
require separation-logic style disjointness, that is enforced at the
logical level.
-/
def union (σ τ : Mem) : Mem :=
  fun x ↦ match σ x with
  | some v => v
  | none => τ x

infixl:40 " ⊎ " => union

/-
Elementary algebra of memories: `Mem.union`, `Mem.restrict` and `Mem.dom`.

These lemmas are the bookkeeping used by the frame reasoning in the parallel-composition
law: a global memory is split into the part owned by the first thread, the part owned by the
second thread, and the part governed by the invariant.
-/

variable {σ τ ρ : Mem} {x : Var} {X Y : Set Var}

def sep (A B : Set Mem) : Set Mem :=
    { σ | ∃ σ₁ ∈ A, ∃ σ₂ ∈ B, σ = σ₁.union σ₂ }

lemma mem_dom_iff : x ∈ σ.dom ↔ σ x ≠ none := Iff.rfl

lemma notMem_dom_iff : x ∉ σ.dom ↔ σ x = none := by
  rw [mem_dom_iff, ne_eq, Decidable.not_not]

lemma emp_dom : Mem.emp.dom = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx rfl

lemma union_emp (σ : Mem) : σ.union Mem.emp = σ := by
  funext x; simp only [Mem.union, Mem.emp]; cases h : σ x <;> rfl

lemma emp_union (σ : Mem) : Mem.emp.union σ = σ := rfl

lemma union_apply_of_mem_dom (h : x ∈ σ.dom) : (σ.union τ) x = σ x := by
  simp only [Mem.union]
  cases hx : σ x with
  | none => exact absurd hx (mem_dom_iff.mp h)
  | some v => rfl

lemma union_apply_of_notMem_dom (h : x ∉ σ.dom) : (σ.union τ) x = τ x := by
  simp only [Mem.union, notMem_dom_iff.mp h]

lemma union_assoc (σ τ ρ : Mem) : (σ.union τ).union ρ = σ.union (τ.union ρ) := by
  funext x
  simp only [Mem.union]
  cases σ x <;> rfl

lemma dom_union (σ τ : Mem) : (σ.union τ).dom = σ.dom ∪ τ.dom := by
  ext x
  simp only [Mem.dom, Mem.union, ne_eq, Set.mem_setOf_eq, Set.mem_union]
  cases h : σ x with
  | none => simp
  | some v => simp

lemma restrict_apply_of_mem (σ : Mem) (h : x ∈ X) : σ.restrict X x = σ x := if_pos h

lemma restrict_apply_of_notMem (σ : Mem) (h : x ∉ X) : σ.restrict X x = none := if_neg h

/-- Restriction distributes over union. -/
lemma restrict_union (σ τ : Mem) (X : Set Var) :
    Mem.restrict (σ.union τ) X = Mem.union (σ.restrict X) (τ.restrict X) := by
  funext x
  by_cases hx : x ∈ X
  · rw [restrict_apply_of_mem _ hx]
    show _ = Mem.union (Mem.restrict σ X) (Mem.restrict τ X) x
    simp only [Mem.union, restrict_apply_of_mem _ hx]
  · rw [restrict_apply_of_notMem _ hx]
    show _ = Mem.union (Mem.restrict σ X) (Mem.restrict τ X) x
    simp only [Mem.union, restrict_apply_of_notMem _ hx]

/-- A memory whose domain is disjoint from `X` restricts to the empty memory. -/
lemma restrict_eq_emp (h : Disjoint σ.dom X) : σ.restrict X = Mem.emp := by
  funext x
  by_cases hx : x ∈ X
  · rw [restrict_apply_of_mem _ hx]
    exact notMem_dom_iff.mp fun hc ↦ Set.disjoint_left.mp h hc hx
  · exact restrict_apply_of_notMem _ hx

/-- A memory contained in `X` is unchanged by restriction to `X`. -/
lemma restrict_eq_self (h : σ.dom ⊆ X) : σ.restrict X = σ := by
  funext x
  by_cases hx : x ∈ X
  · exact restrict_apply_of_mem _ hx
  · rw [restrict_apply_of_notMem _ hx]
    exact (notMem_dom_iff.mp fun hc ↦ hx (h hc)).symm

/-- Splitting a memory into two restrictions covering its domain. -/
lemma union_restrict_restrict (h : σ.dom ⊆ X ∪ Y) :
    Mem.union (σ.restrict X) (σ.restrict Y) = σ := by
  funext x
  show Mem.union (Mem.restrict σ X) (Mem.restrict σ Y) x = σ x
  by_cases hx : x ∈ X
  · simp only [Mem.union, restrict_apply_of_mem _ hx]
    cases hv : σ x with
    | none =>
      by_cases hy : x ∈ Y
      · rw [restrict_apply_of_mem _ hy, hv]
      · rw [restrict_apply_of_notMem _ hy]
    | some v => rfl
  · simp only [Mem.union, restrict_apply_of_notMem _ hx]
    by_cases hy : x ∈ Y
    · exact restrict_apply_of_mem _ hy
    · rw [restrict_apply_of_notMem _ hy]
      refine (notMem_dom_iff.mp fun hc ↦ ?_).symm
      rcases h hc with h' | h'
      · exact hx h'
      · exact hy h'

/-- The restriction of a union to a set on which the left memory is total. -/
lemma restrict_union_left (h : σ.dom = X) (τ : Mem) : Mem.restrict (σ.union τ) X = σ := by
  funext x
  by_cases hx : x ∈ X
  · rw [restrict_apply_of_mem _ hx]
    exact union_apply_of_mem_dom (h ▸ hx)
  · rw [restrict_apply_of_notMem _ hx]
    exact (notMem_dom_iff.mp (h ▸ hx)).symm

/-- Restricting to `Y` a memory that lives inside `X` only sees `X ∩ Y`. -/
lemma restrict_of_dom_subset (h : σ.dom ⊆ X) (Y : Set Var) :
    σ.restrict Y = σ.restrict (X ∩ Y) := by
  conv_lhs => rw [← restrict_eq_self h]
  rw [Mem.restrict_restrict]

/-- If `σ` is defined on all of `X`, the restriction of `σ.union τ` to `X` does not see `τ`. -/
lemma restrict_union_of_subset_dom (h : X ⊆ σ.dom) (τ : Mem) :
    Mem.restrict (σ.union τ) X = σ.restrict X := by
  funext x
  by_cases hx : x ∈ X
  · rw [restrict_apply_of_mem _ hx, restrict_apply_of_mem _ hx, union_apply_of_mem_dom (h hx)]
  · rw [restrict_apply_of_notMem _ hx, restrict_apply_of_notMem _ hx]

/-- Two memories that agree outside the domain of `σ` give the same union with `σ`. -/
lemma union_congr_right (h : ∀ x ∉ σ.dom, τ x = ρ x) : σ.union τ = σ.union ρ := by
  funext x
  by_cases hx : x ∈ σ.dom
  · rw [union_apply_of_mem_dom hx, union_apply_of_mem_dom hx]
  · rw [union_apply_of_notMem_dom hx, union_apply_of_notMem_dom hx, h x hx]

/-- Two restrictions of the same memory glue back to the restriction to the union. -/
lemma restrict_union_restrict (σ : Mem) (X Y : Set Var) :
    Mem.union (σ.restrict X) (σ.restrict Y) = σ.restrict (X ∪ Y) := by
  funext x
  show Mem.union (Mem.restrict σ X) (Mem.restrict σ Y) x = Mem.restrict σ (X ∪ Y) x
  by_cases hx : x ∈ X
  · rw [restrict_apply_of_mem σ (Set.mem_union_left Y hx)]
    simp only [Mem.union, restrict_apply_of_mem σ hx]
    cases h : σ x with
    | none =>
      by_cases hy : x ∈ Y
      · rw [restrict_apply_of_mem σ hy, h]
      · rw [restrict_apply_of_notMem σ hy]
    | some v => rfl
  · simp only [Mem.union, restrict_apply_of_notMem σ hx]
    by_cases hy : x ∈ Y
    · rw [restrict_apply_of_mem σ hy, restrict_apply_of_mem σ (Set.mem_union_right X hy)]
    · rw [restrict_apply_of_notMem σ hy,
        restrict_apply_of_notMem σ (fun hc ↦ hc.elim hx hy)]

/-- If the domain of `σ` misses `X`, the restriction of `σ.union τ` to `X` does not see `σ`. -/
lemma restrict_union_of_disjoint (h : Disjoint σ.dom X) (τ : Mem) :
    Mem.restrict (σ.union τ) X = τ.restrict X := by
  funext x
  by_cases hx : x ∈ X
  · rw [restrict_apply_of_mem _ hx, restrict_apply_of_mem _ hx]
    exact union_apply_of_notMem_dom (fun hc ↦ Set.disjoint_left.mp h hc hx)
  · rw [restrict_apply_of_notMem _ hx, restrict_apply_of_notMem _ hx]

lemma dom_restrict_subset (σ : Mem) (X : Set Var) : Mem.dom (σ.restrict X) ⊆ X := by
  intro x hx
  by_contra hc
  exact (mem_dom_iff.mp hx) (restrict_apply_of_notMem _ hc)

end Mem

end Pcol
