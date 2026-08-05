import ConvexPowerset.Semantics

namespace Pcol

abbrev Var := String
abbrev Val := ℚ
def Mem : Type := Var → Option Val
abbrev Expr := Mem → Option Val
abbrev PExpr := Mem → Option (PMF Val)

namespace Mem

def extend (σ : Mem) (x : Var) (v : Val) : Mem :=
  fun y ↦ if x = y then v else σ y

def dom (σ : Mem) : Set Var := { x | σ x ≠ none }

open Classical in
noncomputable def restrict (σ : Mem) (X : Set Var) :=
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

def union (σ τ : Mem) : Mem :=
  fun x ↦ match σ x with
  | some v => v
  | none => τ x

end Mem

end Pcol
