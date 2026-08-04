import ConvexPowerset.Semantics

namespace Pcol

abbrev Var := String
abbrev Val := ℚ
def Mem := Var → Option Val
abbrev Expr := Mem → Option Val
abbrev PExpr := Mem → Option (PMF Val)

namespace Mem

def extend (σ : Mem) (x : Var) (v : Val) : Mem :=
  fun y ↦ if x = y then v else σ y

def dom (σ : Mem) : Set Var := { x | σ x ≠ none }

open Classical in
noncomputable def restrict (σ : Mem) (X : Set Var) :=
  fun x ↦ if x ∈ X then σ x else none

def emp : Mem := fun _ ↦ none

def union (σ τ : Mem) : Mem :=
  fun x ↦ match σ x with
  | some v => v
  | none => τ x

end Mem

end Pcol
