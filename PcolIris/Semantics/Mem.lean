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

def emp : Mem := fun _ ↦ none

def extend (σ : Mem) (x : Var) (v : Val) : Mem :=
  fun y ↦ if x = y then v else σ y

def singleton (x : Var) (v : Val) : Mem := emp.extend x v

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

/-- The extension order, stated without the `match`. -/
lemma le_iff : σ ≤ τ ↔ ∀ x v, σ x = some v → τ x = some v := by
  constructor
  · intro h x v hx
    have := h x
    rw [hx] at this
    exact this
  · intro h x
    cases hx : σ x with
    | none => trivial
    | some v => exact h x v hx

lemma mem_dom_of_eq_some {v : Val} (h : σ x = some v) : x ∈ σ.dom := by
  rw [mem_dom_iff, h]; simp

/-- The union is monotone, provided that the new variables of the left memory do not clash
with the right memory (the union is left-biased). -/
lemma union_mono {σ' τ' : Mem} (h₁ : σ ≤ σ') (h₂ : τ ≤ τ') (hd : Disjoint σ'.dom τ.dom) :
    (σ ⊎ τ) ≤ (σ' ⊎ τ') := by
  rw [le_iff] at h₁ h₂ ⊢
  intro x v hx
  by_cases hs : x ∈ σ.dom
  · rw [union_apply_of_mem_dom hs] at hx
    have hσ' := h₁ x v hx
    rw [union_apply_of_mem_dom (mem_dom_of_eq_some hσ'), hσ']
  · rw [union_apply_of_notMem_dom hs] at hx
    have hx' : x ∉ σ'.dom := fun hc ↦ Set.disjoint_left.mp hd hc (mem_dom_of_eq_some hx)
    rw [union_apply_of_notMem_dom hx', h₂ x v hx]

/-- The union of memories with disjoint domains is commutative. -/
lemma union_comm (hd : Disjoint σ.dom τ.dom) : (σ ⊎ τ) = (τ ⊎ σ) := by
  funext x
  by_cases hs : x ∈ σ.dom
  · have ht : x ∉ τ.dom := Set.disjoint_left.mp hd hs
    rw [union_apply_of_mem_dom hs, union_apply_of_notMem_dom ht]
  · rw [union_apply_of_notMem_dom hs]
    by_cases ht : x ∈ τ.dom
    · rw [union_apply_of_mem_dom ht]
    · rw [union_apply_of_notMem_dom ht, notMem_dom_iff.mp hs, notMem_dom_iff.mp ht]

lemma dom_mono (h : σ ≤ τ) : σ.dom ⊆ τ.dom := by
  intro x hx
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (mem_dom_iff.mp hx)
  exact mem_dom_of_eq_some ((le_iff.mp h) x v hv)

lemma le_union_left (σ τ : Mem) : σ ≤ (σ ⊎ τ) := by
  rw [le_iff]
  intro x v hx
  rw [union_apply_of_mem_dom (mem_dom_of_eq_some hx), hx]

lemma le_union_right (hd : Disjoint σ.dom τ.dom) : τ ≤ (σ ⊎ τ) := by
  rw [union_comm hd]
  exact le_union_left τ σ

/-- Putting a restriction of a memory in front of the memory itself does not change it. -/
lemma union_restrict_self (σ : Mem) (X : Set Var) : (σ.restrict X ⊎ σ) = σ := by
  funext x
  by_cases hx : x ∈ (σ.restrict X).dom
  · rw [union_apply_of_mem_dom hx]
    have hX : x ∈ X := dom_restrict_subset σ X hx
    exact restrict_apply_of_mem σ hX
  · exact union_apply_of_notMem_dom hx

/-- Restricting commutes with overwriting by a memory that lives inside the restriction. -/
lemma union_restrict_of_subset {τ : Mem} (hτ : τ.dom ⊆ X) (σ : Mem) :
    (τ ⊎ σ.restrict X) = (τ ⊎ σ).restrict X := by
  funext x
  by_cases hτx : x ∈ τ.dom
  · rw [union_apply_of_mem_dom hτx, restrict_apply_of_mem _ (hτ hτx), union_apply_of_mem_dom hτx]
  · rw [union_apply_of_notMem_dom hτx]
    by_cases hx : x ∈ X
    · rw [restrict_apply_of_mem _ hx, restrict_apply_of_mem _ hx, union_apply_of_notMem_dom hτx]
    · rw [restrict_apply_of_notMem _ hx, restrict_apply_of_notMem _ hx]

lemma restrict_le (σ : Mem) (X : Set Var) : σ.restrict X ≤ σ := by
  rw [le_iff]
  intro x v hx
  by_cases h : x ∈ X
  · rwa [restrict_apply_of_mem _ h] at hx
  · rw [restrict_apply_of_notMem _ h] at hx; exact absurd hx (by simp)

lemma union_le {σ₁ σ₂ σ : Mem} (h₁ : σ₁ ≤ σ) (h₂ : σ₂ ≤ σ) : (σ₁ ⊎ σ₂) ≤ σ := by
  rw [le_iff] at h₁ h₂ ⊢
  intro x v hx
  by_cases hs : x ∈ σ₁.dom
  · rw [union_apply_of_mem_dom hs] at hx; exact h₁ x v hx
  · rw [union_apply_of_notMem_dom hs] at hx; exact h₂ x v hx

/-! ### Assignment -/

lemma extend_apply_self (σ : Mem) (x : Var) (v : Val) : σ.extend x v x = some v := if_pos rfl

lemma extend_apply_of_ne {σ : Mem} {x y : Var} (v : Val) (h : x ≠ y) :
    σ.extend x v y = σ y := if_neg h

lemma dom_extend (σ : Mem) (x : Var) (v : Val) : (σ.extend x v).dom = insert x σ.dom := by
  ext y
  by_cases h : x = y
  · subst h; simp [mem_dom_iff, extend_apply_self]
  · rw [Set.mem_insert_iff, mem_dom_iff, mem_dom_iff, extend_apply_of_ne v h]
    exact ⟨Or.inr, fun h' ↦ h'.resolve_left (Ne.symm h)⟩

lemma extend_mono {σ τ : Mem} (h : σ ≤ τ) (x : Var) (v : Val) : σ.extend x v ≤ τ.extend x v := by
  rw [le_iff] at h ⊢
  intro y w hy
  by_cases hxy : x = y
  · subst hxy; rwa [extend_apply_self] at hy ⊢
  · rw [extend_apply_of_ne v hxy] at hy ⊢; exact h y w hy

lemma union_extend (σ τ : Mem) (x : Var) (v : Val) :
    (σ ⊎ τ).extend x v = (σ.extend x v ⊎ τ) := by
  funext y
  by_cases hxy : x = y
  · subst hxy
    rw [extend_apply_self, union_apply_of_mem_dom (by simp [mem_dom_iff, extend_apply_self]),
      extend_apply_self]
  · rw [extend_apply_of_ne v hxy]
    simp only [union, extend_apply_of_ne v hxy]

lemma restrict_extend_of_notMem {σ : Mem} {x : Var} {X : Set Var} (v : Val) (h : x ∉ X) :
    (σ.extend x v).restrict X = σ.restrict X := by
  funext y
  by_cases hy : y ∈ X
  · rw [restrict_apply_of_mem _ hy, restrict_apply_of_mem _ hy,
      extend_apply_of_ne v (fun (hc : x = y) ↦ h (hc ▸ hy))]
  · rw [restrict_apply_of_notMem _ hy, restrict_apply_of_notMem _ hy]

/-- Forgetting a variable and assigning it its old value gives back the memory. -/
lemma extend_restrict_sdiff {σ : Mem} {x : Var} {v : Val} (h : σ x = some v) :
    (σ.restrict (σ.dom \ {x})).extend x v = σ := by
  funext y
  by_cases hxy : x = y
  · subst hxy; rw [extend_apply_self, h]
  · rw [extend_apply_of_ne v hxy]
    by_cases hy : y ∈ σ.dom
    · exact restrict_apply_of_mem _ ⟨hy, Ne.symm hxy⟩
    · rw [restrict_apply_of_notMem _ (fun h' ↦ hy h'.1), notMem_dom_iff.mp hy]

/-- A memory below `m` stays below `τ ⊎ m` if `τ` does not overwrite it. -/
lemma le_union_of_le {σ τ m : Mem} (h : σ ≤ m) (hd : Disjoint τ.dom σ.dom) : σ ≤ (τ ⊎ m) := by
  rw [le_iff] at h ⊢
  intro y w hy
  rw [union_apply_of_notMem_dom (fun hy' ↦ Set.disjoint_left.mp hd hy' (mem_dom_of_eq_some hy))]
  exact h y w hy

/-- A memory below `τ` that lives inside `X` is below the restriction of `τ` to `X`. -/
lemma le_restrict {σ τ : Mem} {X : Set Var} (h : σ ≤ τ) (hX : σ.dom ⊆ X) :
    σ ≤ τ.restrict X := by
  rw [le_iff] at h ⊢
  intro x v hx
  rw [restrict_apply_of_mem _ (hX (mem_dom_of_eq_some hx))]
  exact h x v hx

end Mem

end Pcol
