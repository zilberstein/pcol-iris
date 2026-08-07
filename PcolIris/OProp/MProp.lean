import Iris

import PcolIris.Semantics.Mem

namespace Pcol

@[ext]
structure MProp where
  prop : Mem → Prop
  upcl : IsUpperSet prop

namespace MProp

def Sat (P : MProp) : Prop :=
  ∃ σ, P.prop σ

instance : FunLike MProp Mem Prop where
  coe P := P.prop
  coe_injective := by intro P Q heq; ext1; exact heq

-- The Domain of an `MProp` `P` is the set of variables
-- that are contained in a minimal `Mem` that satisfies `P`
def dom (P : MProp) : Set Var :=
  { x : Var
  | ∃ σ : Mem,
      x ∈ σ.dom ∧
      P σ ∧
      ∀ τ, P τ → σ ≤ τ
  }

instance : Iris.BI.BIBase MProp where
  Entails P Q := ∀ σ, P σ → Q σ

  emp := {
    prop _ := True
    upcl := by intro _ _ _ _; trivial
  }

  pure p := {
    prop _ := p
    upcl _ _ _ p := p
  }

  and P Q := {
    prop σ := P σ ∧ Q σ
    upcl := by
      intro σ τ hle ⟨hP, hQ⟩
      exact ⟨P.upcl hle hP, Q.upcl hle hQ⟩
  }

  or P Q := {
    prop σ := P σ ∨ Q σ
    upcl := by
      rintro σ τ hle (hP | hQ)
      · left; exact P.upcl hle hP
      · right; exact Q.upcl hle hQ
  }

  imp P Q := {
    prop σ := ∀ τ ≥ σ, P τ → Q τ
    upcl := by
      intro σ τ hle himp ρ hle' hP
      exact himp ρ (hle.trans hle') hP
  }

  sForall p := sorry
  sExists p := sorry

  sep P Q := {
    prop σ :=
      ∃ (σ₁ σ₂ : Mem),
        Disjoint σ₁.dom σ₂.dom ∧
        (σ₁ ⊎ σ₂) ≤ σ ∧ P σ₁ ∧ Q σ₂
    upcl := by
      intro σ τ hle ⟨σ₁, σ₂, hdisj, hle', hP, hQ⟩
      exact ⟨σ₁, σ₂, hdisj, hle'.trans hle, hP, hQ⟩
  }
  wand P Q := {
    prop σ := ∀ σ₁, P σ₁ → ∃ σ₂, Disjoint σ₁.dom σ₂.dom ∧ (σ₁ ⊎ σ₂) ≤ σ ∧ Q σ
    upcl := by
      intro σ τ hle h σ₁ hP; have ⟨σ₂, hdisj, hle', hQ⟩ := h σ₁ hP
      refine ⟨σ₂, hdisj, hle'.trans hle, ?_⟩; exact Q.upcl hle hQ
  }

  persistently P := P
  later P := P

instance : Iris.BI MProp where
  toCOFE := sorry
  entails_refl := sorry
  entails_trans := sorry
  equiv_iff := sorry
  and_ne := sorry
  or_ne := sorry
  imp_ne := sorry
  sForall_ne := sorry
  sExists_ne := sorry
  sep_ne := sorry
  wand_ne := sorry
  persistently_ne := sorry
  later_ne := sorry
  pure_intro := sorry
  pure_elim' := sorry
  and_elim_l := sorry
  and_elim_r := sorry
  and_intro := sorry
  or_intro_l := sorry
  or_intro_r := sorry
  or_elim := sorry
  imp_intro := sorry
  imp_elim := sorry
  sForall_intro := sorry
  sForall_elim := sorry
  sExists_intro := sorry
  sExists_elim := sorry
  sep_mono := sorry
  emp_sep := sorry
  sep_symm := sorry
  sep_assoc_l := sorry
  wand_intro := sorry
  wand_elim := sorry
  persistently_mono := sorry
  persistently_idem_2 := sorry
  persistently_emp_2 := sorry
  persistently_and_2 := sorry
  persistently_sExists_1 := sorry
  persistently_absorb_l := sorry
  persistently_and_l := sorry
  later_mono := sorry
  later_intro := sorry
  later_sForall_2 := sorry
  later_sExists_false := sorry
  later_sep := sorry
  later_persistently := sorry
  later_false_em := sorry

def own (e : Expr) : MProp := {
  prop σ := (e σ).isSome
  upcl := sorry
}

end MProp

end Pcol
