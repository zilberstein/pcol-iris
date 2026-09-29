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

  sForall p := {
    prop σ := ∀ P, p P → P σ
    upcl := by
      intro σ τ hle h P hP
      exact P.upcl hle (h P hP)
  }
  sExists p := {
    prop σ := ∃ P, p P ∧ P σ
    upcl := by
      rintro σ τ hle ⟨P, hP, hσ⟩
      exact ⟨P, hP, P.upcl hle hσ⟩
  }

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
    prop σ := ∀ σ₁, Disjoint σ.dom σ₁.dom → P σ₁ → Q (σ ⊎ σ₁)
    upcl := by
      intro σ τ hle h σ₁ hd hP
      exact Q.upcl (Mem.union_mono hle (le_refl σ₁) hd)
        (h σ₁ (hd.mono_left (Mem.dom_mono hle)) hP)
  }

  persistently P := {
    prop _ := P Mem.emp
    upcl := fun _ _ _ h ↦ h
  }
  later P := P

instance : Iris.COFE MProp := Iris.COFE.ofDiscrete MProp

instance : Iris.BI MProp where
  toCOFE := inferInstance
  entails_refl := fun _ h ↦ h
  entails_trans := by intro _ _ _ he₁ he₂ σ h; exact he₂ σ <| he₁ σ h
  equiv_iff := by
    intro P Q; constructor
    · rintro rfl; constructor <;> intro _ h <;> exact h
    · intro ⟨h₁, h₂⟩; ext σ; exact ⟨h₁ σ, h₂ σ⟩
  and_ne := ⟨fun _ _ _ h _ _ h' ↦ h ▸ h' ▸ rfl⟩
  or_ne := ⟨fun _ _ _ h _ _ h' ↦ h ▸ h' ▸ rfl⟩
  imp_ne := ⟨fun _ _ _ h _ _ h' ↦ h ▸ h' ▸ rfl⟩
  sForall_ne := fun h ↦ Iris.liftRel_eq.mp h ▸ rfl
  sExists_ne := fun h ↦ Iris.liftRel_eq.mp h ▸ rfl
  sep_ne := ⟨fun _ _ _ h _ _ h' ↦ h ▸ h' ▸ rfl⟩
  wand_ne := ⟨fun _ _ _ h _ _ h' ↦ h ▸ h' ▸ rfl⟩
  persistently_ne := ⟨fun _ _ _ h ↦ h ▸ rfl⟩
  later_ne := ⟨fun _ _ _ h ↦ h ▸ rfl⟩
  pure_intro := by intro p _ hp _ _; exact hp
  pure_elim' := by intro p P h σ hp; exact h hp σ True.intro
  and_elim_l := by intro P Q σ ⟨hP, _⟩; exact hP
  and_elim_r := by intro P Q σ ⟨_, hQ⟩; exact hQ
  and_intro := by intro P Q R h₁ h₂ σ hP; exact ⟨h₁ σ hP, h₂ σ hP⟩
  or_intro_l := by intro P Q σ hP; exact Or.inl hP
  or_intro_r := by intro P Q σ hQ; exact Or.inr hQ
  or_elim := by
    intro P Q R h₁ h₂ σ h
    rcases h with h | h
    · exact h₁ σ h
    · exact h₂ σ h
  imp_intro := by
    intro P Q R h σ hP τ hle hQ
    exact h τ ⟨P.upcl hle hP, hQ⟩
  imp_elim := by
    intro P Q R h σ ⟨hP, hQ⟩
    exact h σ hP σ (le_refl _) hQ
  sForall_intro := by intro P Ψ h σ hP Q hQ; exact h Q hQ σ hP
  sForall_elim := by intro Ψ P hP σ h; exact h P hP
  sExists_intro := by intro Ψ P hP σ h; exact ⟨P, hP, h⟩
  sExists_elim := by intro Φ Q h σ ⟨P, hP, h'⟩; exact h P hP σ h'
  sep_mono := by
    intro P P' Q Q' h₁ h₂ σ ⟨σ₁, σ₂, hd, hle, h₁', h₂'⟩
    exact ⟨σ₁, σ₂, hd, hle, h₁ σ₁ h₁', h₂ σ₂ h₂'⟩
  emp_sep := by
    intro P; constructor
    · rintro σ ⟨σ₁, σ₂, hd, hle, -, h⟩
      exact P.upcl ((Mem.le_union_right hd).trans hle) h
    · intro σ h
      refine ⟨Mem.emp, σ, ?_, le_refl _, trivial, h⟩
      rw [Mem.emp_dom]; exact Set.empty_disjoint _
  sep_symm := by
    rintro P Q σ ⟨σ₁, σ₂, hd, hle, h₁, h₂⟩
    exact ⟨σ₂, σ₁, hd.symm, (Mem.union_comm hd) ▸ hle, h₂, h₁⟩
  sep_assoc_l := by
    rintro P Q R σ ⟨σ₁₂, σ₃, hd, hle, ⟨σ₁, σ₂, hd', hle', h₁, h₂⟩, h₃⟩
    have hsub₁ : σ₁.dom ⊆ σ₁₂.dom := Mem.dom_mono ((Mem.le_union_left σ₁ σ₂).trans hle')
    have hsub₂ : σ₂.dom ⊆ σ₁₂.dom := Mem.dom_mono ((Mem.le_union_right hd').trans hle')
    refine ⟨σ₁, σ₂ ⊎ σ₃, ?_, ?_, h₁, σ₂, σ₃, hd.mono_left hsub₂, le_refl _, h₂, h₃⟩
    · rw [Mem.dom_union]
      exact Set.disjoint_union_right.mpr ⟨hd', hd.mono_left hsub₁⟩
    · rw [← Mem.union_assoc]
      exact (Mem.union_mono hle' (le_refl σ₃) hd).trans hle
  wand_intro := by
    intro P Q R h σ hP σ₁ hd hQ
    exact h _ ⟨σ, σ₁, hd, le_refl _, hP, hQ⟩
  wand_elim := by
    rintro P Q R h σ ⟨σ₁, σ₂, hd, hle, hP, hQ⟩
    exact R.upcl hle (h σ₁ hP σ₂ hd hQ)
  persistently_mono := by intro P Q h _ hP; exact h Mem.emp hP
  persistently_idem_2 := by intro P _ h; exact h
  persistently_emp_2 := by intro _ _; trivial
  persistently_and_2 := by intro P Q _ h; exact h
  persistently_sExists_1 := by
    rintro Ψ σ ⟨P, hP, h⟩
    exact ⟨_, ⟨P, rfl⟩, hP, h⟩
  persistently_absorb_l := by
    rintro P Q σ ⟨_, _, _, _, h, _⟩
    exact h
  persistently_and_l := by
    rintro P Q σ ⟨hP, hQ⟩
    refine ⟨Mem.emp, σ, ?_, le_refl _, hP, hQ⟩
    rw [Mem.emp_dom]; exact Set.empty_disjoint _
  later_mono := fun h ↦ h
  later_intro := fun _ h ↦ h
  later_sForall_2 := by
    intro Φ σ h P hP
    exact h _ ⟨P, rfl⟩ σ (le_refl _) hP
  later_sExists_false := by
    rintro Φ σ ⟨P, hP, h⟩
    exact Or.inr ⟨_, ⟨P, rfl⟩, hP, h⟩
  later_sep := ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  later_persistently := ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  later_false_em := by
    intro P σ h
    exact Or.inr fun _ _ h' ↦ h'.elim

instance : Iris.BI.BIAffine MProp where
  affine := by intro P; constructor; intro _ _; trivial

/-- The upward closure of a predicate on memories: it holds of `σ` if it holds of some
memory below `σ`.  Expressions are arbitrary functions of the memory, so predicates about
their values are only upward closed after taking this closure; for expressions that are
monotone in the memory (`Expr.Mono`), the closure changes nothing (`MProp.upClose_iff`). -/
def upClose (p : Mem → Prop) : MProp where
  prop σ := ∃ τ, τ ≤ σ ∧ p τ
  upcl := fun _ _ hle ⟨τ, hτ, h⟩ ↦ ⟨τ, hτ.trans hle, h⟩

lemma upClose_of {p : Mem → Prop} {σ : Mem} (h : p σ) : upClose p σ :=
  show ∃ τ, τ ≤ σ ∧ p τ from ⟨σ, le_refl σ, h⟩

lemma upClose_iff {p : Mem → Prop} (hp : ∀ {σ τ}, σ ≤ τ → p σ → p τ) {σ : Mem} :
    upClose p σ ↔ p σ :=
  ⟨fun h ↦ let ⟨_, hle, h'⟩ := (show ∃ τ, τ ≤ σ ∧ p τ from h); hp hle h', upClose_of⟩

/-- Ownership of the resources needed to evaluate `e`. -/
def own (e : Expr) : MProp := upClose fun σ ↦ (e σ).isSome

end MProp

namespace Expr

/-- An expression is monotone if extending the memory preserves its value, when it is
defined. -/
def Mono (e : Expr) : Prop := ∀ {σ τ : Mem} {v : Val}, σ ≤ τ → e σ = some v → e τ = some v

def equals (e₁ e₂ : Expr) : MProp := MProp.upClose fun σ ↦ (e₁ σ).isSome ∧ e₁ σ = e₂ σ
infixr:66 " == " => equals

def le (e₁ e₂ : Expr) : MProp := MProp.upClose fun σ ↦
  match e₁ σ, e₂ σ with
  | some v₁, some v₂ => v₁ ≤ v₂
  | _, _ => False
infixr:66 " <= " => le

end Expr

end Pcol
