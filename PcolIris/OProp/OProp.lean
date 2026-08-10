import Iris

import PcolIris.OProp.MProp
import PcolIris.OProp.ProbSpace

namespace Pcol

def OProp := ProbSpace → Prop

abbrev Event := Set Mem

namespace OProp

def sure (P : MProp) : OProp :=
  fun 𝓟 ↦ 𝓟.support ⊆ 𝓟.state ⁻¹' P.prop

notation "⌈" P "⌉" => sure P

def hasProb (A : Event) (q : ENNReal) : OProp :=
  fun (𝓟 : ProbSpace) ↦
    (𝓟.state ⁻¹' A) ∈ 𝓟 ∧
    𝓟.μ (𝓟.state ⁻¹' A) = q

lemma hasProb_q (A : Event) :
    hasProb A 1 = fun 𝓟 ↦ ∀ i ∈ 𝓟.support, 𝓟.state i ∈ A := by
  -- Needs to be a complete probability space, or something
  funext 𝓟; sorry

instance : Iris.BI.BIBase OProp where
  Entails φ ψ := ∀ m, φ m → ψ m
  emp := ⌈ Iris.BI.BIBase.emp  ⌉
  pure p _ := p
  and φ ψ m := φ m ∧ ψ m
  or φ ψ m := φ m ∨ ψ m
  imp φ ψ m := φ m → ψ m
  sForall p m := ∀ φ, p φ → φ m
  sExists p m := ∃ φ, p φ ∧ φ m
  sep φ ψ m :=
    ∃ (m₁ m₂ : ProbSpace),
      Disjoint m₁.dom m₂.dom ∧
      (m₁ ⊗ m₂) ≤ m ∧
      φ m₁ ∧
      ψ m₂
  wand φ ψ m :=
    ∀ m₁, φ m₁ → ∃ m₂, Disjoint m₁.dom m₂.dom ∧ (m₁ ⊗ m₂) ≤ m ∧ ψ m₂
  persistently φ := φ
  later φ := φ

instance : Iris.BI OProp where
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

instance : Iris.BI.BIAffine OProp where
  affine := by
    intro φ; constructor; intro _ _ _ _; trivial

def Precise (φ : OProp) : Prop :=
  ∃ 𝓟 : ProbSpace, ∀ 𝓠, 𝓟 ≤ 𝓠 ↔ φ 𝓠

def oplus (ξ : PMF Val) (φ : Val → OProp) : OProp :=
  fun 𝓟 ↦ ∃ 𝓠 V h hd,
    ProbSpace.sum ξ 𝓠 V h hd ≤ 𝓟 ∧
    ∀ v ∈ ξ.support, φ v (𝓠 v)

notation "⨁[ " ξ " ] " φ => oplus ξ φ

def nondet (S : Set Val) (φ : Val → OProp) : OProp :=
  fun 𝓟 ↦ ∃ ξ : PMF Val, ξ.support ⊆ S ∧ oplus ξ φ 𝓟

notation "&[ " ξ " ] " φ => nondet ξ φ

end OProp

end Pcol
