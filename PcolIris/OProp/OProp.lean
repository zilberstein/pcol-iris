import Iris

import PcolIris.OProp.ProbSpace

namespace Pcol

def OProp := ProbSpace Mem → Prop

abbrev Event := Set Mem

namespace OProp

def hasProb (A : Event) (q : ENNReal) : OProp :=
  fun p ↦
    p.mspace.MeasurableSet' (p.state ⁻¹' A) ∧
    p.μ (p.state ⁻¹' A) = q

instance : Iris.BI.BIBase OProp where
  Entails φ ψ := ∀ m, φ m → ψ m
  emp := hasProb { Mem.emp } 1
  pure p _ := p
  and φ ψ m := φ m ∧ ψ m
  or φ ψ m := φ m ∨ ψ m
  imp φ ψ m := φ m → ψ m
  sForall p m := ∀ φ, p φ → φ m
  sExists p m := ∃ φ, p φ ∧ φ m
  sep φ ψ m :=
    ∃ (m₁ m₂ : ProbSpace Mem), m₁.product m₂ ≤ m ∧ φ m₁ ∧ ψ m₂
  wand φ ψ m := ∀ m₁, φ m₁ → ∃ m₂, m₁.product m₂ ≤ m ∧ ψ m₂
  persistently φ := φ
  later φ := φ

instance : Iris.BI OProp := sorry

def sure (P : Mem → Prop) : OProp :=
  hasProb P 1

def Precise (φ : OProp) : Prop :=
  ∃ 𝓟 : ProbSpace Mem, ∀ 𝓠, 𝓟 ≤ 𝓠 ↔ φ 𝓠

def oplus (ξ : PMF Val) (φ : Val → OProp) : OProp :=
  fun 𝓟 ↦ ∃ 𝓠 h, ProbSpace.sum ξ 𝓠 h ≤ 𝓟 ∧
    ∀ v ∈ ξ.support, φ v (𝓠 v)

notation "⨁[ " ξ " ] " φ => oplus ξ φ

def nondet (S : Set Val) (φ : Val → OProp) : OProp :=
  fun 𝓟 ↦ ∃ ξ : PMF Val, ξ.support ⊆ S ∧ oplus ξ φ 𝓟

notation "&[ " ξ " ] " φ => nondet ξ φ

end OProp

end Pcol
