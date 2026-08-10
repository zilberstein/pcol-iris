import PcolIris.Logic.WeakestPre
import PcolIris.OProp.Laws

namespace Pcol

open MProp
open OProp

def Expr.xor (e₁ e₂ : Expr) : Expr :=
  fun σ ↦ do
    let v₁ ← e₁ σ
    let v₂ ← e₂ σ
    pure <| if v₁ = v₂ then 0 else 1


noncomputable def entropy_mixer : Cmd Act :=
  "y" ::= 0 ⨟
  Cmd.par (
    "x₁" ::= $"y" ⨟
    "x₂" :≈ Bern 0.5 ⨟
    "z" ::= Expr.xor ($"x₁") ($"x₂")
  ) (
    "y" ::= 1
  )

def PMF.Bern (q : Rat) : PMF Val := sorry

def 𝓘 : Inv := {
  prop := fun σ ↦ σ.dom = {"y"} ∧ (σ "y" = some 0 ∨ σ "y" = some 1)
  dom := {"y"}
  dom_finite := Set.finite_singleton _
  dom_valid := by intro σ ⟨h, _⟩; exact h
  prop_finite := by
    sorry
}

def φ : OProp := iprop(⌈own ($"y")⌉ ∗ ⌈own ($"x₁")⌉ ∗ ⌈own ($"x₂")⌉ ∗ ⌈own ($"z") ⌉)
def ψ : OProp := ⨁[ PMF.Bern 0.5 ] fun z ↦ ⌈ ($"z") == Expr.literal z ⌉

lemma entropy_mixer_spec :
  Inv.emp ⊢{{ φ }} entropy_mixer {{ ψ }} := by
  unfold φ entropy_mixer
  iintro ⟨hy, hx₁, hx₂, hz⟩; iapply wp_seq
  iapply wp_assign' "y"; iframe; iintro hy
  iapply wp_weaken (φ := iprop(ψ ∗ ⌈ 𝓘.to_MProp ⌉)) (ψ := ψ)
  · iintro ⟨h, _⟩; iapply h
  · iapply wp_share (𝓘 := 𝓘); isplitl [hy]
    · irevert hy; iapply sure_weaken; sorry
    · iapply wp_weaken (φ := iprop(ψ ∗ Iris.BI.BIBase.emp))
      · iintro ⟨h, _⟩; iframe
      · iapply wp_par sorry sorry; isplitl
        · iapply wp_seq; iapply wp_atom
          iintro hinv;
          -- This part is a bit involved and requires nondeterminism
          sorry
        · iapply wp_atom; iintro hinv; iapply wp_assign'
          isplitl
          · sorry
          · sorry

end Pcol
