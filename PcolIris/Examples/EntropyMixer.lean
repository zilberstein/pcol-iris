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
    "x₂" :≈ PExpr.Bern 0.5 ⨟
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
     -- Any memory satisfying the invariant is determined by the value of `y`, which is
    -- either `0` or `1`; so the set of such memories is the range of a function on `Bool`.
    refine ((Set.toFinite ({0, 1} : Set ℚ)).image fun v ↦ Mem.singleton "y" v).subset ?_
    rintro σ ⟨hdom, hy | hy⟩ <;> sorry
}

def φ : OProp := iprop(⌈own ($"y")⌉ ∗ ⌈own ($"x₁")⌉ ∗ ⌈own ($"x₂")⌉ ∗ ⌈own ($"z") ⌉)
def ψ : OProp := ($"z") ~ PMF.Bern 0.5

/-- If `y` holds a value that is either `0` or `1`, then the memory satisfies the
invariant `𝓘` (which only constrains the variable `y`). -/
lemma inv_of_y_eq (v : Val) (hv : v = 0 ∨ v = 1) :
    ($"y" == Expr.literal v) ⊢ 𝓘.to_MProp := by
  intro σ hσ
  have hy : σ "y" = some v := hσ.2
  have hmem : "y" ∈ 𝓘.dom := rfl
  refine ⟨?_, ?_⟩
  · rw [Mem.restrict_dom]
    refine Set.inter_eq_right.mpr ?_
    rintro x rfl
    exact Mem.mem_dom_iff.mpr (by rw [hy]; exact Option.some_ne_none v)
  · rw [Mem.restrict_apply_of_mem σ hmem, hy]
    rcases hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The invariant `𝓘` guarantees that the variable `y` is allocated. -/
lemma own_y_of_inv : 𝓘.to_MProp ⊢ MProp.own ($"y") := by
  intro σ hσ
  have hmem : "y" ∈ 𝓘.dom := rfl
  have hy := hσ.2
  rw [Mem.restrict_apply_of_mem σ hmem] at hy
  rcases hy with hy | hy <;>
    exact (show (σ "y").isSome = true by rw [hy]; rfl)

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
          iapply wp_assign' "x₁"; iframe hx₁
          iintro heq
          isplitr [hinv]
          · iapply wp_seq
            -- Remaining gap: the sampling command `x₂ :≈ Bern 0.5`.  The logic does not
            -- provide a weakest-precondition rule for `Cmd.act (Act.samp _ _)` yet (only
            -- `wp_assign`/`wp_assign'` for deterministic assignments), and proving one
            -- from the definition of `wp` requires the still undefined `ProbSpace.sum`,
            -- which is what interprets the outcome conjunction `⨁` of `ψ`.  Reasoning
            -- about the subsequent assignment `z ::= x₁ xor x₂` additionally needs to
            -- case on the (nondeterministic) value read into `x₁`.
            sorry
          · iexact hinv
        · iapply wp_atom; iintro hinv; iapply wp_assign'
          isplitl
          · irevert hinv; iapply sure_weaken; exact own_y_of_inv
          · iintro hy1; isplitr
            · itrivial
            · irevert hy1; iapply sure_weaken
              exact inv_of_y_eq _ (Or.inr (by norm_num))

end Pcol
