import ConvexPowerset
import ConvexPowerset.Monad.Laws
import Pom.Semantics

import PcolIris.Semantics.Syntax

namespace Equiv

noncomputable def pmf {α β : Type} (e : α ≃ β) : PMF α ≃ PMF β := {
    toFun := PMF.map e
    invFun := PMF.map e.symm
    left_inv μ := by simp [PMF.map_comp, PMF.map_id]
    right_inv μ := by simp [PMF.map_comp, PMF.map_id]
  }

end Equiv

namespace Pcol

structure Inv where
  dom : Set Var
  prop : Mem → Prop
  dom_valid : ∀ {σ}, prop σ → σ.dom = dom
  prop_finite : { σ | prop σ }.Finite

open Linearization

open Classical in
noncomputable instance {α : Type} : Nondet (ConvexPowerset α) where
  nondet {ι} _ f := if _ : Nonempty ι then ConvexPowerset.nondet f else ⊥
  nondet_congr {ι κ} _ _ f g e heq := by
    subst heq; refine dite_congr ?_ ?_ (fun _ ↦ rfl)
    · ext; exact e.nonempty_congr
    · intro _; ext μ; have _ := e.nonempty
      conv => lhs; exact ConvexPowerset.mem_nondet |> iff_iff_eq.mp
      conv => rhs; exact ConvexPowerset.mem_nondet |> iff_iff_eq.mp
      refine e.pmf.exists_congr ?_; intro ξ
      refine (e.arrowCongr (Equiv.refl _)).exists_congr ?_
      intro k; refine and_congr ?_ ?_
      · simp only [Set.mem_pi, PMF.mem_support_iff, ne_eq, Function.comp_apply,
          Equiv.arrowCongr_apply, Equiv.coe_refl, id_eq]
        refine e.forall_congr fun i ↦ imp_congr ?_ ?_
        · simp only [Equiv.pmf, Equiv.coe_fn_mk, PMF.map_apply, EmbeddingLike.apply_eq_iff_eq,
            tsum_ite_eq']
        · simp only [Equiv.symm_apply_apply]
      · refine Eq.congr rfl ?_; ext x
        conv => lhs; exact PMF.bind_apply _ _ _
        conv => rhs; exact PMF.bind_apply _ _ _
        refine Eq.trans (tsum_congr ?_) (e.tsum_eq _)
        intro i; simp only [Equiv.pmf, Equiv.coe_fn_mk, PMF.map_apply,
          EmbeddingLike.apply_eq_iff_eq, tsum_ite_eq', Equiv.arrowCongr_apply, Equiv.coe_refl,
          Function.comp_apply, Equiv.symm_apply_apply, id_eq]
  nondet_singleton {ι _ f} := by
    conv => lhs; exact dif_pos instNonemptyOfInhabited
    ext μ; conv => lhs; exact ConvexPowerset.mem_nondet |> iff_iff_eq.mp
    constructor
    · rintro ⟨ξ, k, hk, rfl⟩
      have heq : ξ = pure default := by
        ext x; rw [Unique.uniq _ x]; refine Eq.trans ?_ (PMF.pure_apply_self default).symm
        refine (tsum_eq_single _ ?_).symm.trans ξ.property.tsum_eq
        intro x h; exfalso; apply h; exact Unique.uniq _ x
      subst heq; conv => rhs; exact PMF.pure_bind _ _
      refine Set.mem_pi.mp hk default ?_
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    · intro h; refine ⟨pure default, fun _ ↦ μ, ?_, ?_⟩
      · simp only [Set.mem_pi, PMF.mem_support_iff, ne_eq, Function.comp_apply]
        intro x _; rwa [Unique.uniq _ x]
      · symm; exact PMF.pure_bind _ _

instance : ContinuousMonad ConvexPowerset where
  bind_mono := ConvexPowerset.bind_monotone
  bind_continuous := (ConvexPowerset.bind_continuous _ _).symm
  bind_strict := by
    intro α β f; ext μ; constructor
    · intro _; exact Set.mem_univ _
    · intro _; refine (⊥ >>= f).upcl bot_le ?_
      refine (Set.mem_image _ _ _).mpr ⟨⟨(⊥ : Distr α), fun _ ↦ (⊥ : Distr β)⟩, ?_, ?_⟩
      · apply Set.mem_biUnion (Set.mem_univ ⊥)
        refine Set.mem_prod.mpr ⟨Set.mem_singleton _, ?_⟩
        apply Set.mem_pi.mpr; intro x hx
        rcases (PMF.mem_support_pure_iff _ _).mp hx with rfl
        simp only [Option.elim, Set.mem_univ]
      · simp only [Function.uncurry, PMF.bind_const]

open OmegaCompletePartialOrder

lemma nondet_mono {ι α : Type} [Finite ι] : Monotone (@Nondet.nondet (ConvexPowerset α) _ ι _) := by
  intro _ _ hle
  by_cases hne : Nonempty ι <;> simp only [Nondet.nondet, hne, ↓reduceDIte]
  · exact ConvexPowerset.nondet_monotone hle
  · exact le_refl _

noncomputable instance {α : Type} : Linearizable ConvexPowerset α where
  nondet_mono hle := nondet_mono hle
  nondet_continuous := by
    intro ι _; by_cases hne : Nonempty ι <;>
      simp only [Nondet.nondet, hne, ↓reduceDIte]
    · exact ConvexPowerset.nondet_continuous
    · exact ωScottContinuous.fun_const
  bind_additive {ι} _ κ f := by
    by_cases hne : Nonempty ι <;> simp only [Nondet.nondet, hne, ↓reduceDIte]
    · exact bind_assoc _ _ _
    · exact ContinuousMonad.bind_strict

instance : PartialOrder Act where
  le a a' := a = a'
  le_refl a := rfl
  le_trans _ _ _ hle₁ hle₂ := hle₁.trans hle₂
  le_antisymm _ _ hle _ := hle

noncomputable instance : DCPO Act where
  dSup d := d.nonempty.choose
  lubOfDirected d := by
    constructor
    · intro a ha
      obtain ⟨_, _, rfl, rfl⟩ := d.directed a ha _ d.nonempty.choose_spec
      rfl
    · intro a ha; exact ha d.nonempty.choose_spec

instance : ScottCompact Act where
  scottCompact _ := by
    rintro d rfl; have ⟨a, ha⟩ := d.nonempty
    refine ⟨a, ha, ?_⟩; exact (d.le_dSup ha).symm


inductive Test : Type where
| lift : Expr → Test
| nd : Test
| prob : Expr → Test

instance : PartialOrder Test where
  le b b' := b = b'
  le_refl a := rfl
  le_trans _ _ _ hle₁ hle₂ := hle₁.trans hle₂
  le_antisymm _ _ hle _ := hle

noncomputable instance : DCPO Test where
  dSup d := d.nonempty.choose
  lubOfDirected d := by
    constructor
    · intro b hb
      obtain ⟨_, _, rfl, rfl⟩ := d.directed b hb _ d.nonempty.choose_spec
      rfl
    · intro b hb; exact hb d.nonempty.choose_spec

instance : ScottCompact Test where
  scottCompact _ := by
    rintro d rfl; have ⟨b, hb⟩ := d.nonempty
    refine ⟨b, hb, ?_⟩; exact (d.le_dSup hb).symm

end Pcol
