import PcolIris.Semantics.Semantics

namespace Pcol

open Linearization

@[ext]
structure Inv where
  dom : Set Var
  prop : Mem → Prop
  dom_finite : dom.Finite
  dom_valid : ∀ {σ}, prop σ → σ.dom = dom
  prop_finite : { σ | prop σ }.Finite

namespace Inv

instance : LE Inv where
  le 𝓙 𝓘 :=
    𝓘.dom ⊆ 𝓙.dom ∧
    ∀ {σ}, 𝓘.prop σ ↔ ∃ τ : Mem, σ = τ.restrict 𝓘.dom ∧ 𝓙.prop τ

instance : Preorder Inv where
  le_refl 𝓘 := by
    constructor
    · exact Set.Subset.refl _
    · intro σ; constructor
      · intro h; have hdom := 𝓘.dom_valid h
        exact ⟨σ, hdom.symm ▸ σ.restrict_self.symm, h⟩
      · rintro ⟨τ, rfl, h⟩; have hdom := 𝓘.dom_valid h
        rwa [← hdom, Mem.restrict_self]
  le_trans 𝓘 𝓙 𝓚 hle₁ hle₂ := by
    constructor
    · exact hle₂.1.trans hle₁.1
    · intro σ; rw [hle₂.2]
      conv => lhs; arg 1; ext τ; rw [hle₁.2]
      simp only [↓existsAndEq, true_and, Mem.restrict_restrict,
        Set.inter_eq_self_of_subset_right hle₂.1]

instance : PartialOrder Inv where
  le_antisymm 𝓘 𝓙 hle hge := by
    have heq := Set.Subset.antisymm hge.1 hle.1
    ext1
    · exact heq
    · ext σ; rw [hle.2]; constructor
      · intro h; refine ⟨σ, ?_, h⟩
        rw [← heq, ← 𝓘.dom_valid h, Mem.restrict_self]
      · rintro ⟨σ, rfl, h⟩
        rwa [← heq, ← 𝓘.dom_valid h, Mem.restrict_self]

instance : DCPO Inv where
  dSup d := {
    dom := ⋂ 𝓘 ∈ d, 𝓘.dom
    prop σ :=
      σ.dom = (⋂ 𝓘 ∈ d, 𝓘.dom) ∧
      ∀ 𝓘 ∈ d, ∃ τ, σ = τ.restrict σ.dom ∧ 𝓘.prop τ
    dom_finite := by
      have ⟨𝓘, hd⟩ := d.nonempty
      apply 𝓘.dom_finite.subset; exact Set.biInter_subset_of_mem hd
    dom_valid := by intro σ ⟨hdom, _⟩; exact hdom
    prop_finite := by
      have ⟨𝓘, hd⟩ := d.nonempty
      have := 𝓘.prop_finite; sorry
  }
  lubOfDirected d := by
    constructor
    · intro 𝓘 hd; constructor
      · exact Set.biInter_subset_of_mem hd
      · intro σ; simp only; constructor
        · intro ⟨hdom, hprop⟩; have ⟨τ, heq, h⟩ := hprop _ hd
          refine ⟨τ, ?_, h⟩; rw [heq, hdom]
        · rintro ⟨τ, rfl, hprop⟩; constructor
          · rw [Mem.restrict_dom]; apply Set.inter_eq_self_of_subset_right
            rw [𝓘.dom_valid hprop]; exact Set.biInter_subset_of_mem hd
          · intro 𝓙 h𝓙
            have ⟨𝓚, h𝓚, ⟨hsub₁, hprop₁⟩, hsub₂, hprop₂⟩ := d.directed _ hd _ h𝓙
            have hp𝓚 := hprop₁.mpr ⟨τ, rfl, hprop⟩
            have ⟨ρ, heq, h⟩ := hprop₂.mp hp𝓚
            refine ⟨ρ, ?_, h⟩; rw [Mem.restrict_dom]
            conv =>
              lhs; arg 2;
              exact (Set.biInter_subset_of_mem h𝓚 (t := Inv.dom) |>
                Set.inter_eq_self_of_subset_right).symm
            rw [← Mem.restrict_restrict, heq, Mem.restrict_restrict]
            refine congrArg₂ _ rfl ?_
            rw [Set.inter_eq_self_of_subset_right, Set.inter_eq_self_of_subset_right]
            · rfl
            · rw [𝓘.dom_valid hprop]; exact Set.biInter_subset_of_mem hd
            · exact Set.biInter_subset_of_mem h𝓚
    · intro 𝓘 hup; constructor
      · intro x hx; apply Set.mem_biInter; intro 𝓙 h𝓙
        exact (hup h𝓙).1 hx
      · intro σ
        have ⟨𝓙, h𝓙⟩ := d.nonempty; have ⟨hsub, hprop⟩ := hup h𝓙; constructor
        · intro h; obtain ⟨τ, rfl, hp⟩ := hprop.mp h
          refine ⟨τ.restrict (⋂ 𝓙 ∈ d, 𝓙.dom), ?_, ?_⟩
          · rw [Mem.restrict_restrict]; congr
            symm; apply Set.inter_eq_self_of_subset_right
            apply Set.subset_iInter₂; intro 𝓚 h𝓚; exact (hup h𝓚).1
          · constructor
            · rw [Mem.restrict_dom]; apply Set.inter_eq_self_of_subset_right
              rw [𝓙.dom_valid hp]; exact Set.biInter_subset_of_mem h𝓙
            · intro 𝓚 h𝓚; sorry
        · rintro ⟨τ, rfl, hdom, h⟩
          have ⟨ρ, heq, hp⟩ := h _ h𝓙; refine hprop.mpr ⟨ρ, ?_, hp⟩
          rw [heq, Mem.restrict_restrict]; congr
          apply Set.inter_eq_self_of_subset_right; rw [hdom]
          apply Set.subset_iInter₂; intro 𝓚 h𝓚; exact (hup h𝓚).1



lemma ge_of_subset {𝓘 𝓙 : Inv} (hle : 𝓘 ≤ 𝓙) :
    𝓙.prop = fun σ ↦ ∃ τ : Mem, σ = τ.restrict 𝓙.dom ∧ 𝓘.prop τ := by
  ext σ; rw [hle.2]; rfl

instance : ScottCompact Inv where
  scottCompact 𝓘 := by
    sorry

open Classical in
noncomputable def check (𝓘 : Inv) (σ : Mem) : ConvexPowerset Mem :=
  if 𝓘.prop (σ.restrict 𝓘.dom) then pure σ else ⊥

lemma check_monotone (σ : Mem) : Monotone (check · σ) := by
  intro 𝓘 𝓙 ⟨hsub, hprop⟩; simp only [check]
  by_cases h : 𝓘.prop (σ.restrict 𝓘.dom)
  · rw [if_pos h]
    have h' := hprop.mpr ⟨_, rfl, h⟩
    rw [Mem.restrict_restrict, Set.inter_eq_self_of_subset_right hsub] at h'
    rw [if_pos h']
  · rw [if_neg h]; exact bot_le

open Classical in
noncomputable def replace (𝓘 : Inv) (σ : Mem) : ConvexPowerset Mem :=
  Nondet.nondet fun τ : 𝓘.prop_finite.toFinset ↦
    pure fun x ↦ if x ∈ 𝓘.dom then τ.val x else σ x

lemma replace_monotone (σ : Mem) : Monotone (replace · σ) := by
  intro 𝓘 𝓙 hle; simp only [replace]; sorry

end Inv

@[ext]
structure WithInv (act : Type) where
  action : act
  inv : Inv

instance {act : Type} : PartialOrder (WithInv act) where
  le a₁ a₂ := a₁.action = a₂.action ∧ a₁.inv ≤ a₂.inv
  le_refl a := ⟨rfl, le_refl _⟩
  le_trans a₁ a₂ a₃ hle hle' := ⟨hle.1.trans hle'.1, hle.2.trans hle'.2⟩
  le_antisymm a₁ a₂ hle hle' := by
    ext1
    · exact hle.1
    · exact le_antisymm hle.2 hle'.2

noncomputable instance {act : Type} : DCPO (WithInv act) where
  dSup d := sorry
  lubOfDirected d := sorry

instance {act : Type} : ScottCompact (WithInv act) where
  scottCompact _ := by sorry

noncomputable instance semWithAct {act : Type} [Sem act Mem (ConvexPowerset Mem)] :
    Sem (WithInv act) Mem (ConvexPowerset Mem) where
  sem a σ := do
    let σ ← a.inv.check σ
    let σ ← a.inv.replace σ
    let τ ← Sem.sem a.action σ
    a.inv.check τ

noncomputable instance {act : Type} [Preorder act] [Sem act Mem (ConvexPowerset Mem)] :
    MonoSem (WithInv act) Mem (ConvexPowerset Mem) where
  sem_mono := by
    rintro ⟨a, 𝓘⟩ ⟨_, 𝓙⟩ ⟨rfl, hle⟩ σ
    apply ConvexPowerset.bind_monotone (Inv.check_monotone _ hle)
    intro σ; simp only
    apply ConvexPowerset.bind_monotone (Inv.replace_monotone _ hle)
    intro σ; simp only; apply ConvexPowerset.bind_monotone
    · exact le_refl _
    · intro τ; exact Inv.check_monotone _ hle

namespace Cmd

def withInv {act : Type} (c : Cmd act) (𝓘 : Inv) : Cmd (WithInv act) :=
  match c with
  | skip => skip
  | seq c₁ c₂ => seq (c₁.withInv 𝓘) (c₂.withInv 𝓘)
  | prob e c₁ c₂ => prob e (c₁.withInv 𝓘) (c₂.withInv 𝓘)
  | nd c₁ c₂ => nd (c₁.withInv 𝓘) (c₂.withInv 𝓘)
  | par c₁ c₂ => par (c₁.withInv 𝓘) (c₂.withInv 𝓘)
  | if_stmt e c₁ c₂ => if_stmt e (c₁.withInv 𝓘) (c₂.withInv 𝓘)
  | while_loop e c => while_loop e (c.withInv 𝓘)
  | Cmd.act a => Cmd.act ⟨a, 𝓘⟩

lemma withInv_monotone {act : Type} (c : Cmd act) : Monotone (Cmd.to_pom ∘ c.withInv) := by
  intro 𝓘 𝓙 hle; simp only [Function.comp_apply]; induction c with
  | skip => exact le_refl _
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [withInv, to_pom]; apply Pom.seq_monotone <;> assumption
  | if_stmt _ c₁ c₂ ih₁ ih₂
  | nd c₁ c₂ ih₁ ih₂
  | prob _ c₁ c₂ ih₁ ih₂ =>
    simp only [withInv, to_pom]; apply Pom.guard_monotone _ (le_refl _) <;> assumption
  | par c₁ c₂ ih₁ ih₂ =>
    simp only [withInv, to_pom]; apply Pom.par_monotone <;> assumption
  | while_loop e c ih =>
    simp only [withInv, to_pom]
    apply OmegaCompletePartialOrder.ωSup_le_ωSup_of_le; intro n; use n
    sorry
  | act a =>
    simp only [withInv, to_pom]
    -- This case is easy, but we need to add a lemma to the pomset library
    sorry

end Cmd


end Pcol
