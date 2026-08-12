import PcolIris.Logic.WeakestPre
import PcolIris.OProp.Laws

namespace Pcol

open MProp
open OProp

/-- A memory whose domain is the single variable `x`, and which maps `x` to `v`,
is the singleton memory `x ↦ v`. -/
lemma Mem.eq_singleton_of_dom_eq {σ : Mem} {x : Var} {v : Val}
    (hdom : σ.dom = {x}) (hx : σ x = some v) : σ = Mem.singleton x v := by
  funext z
  by_cases hz : x = z
  · subst hz; simpa [Mem.singleton, Mem.extend] using hx
  · have hzdom : z ∉ σ.dom := by rw [hdom]; exact fun h ↦ hz h.symm
    rw [Mem.notMem_dom_iff.mp hzdom]
    simp [Mem.singleton, Mem.extend, Mem.emp, hz]

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

def 𝓘 : Inv := {
  prop := fun σ ↦ σ.dom = {"y"} ∧ (σ "y" = some 0 ∨ σ "y" = some 1)
  dom := {"y"}
  dom_finite := Set.finite_singleton _
  dom_valid := by intro σ ⟨h, _⟩; exact h
  prop_finite := by
     -- Any memory satisfying the invariant is determined by the value of `y`, which is
    -- either `0` or `1`; so the set of such memories is the range of a function on `Bool`.
    refine ((Set.toFinite ({0, 1} : Set ℚ)).image fun v ↦ Mem.singleton "y" v).subset ?_
    rintro σ ⟨hdom, hy | hy⟩
    · exact ⟨0, by simp, (Mem.eq_singleton_of_dom_eq hdom hy).symm⟩
    · exact ⟨1, by simp, (Mem.eq_singleton_of_dom_eq hdom hy).symm⟩
}

def φ : OProp := iprop(⌈own ($"y")⌉ ∗ ⌈own ($"x₁")⌉ ∗ ⌈own ($"x₂")⌉ ∗ ⌈own ($"z") ⌉)
def ψ : OProp := ($"z") ~ Bern 0.5

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

/-- The postcondition `ψ` is precise: it is a probabilistic sum of the (precise)
assertions `⌈$"z" == v⌉`. -/
lemma ψ_precise : ψ.Precise := Precise.oplus fun _ _ ↦ Precise.sure _

/-- The unit of the separating conjunction is precise. -/
lemma emp_precise : (Iris.BI.BIBase.emp : OProp).Precise := Precise.sure _

/-- The invariant `𝓘` guarantees that `y` holds one of the two values `0` and `1`. -/
lemma exists_y_of_inv :
    𝓘.to_MProp ⊢ iprop(∃ (x : ↑({0, 1} : Set ℚ)), ($"y") == Expr.literal x.val) := by
  intro σ hσ
  have hmem : "y" ∈ 𝓘.dom := rfl
  have hy := hσ.2
  rw [Mem.restrict_apply_of_mem σ hmem] at hy
  rcases hy with hy | hy
  · exact ⟨_, ⟨⟨0, by simp⟩, rfl⟩,
      ⟨by simp [Expr.var, hy], by simp [Expr.var, Expr.literal, hy]⟩⟩
  · exact ⟨_, ⟨⟨1, by simp⟩, rfl⟩,
      ⟨by simp [Expr.var, hy], by simp [Expr.var, Expr.literal, hy]⟩⟩

/-- The invariant `𝓘` guarantees that the variable `y` is allocated. -/
lemma own_y_of_inv : 𝓘.to_MProp ⊢ MProp.own ($"y") := by
  intro σ hσ
  have hmem : "y" ∈ 𝓘.dom := rfl
  have hy := hσ.2
  rw [Mem.restrict_apply_of_mem σ hmem] at hy
  rcases hy with hy | hy <;>
    exact (show (σ "y").isSome = true by rw [hy]; rfl)

/-! ### The Bernoulli distribution with parameter `1/2` -/

lemma Bern_half_apply (w : Val) :
    Bern 0.5 w = if w = 1 then 2⁻¹ else if w = 0 then 2⁻¹ else 0 := by
  have hq : min 1 (ENNReal.ofReal (((0.5 : ℚ)) : ℝ)) = 2⁻¹ := by
    rw [show (((0.5 : ℚ)) : ℝ) = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat, min_eq_right]
    exact ENNReal.inv_le_one.mpr (by norm_num)
  unfold Bern
  rw [PMF.map_apply]
  simp only [PMF.ofFintype_apply, tsum_bool, hq]
  by_cases h1 : w = 1
  · simp [h1]
  · by_cases h0 : w = 0
    · simp [h0]
    · simp [h0, h1]

/-- `Bern 0.5` is invariant under the involution `u ↦ 1 - u`. -/
lemma Bern_half_symm (u : Val) : Bern 0.5 (1 - u) = Bern 0.5 u := by
  rw [Bern_half_apply, Bern_half_apply]
  by_cases h1 : u = 1
  · simp [h1]
  · by_cases h0 : u = 0
    · simp [h0]
    · have hne1 : (1 : Val) - u ≠ 1 := fun h ↦ h0 (by linarith [h])
      have hne0 : (1 : Val) - u ≠ 0 := fun h ↦ h1 (by linarith [h])
      simp [hne0, hne1, h0, h1]

/-- Only `0` and `1` are in the support of `Bern 0.5`. -/
lemma Bern_half_support {u : Val} (hu : u ∈ (Bern 0.5).support) : u = 0 ∨ u = 1 := by
  by_contra hc
  push Not at hc
  rw [PMF.mem_support_iff, Bern_half_apply] at hu
  simp [hc.1, hc.2] at hu

/-! ### Exclusive or -/

/-- The exclusive or of two values, seen as bits. -/
def xorVal (a b : Val) : Val := if a = b then 0 else 1

lemma xorVal_zero {u : Val} : xorVal 0 u = u ∨ ¬ (u = 0 ∨ u = 1) := by
  by_cases h0 : u = 0
  · left; simp [xorVal, h0]
  · by_cases h1 : u = 1
    · left; simp [xorVal, h1]
    · right; push Not; exact ⟨h0, h1⟩

/-- On the two admissible values, `xor` with `1` is the involution `u ↦ 1 - u`. -/
lemma xorVal_one {u : Val} (hu : u = 0 ∨ u = 1) : xorVal 1 u = 1 - u := by
  rcases hu with rfl | rfl <;> simp [xorVal]

lemma Expr.xor_eval {σ : Mem} {a b : Val} (h₁ : σ "x₁" = some a) (h₂ : σ "x₂" = some b) :
    Expr.xor ($"x₁") ($"x₂") σ = some (xorVal a b) := by
  simp [Expr.xor, Expr.var, h₁, h₂, xorVal]

/-! ### The second half of the first thread -/

/-- The memory-level fact behind the assignment to `z`. -/
lemma xor_entails (v u : Val) :
    (iprop(($"x₁" == Expr.literal v) ∧ (($"x₂" == Expr.literal u) ∧ own ($"z"))) : MProp) ⊢
      iprop((Expr.xor ($"x₁") ($"x₂") == Expr.literal (xorVal v u)) ∧ own ($"z")) := by
  intro σ hσ
  obtain ⟨⟨-, hx₁⟩, ⟨-, hx₂⟩, hzo⟩ := hσ
  have hxor : Expr.xor ($"x₁") ($"x₂") σ = some (xorVal v u) := Expr.xor_eval hx₁ hx₂
  exact ⟨⟨by rw [hxor]; rfl, by rw [hxor]; rfl⟩, hzo⟩

/-- After both `x₁` and `x₂` are known, the assignment to `z` establishes the value of `z`. -/
lemma wp_z_assign {F : ProbSpace → Prop} (v u : Val) :
    iprop(⌈$"x₂" == Expr.literal u⌉ ∗ ⌈$"x₁" == Expr.literal v⌉ ∗ ⌈own ($"z")⌉) ⊢
      wp_base 𝓘 F ("z" ::= Expr.xor ($"x₁") ($"x₂")) ⌈$"z" == Expr.literal (xorVal v u)⌉ := by
  iintro ⟨h2, h1, hz⟩
  iapply wp_assign "z" (Expr.xor ($"x₁") ($"x₂")) _ (xorVal v u)
  isplitl [h1 h2 hz]
  · iapply sure_weaken (xor_entails v u)
    iapply sure_and; isplitl [h1]
    · iapply h1
    · iapply sure_and; isplitl [h2]
      · iapply h2
      · iapply hz
  · iintro h; irevert h
    iapply sure_weaken (Q := iprop($"z" == Expr.literal (xorVal v u)))
    intro σ hσ; exact hσ.1

/-- Once `x₂` has been sampled, the value of `z` is a fair coin flip, whatever the (bit)
value `v` of `x₁` is: `xor` with a fixed bit is a bijection of `{0, 1}` preserving
`Bern 0.5`. -/
lemma oplus_xor_eq_bern (v : Val) (hv : v = 0 ∨ v = 1) :
    (⨁[Bern 0.5] fun u ↦ ⌈$"z" == Expr.literal (xorVal v u)⌉) ⊢ ψ := by
  rcases hv with rfl | rfl
  · refine OProp.oplus_weaken' (fun u hu ↦ ?_)
    rcases xorVal_zero (u := u) with h | h
    · rw [h]
    · exact absurd (Bern_half_support hu) h
  · refine Iris.BI.Entails.trans (OProp.oplus_weaken' (ψ := fun u ↦
      ⌈$"z" == Expr.literal (1 - u)⌉) (fun u hu ↦ ?_)) ?_
    · rw [xorVal_one (Bern_half_support hu)]
    · exact OProp.oplus_reindex (Equiv.subLeft 1) Bern_half_symm
        (fun w ↦ ⌈$"z" == Expr.literal w⌉)

/-- The rest of the first thread, once the value of `x₁` is known: sampling `x₂` and storing
the exclusive or into `z` makes `z` a fair coin flip. -/
lemma wp_after_sample {F : ProbSpace → Prop} (v : Val) (hv : v = 0 ∨ v = 1) :
    iprop((($"x₂") ~ Bern 0.5) ∗ ⌈$"x₁" == Expr.literal v⌉ ∗ ⌈own ($"z")⌉) ⊢
      wp_base 𝓘 F ("z" ::= Expr.xor ($"x₁") ($"x₂")) ψ := by
  refine Iris.BI.Entails.trans
    (OProp.oplus_distrib (Bern 0.5) (fun u ↦ ⌈$"x₂" == Expr.literal u⌉) _) ?_
  refine Iris.BI.Entails.trans (OProp.oplus_weaken' (ψ := fun u ↦
    wp_base 𝓘 F ("z" ::= Expr.xor ($"x₁") ($"x₂")) ⌈$"z" == Expr.literal (xorVal v u)⌉)
    (fun u _ ↦ wp_z_assign v u)) ?_
  exact Iris.BI.Entails.trans wp_split (wp_conseq (oplus_xor_eq_bern v hv))

/-- The whole second half of the first thread, starting from the knowledge of the value of
`x₁`. -/
lemma wp_x2_sample {F : ProbSpace → Prop} (v : Val) (hv : v = 0 ∨ v = 1) :
    iprop(⌈$"x₁" == Expr.literal v⌉ ∗ ⌈own ($"x₂")⌉ ∗ ⌈own ($"z")⌉) ⊢
      wp_base 𝓘 F ("x₂" :≈ PExpr.Bern 0.5 ⨟ "z" ::= Expr.xor ($"x₁") ($"x₂")) ψ := by
  iintro ⟨h1, hx₂, hz⟩
  iapply wp_seq
  iapply wp_bern "x₂" (0.5 : Expr) 0.5
  isplitl [hx₂]
  · irevert hx₂
    iapply sure_weaken (Q := iprop(((0.5 : Expr) == Expr.literal 0.5) ∧ own ($"x₂")))
    intro σ hσ; exact ⟨⟨rfl, rfl⟩, hσ⟩
  · iintro ⟨hb, -⟩
    iapply wp_after_sample v hv; iframe

/-- The first thread, in the branch where the invariant guarantees the value `v` for `y`.
The assignment `x₁ := y` copies that value into `x₁`, which both starts the second half of
the thread and lets the invariant be re-established. -/
lemma wp_x1_branch {F : ProbSpace → Prop} (v : Val) (hv : v = 0 ∨ v = 1) :
    iprop(⌈$"y" == Expr.literal v⌉ ∗ ⌈own ($"x₁")⌉ ∗ ⌈own ($"x₂")⌉ ∗ ⌈own ($"z")⌉) ⊢
      wp_base Inv.emp F ("x₁" ::= $"y")
        iprop(wp_base 𝓘 F ("x₂" :≈ PExpr.Bern 0.5 ⨟ "z" ::= Expr.xor ($"x₁") ($"x₂")) ψ ∗
          ⌈𝓘.to_MProp⌉) := by
  iintro ⟨hy, hx₁, hx₂, hz⟩
  iapply wp_assign_pres "x₁" ($"y") _ v (by intro σ w; simp [Expr.var, Mem.extend])
  isplitl [hy hx₁]
  · iapply sure_and; isplitl [hy]
    · iapply hy
    · iapply hx₁
  · iintro ⟨h1, hy'⟩
    isplitl [h1 hx₂ hz]
    · iapply wp_x2_sample v hv; iframe
    · irevert hy'
      iapply sure_weaken (inv_of_y_eq v hv)

/-- The two values allowed for `y` by the invariant. -/
abbrev Bit : Set Val := {0, 1}

/-- A nondeterministic choice between (identical) postconditions of the shape
"weakest precondition, and the invariant holds" can be collapsed: the invariant is precise,
and the postcondition `ψ` of the weakest precondition is precise as well. -/
lemma collapse_post {F : ProbSpace → Prop} {ι : Type} {c : Cmd Act} :
    OProp.nondet (fun (_ : ι) => iprop(wp_base 𝓘 F c ψ ∗ ⌈𝓘.to_MProp⌉)) ⊢
      iprop(wp_base 𝓘 F c ψ ∗ ⌈𝓘.to_MProp⌉) :=
  Iris.BI.Entails.trans (OProp.nondet_distrib' _ _ (Precise.sure _))
    (Iris.BI.sep_mono_left (wp_nondet ψ_precise))

/-- The first thread, given only the nondeterministic knowledge that `y` holds one of the
two values allowed by the invariant. -/
lemma wp_x1_nondet {F : ProbSpace → Prop} :
    iprop(& (fun (i : Bit) => ⌈$"y" == Expr.literal i.val⌉) ∗
        ⌈own ($"x₁")⌉ ∗ ⌈own ($"x₂")⌉ ∗ ⌈own ($"z")⌉) ⊢
      wp_base Inv.emp F ("x₁" ::= $"y")
        iprop(wp_base 𝓘 F ("x₂" :≈ PExpr.Bern 0.5 ⨟ "z" ::= Expr.xor ($"x₁") ($"x₂")) ψ ∗
          ⌈𝓘.to_MProp⌉) := by
  refine Iris.BI.Entails.trans (OProp.nondet_distrib _ _) ?_
  refine Iris.BI.Entails.trans
    (OProp.nondet_weaken (fun i ↦ wp_x1_branch (F := F) i.val i.2)) ?_
  exact Iris.BI.Entails.trans wp_nsplit (wp_conseq collapse_post)

lemma entropy_mixer_spec :
  Inv.emp ⊢{{ φ }} entropy_mixer {{ ψ }} := by
  unfold φ entropy_mixer
  iintro ⟨hy, hx₁, hx₂, hz⟩; unfold wp; iapply wp_seq
  iapply wp_assign "y" 0 _ 0; isplitl [hy]
  · irevert hy; iapply sure_weaken; iintro hy
    isplit
    · intro _ _; exact ⟨rfl, rfl⟩
    · iapply hy
  · iintro hy
    iapply wp_conseq (φ := iprop(ψ ∗ ⌈ 𝓘.to_MProp ⌉)) (ψ := ψ)
    · iintro ⟨h, _⟩; iapply h
    · iapply wp_share (𝓘 := 𝓘); isplitl [hy]
      · irevert hy; iapply sure_weaken
        intro σ hσ; exact inv_of_y_eq 0 (Or.inl rfl) σ hσ.1
      · iapply wp_conseq (φ := iprop(ψ ∗ Iris.BI.BIBase.emp))
        · iintro ⟨h, _⟩; iframe
        · rw [← wp]
          iapply wp_par (ψ₁ := ψ) (ψ₂ := iprop(emp)) ψ_precise emp_precise
          isplitl
          · unfold wp; rw [← wp]; iapply wp_strengthen
            · exact ψ_precise
            · unfold wp_weak; iapply wp_seq; iapply wp_atom
              iintro hinv; rw [← wp_weak]
              ihave hinv := sure_weaken exists_y_of_inv $$ hinv
              irevert hinv
              iapply wp_exists (F := fun 𝓟fr ↦ ∀ E, 𝓟fr.mspace.MeasurableSet' E →
                𝓟fr.μ E = 0 ∨ 𝓟fr.μ E = 1)
              iintro hy
              iapply wp_x1_nondet; iframe
          · unfold wp; iapply wp_atom; iintro hinv
            iapply wp_assign "y" 1 _ 1
            isplitl [hinv]
            · irevert hinv; iapply sure_weaken
              intro σ hσ; exact ⟨⟨rfl, rfl⟩, own_y_of_inv σ hσ⟩
            · iintro hy
              isplit
              · intro _ _; trivial
              · irevert hy; iapply sure_weaken
                intro σ hσ; exact inv_of_y_eq 1 (Or.inr rfl) σ hσ.1

end Pcol
