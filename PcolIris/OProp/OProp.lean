import Iris

import PcolIris.Semantics.Syntax
import PcolIris.OProp.MProp
import PcolIris.OProp.ProductLaws

namespace Pcol

/-! ### Assertions about monotone expressions -/

namespace Expr

lemma literal_mono (v : Val) : Expr.Mono (literal v) := fun _ h ↦ h

lemma var_mono (x : Var) : Expr.Mono (var x) := fun hle h ↦ (Mem.le_iff.mp hle) x _ h

lemma equals_iff {e₁ e₂ : Expr} (h₁ : Expr.Mono e₁) (h₂ : Expr.Mono e₂) {σ : Mem} :
    (e₁ == e₂) σ ↔ (e₁ σ).isSome ∧ e₁ σ = e₂ σ := by
  refine MProp.upClose_iff (fun {σ τ} hle ⟨hs, heq⟩ ↦ ?_)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  rw [h₁ hle hv, h₂ hle (heq ▸ hv)]
  exact ⟨rfl, rfl⟩

/-- The value of a variable, as an assertion about memories. -/
lemma var_equals_literal_iff {x : Var} {v : Val} {σ : Mem} :
    ($ x == literal v) σ ↔ σ x = some v := by
  rw [equals_iff (var_mono x) (literal_mono v)]
  simp only [var, literal]
  constructor
  · exact fun h ↦ h.2
  · intro h; rw [h]; exact ⟨rfl, rfl⟩

/-- Equality of two variables, as an assertion about memories. -/
lemma var_equals_var_iff {x y : Var} {σ : Mem} :
    ($ x == $ y) σ ↔ (σ x).isSome ∧ σ x = σ y :=
  equals_iff (var_mono x) (var_mono y)

end Expr

namespace MProp

lemma own_iff {e : Expr} (h : Expr.Mono e) {σ : Mem} : own e σ ↔ (e σ).isSome := by
  refine upClose_iff (fun {σ τ} hle hs ↦ ?_)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  rw [h hle hv]; rfl

lemma own_var_iff {x : Var} {σ : Mem} : own ($ x) σ ↔ (σ x).isSome :=
  own_iff (Expr.var_mono x)

end MProp


/-- Outcome assertions: upward-closed predicates on probability spaces.  Adding information
to a probability space (going up in the order) preserves every assertion. -/
@[ext]
structure OProp where
  prop : ProbSpace → Prop
  upcl : ∀ {𝓟 𝓠 : ProbSpace}, 𝓟 ≤ 𝓠 → prop 𝓟 → prop 𝓠

abbrev Event := Set Mem

namespace OProp

instance : FunLike OProp ProbSpace Prop where
  coe φ := φ.prop
  coe_injective := by intro φ ψ heq; ext1; exact heq

lemma mono (φ : OProp) {𝓟 𝓠 : ProbSpace} (h : 𝓟 ≤ 𝓠) (hφ : φ 𝓟) : φ 𝓠 := φ.upcl h hφ

/-- The almost sure assertion: the memory satisfies `P` at every outcome of positive
probability. -/
def sure (P : MProp) : OProp where
  prop 𝓟 := 𝓟.support ⊆ 𝓟.state ⁻¹' P.prop
  upcl := by
    rintro 𝓟 𝓠 ⟨g, hg⟩ h i hi
    exact P.upcl (hg.state i hi) (h (hg.mem_support hi))

notation "⌈" P "⌉" => sure iprop(P)

open MeasureTheory in
/-- The almost sure assertion agrees with the definition of the paper: `⌈P⌉` holds exactly
when the set of outcomes whose memory satisfies `P` is measurable and has probability `1`.
Completeness of probability spaces is what makes this set measurable. -/
lemma sure_iff {P : MProp} {𝓟 : ProbSpace} :
    sure P 𝓟 ↔ 𝓟.mspace.MeasurableSet' (𝓟.state ⁻¹' P.prop) ∧
      𝓟.meas (𝓟.state ⁻¹' P.prop) = 1 := by
  constructor
  · intro h
    have hsupp := ProbSpace.support_measurableSet 𝓟
    have hc0 : 𝓟.meas 𝓟.supportᶜ = 0 := by
      rw [measure_compl hsupp (measure_ne_top _ _), ProbSpace.measure_support 𝓟,
        measure_univ, tsub_self]
    have hSc : 𝓟.meas (𝓟.state ⁻¹' P.prop)ᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.mpr h) hc0
    have hmeas : 𝓟.mspace.MeasurableSet' (𝓟.state ⁻¹' P.prop)ᶜ := 𝓟.complete.out _ hSc
    have hmeas' : 𝓟.mspace.MeasurableSet' (𝓟.state ⁻¹' P.prop) := by
      simpa only [compl_compl] using 𝓟.mspace.measurableSet_compl _ hmeas
    refine ⟨hmeas', ?_⟩
    rw [← compl_compl (𝓟.state ⁻¹' P.prop), measure_compl hmeas (measure_ne_top _ _), hSc,
      measure_univ, tsub_zero]
  · rintro ⟨hmeas, h1⟩
    exact ProbSpace.support_subset hmeas h1

open ProbSpace in
instance : Iris.BI.BIBase OProp where
  Entails φ ψ := ∀ m, φ m → ψ m
  emp := ⌈ Iris.BI.BIBase.emp ⌉
  pure p := ⟨fun _ ↦ p, fun _ h ↦ h⟩
  and φ ψ := ⟨fun m ↦ φ m ∧ ψ m, fun h ⟨h₁, h₂⟩ ↦ ⟨φ.mono h h₁, ψ.mono h h₂⟩⟩
  or φ ψ := ⟨fun m ↦ φ m ∨ ψ m, fun h h' ↦ h'.imp (φ.mono h) (ψ.mono h)⟩
  imp φ ψ := ⟨fun m ↦ ∀ m', m ≤ m' → φ m' → ψ m', fun h h' m' hm' ↦ h' m' (h.trans hm')⟩
  sForall Ψ := ⟨fun m ↦ ∀ φ, Ψ φ → φ m, fun h h' φ hφ ↦ φ.mono h (h' φ hφ)⟩
  sExists Ψ := ⟨fun m ↦ ∃ φ, Ψ φ ∧ φ m, fun h ⟨φ, hφ, h'⟩ ↦ ⟨φ, hφ, φ.mono h h'⟩⟩
  sep φ ψ := ⟨fun m ↦
    ∃ (m₁ m₂ : ProbSpace),
      Disjoint m₁.dom m₂.dom ∧
      (m₁ ⊗ m₂) ≤ m ∧
      φ m₁ ∧
      ψ m₂,
    fun h ⟨m₁, m₂, hd, hle, h₁, h₂⟩ ↦ ⟨m₁, m₂, hd, hle.trans h, h₁, h₂⟩⟩
  wand φ ψ := ⟨fun m ↦ ∀ m₁, Disjoint m.dom m₁.dom → φ m₁ → ψ (m ⊗ m₁),
    fun h h' m₁ hd hφ ↦
      ψ.mono (product_mono_left h hd) (h' m₁ (hd.mono_left (dom_mono h)) hφ)⟩
  persistently φ := ⟨fun _ ↦ φ unit, fun _ h ↦ h⟩
  later φ := φ

instance : Iris.COFE OProp := Iris.COFE.ofDiscrete OProp

open ProbSpace in
instance : Iris.BI OProp where
  toCOFE := inferInstance
  entails_refl := fun _ h ↦ h
  entails_trans := by intro _ _ _ he₁ he₂ 𝓟 h; exact he₂ 𝓟 <| he₁ 𝓟 h
  equiv_iff := by
    intro φ ψ; constructor
    · rintro rfl; constructor <;> intro _ h <;> exact h
    · intro ⟨h₁, h₂⟩; ext 𝓟; exact ⟨h₁ 𝓟, h₂ 𝓟⟩
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
  pure_elim' := by intro p φ hφ 𝓟 hp; exact hφ hp 𝓟 True.intro
  and_elim_l := by intro φ ψ 𝓟 ⟨hφ, _⟩; exact hφ
  and_elim_r := by intro φ ψ 𝓟 ⟨_, hψ⟩; exact hψ
  and_intro := by intro φ ψ ϑ he₁ he₂ 𝓟 hφ; exact ⟨he₁ 𝓟 hφ, he₂ 𝓟 hφ⟩
  or_intro_l := by intro φ ψ 𝓟 hφ; left; exact hφ
  or_intro_r := by intro φ ψ 𝓟 hψ; right; exact hψ
  or_elim := by
    intro φ ψ ϑ h₁ h₂ 𝓟 h
    rcases h with h | h
    · exact h₁ 𝓟 h
    · exact h₂ 𝓟 h
  imp_intro := by
    intro φ ψ ϑ h 𝓟 hφ 𝓠 hle hψ
    exact h 𝓠 ⟨φ.mono hle hφ, hψ⟩
  imp_elim := by
    intro φ ψ ϑ h 𝓟 ⟨hφ, hψ⟩
    exact h 𝓟 hφ 𝓟 (le_refl _) hψ
  sForall_intro := by intro φ Ψ h 𝓟 hφ ψ hψ; exact h ψ hψ 𝓟 hφ
  sForall_elim := by intro Ψ φ hφ 𝓟 h; exact h φ hφ
  sExists_intro := by intro Ψ φ hφ 𝓟 h; exact ⟨φ, hφ, h⟩
  sExists_elim := by intro Φ ψ h 𝓟 ⟨φ, hφ, h'⟩; exact h φ hφ 𝓟 h'
  sep_mono := by
    intro φ φ' ψ ψ' h₁ h₂ 𝓟 ⟨m₁, m₂, hd, hle, h₁', h₂'⟩
    exact ⟨m₁, m₂, hd, hle, h₁ m₁ h₁', h₂ m₂ h₂'⟩
  emp_sep := by
    intro φ; constructor
    · rintro 𝓟 ⟨m₁, m₂, hd, hle, -, h⟩
      exact φ.mono ((le_product_right hd).trans hle) h
    · intro 𝓟 h
      exact ⟨unit, 𝓟, Set.empty_disjoint _, product_unit_le 𝓟, fun _ _ ↦ trivial, h⟩
  sep_symm := by
    rintro φ ψ 𝓟 ⟨m₁, m₂, hd, hle, h₁, h₂⟩
    exact ⟨m₂, m₁, hd.symm, (product_comm hd).trans hle, h₂, h₁⟩
  sep_assoc_l := by
    rintro φ ψ ϑ 𝓟 ⟨m₁₂, m₃, hd, hle, ⟨m₁, m₂, hd', hle', h₁, h₂⟩, h₃⟩
    have hsub₁ : m₁.dom ⊆ m₁₂.dom := Set.subset_union_left.trans (dom_mono hle')
    have hsub₂ : m₂.dom ⊆ m₁₂.dom := Set.subset_union_right.trans (dom_mono hle')
    refine ⟨m₁, m₂ ⊗ m₃, Set.disjoint_union_right.mpr ⟨hd', hd.mono_left hsub₁⟩, ?_, h₁,
      m₂, m₃, hd.mono_left hsub₂, le_refl _, h₂, h₃⟩
    exact (product_assoc' m₁ m₂ m₃).trans ((product_mono_left hle' hd).trans hle)
  wand_intro := by
    intro φ ψ ϑ h 𝓟 hφ m₁ hd hψ
    exact h _ ⟨𝓟, m₁, hd, le_refl _, hφ, hψ⟩
  wand_elim := by
    rintro φ ψ ϑ h 𝓟 ⟨m₁, m₂, hd, hle, hφ, hψ⟩
    exact ϑ.mono hle (h m₁ hφ m₂ hd hψ)
  persistently_mono := by intro φ ψ h _ hφ; exact h unit hφ
  persistently_idem_2 := by intro φ _ h; exact h
  persistently_emp_2 := by intro _ _; exact fun _ _ ↦ trivial
  persistently_and_2 := by intro φ ψ _ h; exact h
  persistently_sExists_1 := by
    rintro Ψ 𝓟 ⟨φ, hφ, h⟩
    exact ⟨_, ⟨φ, rfl⟩, hφ, h⟩
  persistently_absorb_l := by
    rintro φ ψ 𝓟 ⟨_, _, _, _, h, _⟩
    exact h
  persistently_and_l := by
    rintro φ ψ 𝓟 ⟨hφ, hψ⟩
    exact ⟨unit, 𝓟, Set.empty_disjoint _, product_unit_le 𝓟, hφ, hψ⟩
  later_mono := fun h ↦ h
  later_intro := fun _ h ↦ h
  later_sForall_2 := by
    intro Φ 𝓟 h φ hφ
    exact h _ ⟨φ, rfl⟩ 𝓟 (le_refl _) hφ
  later_sExists_false := by
    rintro Φ 𝓟 ⟨φ, hφ, h⟩
    exact Or.inr ⟨_, ⟨φ, rfl⟩, hφ, h⟩
  later_sep := ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  later_persistently := ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  later_false_em := by
    intro φ 𝓟 h
    exact Or.inr fun _ _ h' ↦ h'.elim

instance : Iris.BI.BIAffine OProp where
  affine := by
    intro φ; constructor; intro _ _ _ _; trivial

def Precise (φ : OProp) : Prop :=
  ∃ 𝓟 : ProbSpace, ∀ 𝓠, 𝓟 ≤ 𝓠 ↔ φ 𝓠

def oplus {ι : Type} (ξ : PMF ι) (φ : ι → OProp) : OProp where
  prop 𝓟 := ∃ 𝓠 V h hd,
    ProbSpace.sum ξ 𝓠 V h hd ≤ 𝓟 ∧
    ∀ v ∈ ξ.support, φ v (𝓠 v)
  upcl := fun hle ⟨𝓠, V, h, hd, hsum, hφ⟩ ↦ ⟨𝓠, V, h, hd, hsum.trans hle, hφ⟩

notation "⨁[ " ξ " ] " φ => oplus ξ φ

def distributed_as (e : Expr) (ξ : PMF Val) : OProp :=
  ⨁[ξ] fun v ↦ ⌈ e == Expr.literal v ⌉

infixl:70 " ~ " => distributed_as

def nondet {ι : Type} (φ : ι → OProp) : OProp where
  prop 𝓟 := ∃ ξ : PMF ι, oplus ξ φ 𝓟
  upcl := fun hle ⟨ξ, h⟩ ↦ ⟨ξ, (oplus ξ φ).mono hle h⟩

prefix:60 "& " => nondet

end OProp

end Pcol
