import PcolIris.Logic.Par
import PcolIris.Logic.LemmaC6
import PcolIris.Logic.Framed
import PcolIris.Logic.Actions
import PcolIris.OProp.ProbSpaceLemmas
import PcolIris.OProp.Laws
import PcolIris.Semantics.Invariant
import PcolIris.Semantics.Semantics
import PcolIris.OProp.OProp

namespace Pcol

open MProp

def wp_base (𝓘 : Inv) (F : ProbSpace → Prop) (c : Cmd Act) (ψ : OProp) : OProp where
  prop 𝓟 :=
    ∀ (μ : Distr Mem) (𝓟fr 𝓙 : ProbSpace),
      -- The frame validity predicate holds
      F 𝓟fr →
      -- The initial distribution `μ` refines the precondition `𝓟`, the frame `𝓟fr`, and a
      -- space `𝓙` satisfying the invariant `𝓘`
      Framed 𝓘 𝓟 𝓟fr 𝓙 μ →
      -- Take any `ν` that results from running the program
      ∀ ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 (c.withInv 𝓘).to_pom,
      -- Then the program has not deallocated variables, and `ν` refines some probability
      -- space `𝓠`, which satisfies the postcondition `ψ`, together with the same frame and a
      -- space satisfying the invariant.  The program does not acquire variables either: `𝓠`
      -- owns no more variables than `𝓟`.
        Distr.Keeps μ ν ∧ ∃ 𝓠 𝓙', Framed 𝓘 𝓠 𝓟fr 𝓙' ν ∧ 𝓠.dom ⊆ 𝓟.dom ∧ ψ 𝓠
  upcl := fun hle h μ 𝓟fr 𝓙 hF hf ν hν ↦
    let ⟨hk, 𝓠, 𝓙', hf', hdom, hψ⟩ := h μ 𝓟fr 𝓙 hF (hf.mono hle) ν hν
    ⟨hk, 𝓠, 𝓙', hf', hdom.trans (ProbSpace.dom_mono hle), hψ⟩

/-- The standard "strong" wp allows any frame -/
def wp (𝓘 : Inv) : Cmd Act → OProp → OProp := wp_base 𝓘 (fun _ ↦ True)

/-- The "weak" wp only preserves frames for trivial probability spaces,
where every event has probability exactly 0 or 1 -/
def wp_weak (𝓘 : Inv) : Cmd Act → OProp → OProp := wp_base 𝓘 fun 𝓟fr ↦
  ∀ E, 𝓟fr.mspace.MeasurableSet' E → 𝓟fr.μ E = 0 ∨ 𝓟fr.μ E = 1

notation 𝓘 " ⊢{{" φ "}} " c " {{" ψ "}}" => φ ⊢ wp 𝓘 c ψ

/- BASIC COMMAND RULES -/

variable {𝓘 : Inv} {F : ProbSpace → Prop} {c : Cmd Act}

/-- The `Skip` rule. -/
lemma wp_skip (φ : OProp) :
    φ ⊢ wp_base 𝓘 F Cmd.skip φ := by
  intro 𝓟 hφ μ 𝓟fr 𝓙 _ hf ν hν
  rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_skip, bind_pure] at hν
  have hle : μ ≤ ν := by
    have : ν ∈ (ConvexPowerset.singleton' μ).set := hν
    rwa [ConvexPowerset.singleton'_set_eq] at this
  rw [← proper_dist_maximal hf.refines.bot_0 hle]
  exact ⟨Distr.Keeps.refl μ, 𝓟, 𝓙, hf, subset_rfl, hφ⟩

lemma wp_seq {c₁ c₂ : Cmd Act} {ψ : OProp} :
    wp_base 𝓘 F c₁ (wp_base 𝓘 F c₂ ψ) ⊢ wp_base 𝓘 F (Cmd.seq c₁ c₂) ψ := by
  intro 𝓟 h μ 𝓟fr 𝓙 hF href ν; rw [Cmd.withInv, Cmd.to_pom, Pom.lin_seq, ← bind_assoc]
  intro hν; rcases ConvexPowerset.mem_bind.mp hν with ⟨ξ, hξ, f, hf, rfl⟩
  have ⟨hk, 𝓡, 𝓙', href', hdom, h'⟩ := h μ 𝓟fr 𝓙 hF href ξ hξ
  obtain ⟨hk', 𝓠, 𝓙'', hf'', hdom', hψ⟩ := h' ξ 𝓟fr 𝓙' hF href' _
    (ConvexPowerset.mem_bind.mpr ⟨ξ, ConvexPowerset.self_mem_singleton' _, f, hf, rfl⟩)
  exact ⟨Distr.Keeps.trans hk hk', 𝓠, 𝓙'', hf'', hdom'.trans hdom, hψ⟩

lemma wp_if_true {b : Expr} {c₁ c₂ : Cmd Act} {φ ψ : OProp} :
     ⌈b == Expr.literal 1⌉ ∧ wp_base 𝓘 F c₁ ψ ⊢ wp_base 𝓘 F (Cmd.if_stmt b c₁ c₂) ψ := by
  intro 𝓟 ⟨htrue, hwp⟩ μ 𝓟fr 𝓙 hF href ν hν; rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_if_stmt] at hν
  sorry

/-- The `Assign` rule.  The expression must be local (`Expr.Local`): its value is known in
the precondition, and must not be changed by interference on the invariant's variables. -/
lemma wp_assign (x : Var) (e : Expr) (ψ : OProp) (v : Val) (he : e.Local) :
    ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗ ((⌈$ x == Expr.literal v ∧ own e⌉) -∗ ψ) ⊢
      wp_base 𝓘 F (x ::= e) ψ := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hd, hle, hpre, hwand⟩ μ 𝓟fr 𝓙 _ hf ν hν
  have hf₁ := hf.mono hle
  change ν ∈ ConvexPowerset.singleton' μ >>=
    𝓛 (Pom.singleton (Label.act (⟨Act.assign x e, 𝓘⟩ : WithInv Act))) at hν
  rw [Pom.lin_act] at hν
  obtain ⟨K, rfl, hK⟩ := run_act hf.refines.bot_0 hν
  -- The program's part of the space, with the frame
  set 𝓐 := (𝓟₁ ⊗ 𝓟₂) ⊗ 𝓟fr with h𝓐def
  have h𝓐 : 𝓐 ≼ μ := Distr.Refines.mono (ProbSpace.le_product_left _ _) hf₁.refines
  have hIJ : 𝓘.dom ⊆ 𝓙.dom := (OProp.sure_forget 𝓘.footprint hf₁.inv).1
  have h𝓐I : Disjoint 𝓐.dom 𝓘.dom := hf₁.disj_inv.mono_right hIJ
  -- The invariant holds of the initial memories
  have hIμ : ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → 𝓘.prop (m.restrict 𝓘.dom) := fun m hm ↦
    Distr.Refines.sure hf₁.refines ((OProp.sure 𝓘.to_MProp).mono
      (ProbSpace.le_product_right hf₁.disj_inv) hf₁.inv) hm
  -- The precondition holds of the program's part of the space
  have h𝓟₁𝓐 : 𝓟₁ ≤ 𝓐 :=
    (ProbSpace.le_product_left 𝓟₁ 𝓟₂).trans (ProbSpace.le_product_left _ _)
  have hpre𝓐 := (OProp.sure _).mono h𝓟₁𝓐 hpre
  have hx : x ∈ 𝓟₁.dom := by
    obtain ⟨k, hk⟩ := ProbSpace.support_nonempty 𝓟₁
    rw [← 𝓟₁.dom_valid k, Mem.mem_dom_iff]
    exact Option.isSome_iff_ne_none.mp (MProp.own_var_iff.mp (hpre hk).2)
  have hx𝓐 : x ∈ 𝓐.dom := Or.inl (Or.inl hx)
  have hxI : x ∉ 𝓘.dom := fun h ↦ Set.disjoint_left.mp h𝓐I hx𝓐 h
  -- The outcomes of the assignment
  have hKm : ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → ∀ y ∈ (K m).support,
      ∃ τ, 𝓘.prop τ ∧ y = ((τ ⊎ m).extend x v : Mem) := by
    intro m hm y hy
    obtain ⟨i, hi, him⟩ := Distr.Refines.exists_le h𝓐 hm
    obtain ⟨σ', hσ', -, hσ'e⟩ := (hpre𝓐 hi).1
    have hsupp := sem_withInv_supportedIn (a := Act.assign x e) (hIμ m hm)
      (G := {m'' | ∃ τ, 𝓘.prop τ ∧ m'' = (τ ⊎ m).extend x v}) fun τ hτ ↦ ?_
    · obtain ⟨m'', ⟨τ, hτ, rfl⟩, rfl⟩ := hsupp (K m) (hK m hm) y hy
      exact ⟨τ, hτ, rfl⟩
    · have hτd : τ.dom = 𝓘.dom := 𝓘.dom_valid hτ
      have hle' : 𝓐.state i ≤ (τ ⊎ m) := Mem.le_union_of_le him
        (by rw [hτd, 𝓐.dom_valid]; exact h𝓐I.symm)
      have hev : e (τ ⊎ m) = some v := he.mono (hσ'.trans hle') hσ'e
      refine (sem_assign_supportedIn hev).mono (Set.singleton_subset_iff.mpr ⟨⟨τ, hτ, rfl⟩, ?_⟩)
      rw [Mem.restrict_extend_of_notMem v hxI, Mem.restrict_union_left hτd]
      exact hτ
  -- The final memories
  have hfin : ∀ m'' : Mem, (μ.bind K) (m'' : WithBot Mem) ≠ 0 →
      ∃ (m : Mem) (τ : Mem), μ (m : WithBot Mem) ≠ 0 ∧ 𝓘.prop τ ∧ m'' = (τ ⊎ m).extend x v := by
    intro m'' hm''
    obtain ⟨y, hy, hm''y⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hm'')
    rcases y with _ | m
    · exact absurd hf.refines.bot_0 ((PMF.mem_support_iff _ _).mp hy)
    · have hm : μ (m : WithBot Mem) ≠ 0 := (PMF.mem_support_iff _ _).mp hy
      obtain ⟨τ, hτ, h⟩ := hKm m hm _ hm''y
      exact ⟨m, τ, hm, hτ, Option.some.inj h⟩
  refine ⟨fun D hD m'' hm'' ↦ ?_, ?_⟩
  · obtain ⟨m, τ, hm, -, rfl⟩ := hfin m'' hm''
    rw [Mem.dom_extend, Mem.dom_union]
    exact (hD m hm).trans (Set.subset_union_right.trans (Set.subset_insert _ _))
  -- The program's part of the space after the assignment
  set 𝓡 := 𝓟₁.assign x v hx
  have hst' : ∀ i, ((𝓡 ⊗ 𝓟₂) ⊗ 𝓟fr).state i = (𝓐.state i).extend x v := fun i ↦ by
    simp only [𝓐, ProbSpace.product_state, Mem.union_extend]; rfl
  have href' : ((𝓡 ⊗ 𝓟₂) ⊗ 𝓟fr) ≼ μ.bind K := by
    refine Distr.Refines.bind (𝓐' := (𝓡 ⊗ 𝓟₂) ⊗ 𝓟fr) h𝓐 (fun E h ↦ h) (fun E _ ↦ rfl)
      fun i _ m hm him y hy ↦ ?_
    obtain ⟨τ, hτ, rfl⟩ := hKm m hm y hy
    refine ⟨_, rfl, ?_⟩
    rw [hst']
    exact Mem.extend_mono (Mem.le_union_of_le him
      (by rw [𝓘.dom_valid hτ, 𝓐.dom_valid]; exact h𝓐I.symm)) x v
  -- The invariant's part of the space after the assignment
  obtain ⟨T, hT, hTref, hTst⟩ := Distr.Refines.pad href' (U := 𝓘.dom) fun m'' hm'' ↦ by
    obtain ⟨m, τ, -, hτ, rfl⟩ := hfin m'' hm''
    rw [Mem.dom_extend, Mem.dom_union, 𝓘.dom_valid hτ]
    exact Set.subset_union_left.trans (Set.subset_insert _ _)
  have hTinv : OProp.sure 𝓘.to_MProp T := fun k _ ↦ by
    obtain ⟨m'', hm'', heq⟩ := hTst k
    obtain ⟨m, τ, -, hτ, rfl⟩ := hfin m'' hm''
    change 𝓘.prop ((T.state k).restrict 𝓘.dom)
    rw [heq, Mem.restrict_restrict, Set.inter_self, Mem.restrict_extend_of_notMem v hxI,
      Mem.restrict_union_left (𝓘.dom_valid hτ)]
    exact hτ
  -- The postcondition
  have h𝓡 : OProp.sure iprop($ x == Expr.literal v ∧ own e) 𝓡 := by
    intro k hk
    obtain ⟨σ', hσ', hσ'd, -⟩ := (hpre hk).1
    refine ⟨Expr.var_equals_literal_iff.mpr (Mem.extend_apply_self _ _ _), ?_⟩
    exact ⟨σ'.extend x v, Mem.extend_mono hσ' x v, he.extend x v hσ'd⟩
  refine ⟨𝓡 ⊗ 𝓟₂, T, ⟨hTinv, hf₁.disj_frame, ?_, hTref⟩,
    (show 𝓟₁.dom ∪ 𝓟₂.dom ⊆ 𝓟.dom from ProbSpace.dom_mono hle),
    ψ.mono (ProbSpace.product_comm hd) (hwand 𝓡 hd.symm h𝓡)⟩
  rw [hT]; exact h𝓐I

lemma wp_bern (x : Var) (e : Expr) (v : Val) {ψ : OProp} :
    ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗ (($ x ~ Bern v ∧ ⌈own e⌉) -∗ ψ) ⊢
    wp_base 𝓘 F (x :≈ PExpr.Bern e) ψ := by sorry

lemma wp_bounded_rank {ℓ h : ℕ} (hle : ℓ ≤ h) {φ : Set.Icc ℓ h → OProp} {b rank : Expr} {p : ℚ} (hp : p > 0)
    (hrank : ∀ r, φ r ⊢ ⌈rank == Expr.literal r⌉)
    (hexit : φ ⟨ℓ, le_refl _, hle⟩ ⊢ ⌈b == Expr.literal 0⌉)
    (hloop : ∀ {r}, r.val > ℓ → φ r ⊢ ⌈b == Expr.literal 1⌉)
    (hprec : (φ ⟨ℓ, le_refl _, hle⟩).Precise) :
    (∀ r, ⌜r.val > 0⌝ -∗ φ r -∗
      wp_base 𝓘 F c
        (⨁[Bern p] fun x ↦
          if x = 1 then
            (& fun (s : Set.Ico ℓ r) ↦
              φ ⟨s.val, s.property.1, (le_of_lt s.property.2).trans r.property.2⟩)
          else
            (& φ)))
      ⊢ & φ -∗ wp 𝓘 (while( b ){ c }) (φ ⟨ℓ, le_refl _, hle⟩) := sorry

/-- CONCURRNCY RULES -/

-- This mostly follows from invariant monotonicity, but we need a few more properties about
-- assertions, etc
lemma wp_share {𝓘 : Inv} {F : ProbSpace → Prop} {c : Cmd Act} {ψ : OProp} :
    OProp.sure 𝓘.to_MProp ∗ wp_base 𝓘 F c ψ ⊢ wp_base Inv.emp F c iprop(ψ ∗ OProp.sure 𝓘.to_MProp) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h𝓘, hwp⟩ μ 𝓟fr 𝓙 hF hf ν hν
  have hν' : ν ∈ ConvexPowerset.singleton' μ >>= Pom.lin (c.withInv 𝓘).to_pom := by
    refine le_iff_supset.mp ?_ hν
    apply ConvexPowerset.bind_monotone (le_refl _)
    apply (Pom.lin_continuous (act := WithInv Act) (test := Test)).monotone
    exact Cmd.withInv_monotone c (Inv.le_emp 𝓘)
  sorry

lemma wp_atom {𝓘 : Inv} {F : ProbSpace → Prop} {a : Act} {ψ : OProp} :
    (OProp.sure 𝓘.to_MProp -∗ wp_base Inv.emp F (Cmd.act a) (iprop(ψ ∗ OProp.sure 𝓘.to_MProp)))
    ⊢ wp_base 𝓘 F (Cmd.act a) ψ := by
  sorry

/-- **The parallel composition rule.**  If the postconditions `ψ₁` and `ψ₂` are precise, then
the weakest preconditions of two threads can be combined with the separating conjunction.

The proof follows the `Par` case of the soundness theorem of the pcOL paper: precision
provides least probability spaces `𝓠₁` and `𝓠₂` satisfying the two postconditions, each
thread is shown to take any frame-respecting refinement of its precondition to a refinement
of `𝓠ₖ`, and the two threads are then combined by `lemma_C6`. -/
lemma wp_par {𝓘 : Inv} {c₁ c₂ : Cmd Act} {ψ₁ ψ₂ : OProp}
    (hψ₁ : ψ₁.Precise) (hψ₂ : ψ₂.Precise) :
    wp 𝓘 c₁ ψ₁ ∗ wp 𝓘 c₂ ψ₂ ⊢ wp 𝓘 (c₁.par c₂) iprop(ψ₁ ∗ ψ₂) := by
  intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, h₁, h₂⟩ μ 𝓟fr 𝓙 _ hf ν hν
  -- Running each thread alone shows that `ψ₁` and `ψ₂` are satisfiable, so by precision
  -- they have least models `𝓠₁` and `𝓠₂`
  have hf' := hf.mono hle
  obtain ⟨ν₁, hν₁⟩ := (ConvexPowerset.singleton' μ >>= 𝓛 (c₁.withInv 𝓘).to_pom).nonempty
  obtain ⟨ν₂, hν₂⟩ := (ConvexPowerset.singleton' μ >>= 𝓛 (c₂.withInv 𝓘).to_pom).nonempty
  obtain ⟨-, 𝓡₁, _, -, hdom₁, hψ₁'⟩ := h₁ μ _ 𝓙 True.intro (hf'.left hdisj) ν₁ hν₁
  obtain ⟨-, 𝓡₂, _, -, hdom₂, hψ₂'⟩ := h₂ μ _ 𝓙 True.intro (hf'.right hdisj) ν₂ hν₂
  obtain ⟨𝓠₁, hQ₁⟩ := hψ₁ _ hψ₁'
  obtain ⟨𝓠₂, hQ₂⟩ := hψ₂ _ hψ₂'
  -- Each thread, run in isolation with an arbitrary frame, establishes its postcondition;
  -- by precision, the least such postcondition space is `𝓠ₖ`
  have hthread₁ : ∀ (𝓕 𝓙₁ : ProbSpace) (μ₁ : Distr Mem), Framed 𝓘 𝓟₁ 𝓕 𝓙₁ μ₁ →
      ∀ ν₁ ∈ ConvexPowerset.singleton' μ₁ >>= 𝓛 (c₁.withInv 𝓘).to_pom,
        Distr.Keeps μ₁ ν₁ ∧ ∃ 𝓙₁', Framed 𝓘 𝓠₁ 𝓕 𝓙₁' ν₁ := by
    intro 𝓕 𝓙₁ μ₁ hf₁ ν₁ hν₁
    obtain ⟨hk, 𝓠, 𝓙₁', hf', -, hψ⟩ := h₁ μ₁ 𝓕 𝓙₁ True.intro hf₁ ν₁ hν₁
    exact ⟨hk, 𝓙₁', hf'.mono ((hQ₁ 𝓠).mpr hψ)⟩
  have hthread₂ : ∀ (𝓕 𝓙₂ : ProbSpace) (μ₂ : Distr Mem), Framed 𝓘 𝓟₂ 𝓕 𝓙₂ μ₂ →
      ∀ ν₂ ∈ ConvexPowerset.singleton' μ₂ >>= 𝓛 (c₂.withInv 𝓘).to_pom,
        Distr.Keeps μ₂ ν₂ ∧ ∃ 𝓙₂', Framed 𝓘 𝓠₂ 𝓕 𝓙₂' ν₂ := by
    intro 𝓕 𝓙₂ μ₂ hf₂ ν₂ hν₂
    obtain ⟨hk, 𝓠, 𝓙₂', hf', -, hψ⟩ := h₂ μ₂ 𝓕 𝓙₂ True.intro hf₂ ν₂ hν₂
    exact ⟨hk, 𝓙₂', hf'.mono ((hQ₂ 𝓠).mpr hψ)⟩
  -- The parallel composition is handled by Lemma C.6
  rw [Cmd.withInv, Cmd.to_pom] at hν
  obtain ⟨hk, 𝓙', hf''⟩ := lemma_C6 hf' hthread₁ hthread₂ ν hν
  -- The least models own no more variables than the preconditions of the two threads
  have hsub₁ : 𝓠₁.dom ⊆ 𝓟₁.dom := (ProbSpace.dom_mono ((hQ₁ _).mpr hψ₁')).trans hdom₁
  have hsub₂ : 𝓠₂.dom ⊆ 𝓟₂.dom := (ProbSpace.dom_mono ((hQ₂ _).mpr hψ₂')).trans hdom₂
  refine ⟨hk, 𝓠₁ ⊗ 𝓠₂, 𝓙', hf'', ?_,
    𝓠₁, 𝓠₂, hdisj.mono hsub₁ hsub₂, le_refl _, (hQ₁ 𝓠₁).mp (le_refl _), (hQ₂ 𝓠₂).mp (le_refl _)⟩
  exact (Set.union_subset_union hsub₁ hsub₂).trans (ProbSpace.dom_mono hle)

/- STRUCTURAL RULES -/

variable {ι : Type} [Countable ι] {𝓘 : Inv} {F : ProbSpace → Prop} {c : Cmd Act} {ξ : PMF ι} {φ ψ : OProp}

lemma wp_conseq (h : φ ⊢ ψ) : wp_base 𝓘 F c φ ⊢ wp_base 𝓘 F c ψ := by
  intro 𝓟 hc μ 𝓟fr 𝓙 hF hf ν hν
  have ⟨hk, 𝓠, 𝓙', hf', hdom, hφ⟩ := hc μ 𝓟fr 𝓙 hF hf ν hν
  exact ⟨hk, 𝓠, 𝓙', hf', hdom, h 𝓠 hφ⟩

/-- The `Split` rule: the weakest precondition distributes over outcome conjunctions.

The initial distribution is split into its conditionings on the summands of the
precondition; each is run separately, and the results (padded to the variables of the
precondition, and relabeled to disjoint outcomes) are glued back together. -/
lemma wp_split {ψ : ι → OProp} :
    (⨁[ ξ ] fun v ↦ wp_base 𝓘 F c (ψ v)) ⊢ wp_base 𝓘 F c (⨁[ ξ ] ψ) := by
  classical
  rintro 𝓟 ⟨𝓟s, V, hd, hdom, hsum, hwp⟩ μ 𝓟fr 𝓙 hF hf ν hν
  have hf' := hf.mono hsum
  obtain ⟨μ', hμ', rfl⟩ := Framed.split (hd := hd) hf'
  -- The run is the average of the runs from the conditioned distributions
  obtain ⟨μ₀, hμ₀, K, hK, rfl⟩ := ConvexPowerset.mem_bind.mp hν
  have hμ₀' : ξ.bind μ' = μ₀ := by
    have h' : μ₀ ∈ (ConvexPowerset.singleton' (ξ.bind μ')).set := hμ₀
    rw [ConvexPowerset.singleton'_set_eq] at h'
    exact proper_dist_maximal hf.refines.bot_0 h'
  subst hμ₀'
  have hsupp : ∀ i, ξ i ≠ 0 → (μ' i).support ⊆ (ξ.bind μ').support := fun i hi x hx ↦
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨i, (PMF.mem_support_iff _ _).mpr hi, hx⟩
  have hrun : ∀ i, ξ i ≠ 0 →
      (μ' i).bind K ∈ ConvexPowerset.singleton' (μ' i) >>= 𝓛 (c.withInv 𝓘).to_pom :=
    fun i hi ↦ ConvexPowerset.mem_bind.mpr ⟨μ' i, ConvexPowerset.self_mem_singleton' _, K,
      fun x hx ↦ hK x (hsupp i hi hx), rfl⟩
  -- The variables of the precondition are disjoint from the frame and the invariant
  have hVfr : Disjoint V 𝓟fr.dom := hf'.disj_frame
  have hVI : Disjoint V 𝓘.dom :=
    (Set.disjoint_union_left.mp hf'.disj_inv).1.mono_right
      (OProp.sure_forget 𝓘.footprint hf.inv).1
  -- Run each branch, and pad its postcondition to the variables `V`
  have hbr : ∀ i, ∃ 𝓠 𝓙' : ProbSpace, ξ i ≠ 0 →
      Distr.Keeps (μ' i) ((μ' i).bind K) ∧ Framed 𝓘 𝓠 𝓟fr 𝓙' ((μ' i).bind K) ∧
        𝓠.dom = V ∧ 𝓙'.dom = 𝓘.dom ∧ ψ i 𝓠 := by
    intro i
    by_cases hi : ξ i = 0
    · exact ⟨ProbSpace.unit, ProbSpace.unit, fun h ↦ absurd hi h⟩
    obtain ⟨hk, 𝓠, 𝓙', hfQ, hdomQ, hψ⟩ :=
      hwp i ((PMF.mem_support_iff _ _).mpr hi) _ 𝓟fr 𝓙 hF (hμ' i hi) _ (hrun i hi)
    obtain ⟨𝓙₀, hJ₀, -, hfQ⟩ := hfQ.shrink_inv
    have hown : Distr.Owns ((μ' i).bind K) V := hk V (hdom i ▸ (hμ' i hi).owns)
    obtain ⟨𝓠', hle, hdom', hfQ'⟩ := hfQ.pad hown hVfr (hJ₀ ▸ hVI)
    refine ⟨𝓠', 𝓙₀, fun _ ↦ ⟨hk, hfQ', ?_, hJ₀, (ψ i).mono hle hψ⟩⟩
    rw [hdom', Set.union_eq_right.mpr (hdomQ.trans (hdom i).subset)]
  choose 𝓠 𝓙' hbr using hbr
  -- Glue the branches back together
  obtain ⟨𝓠', hd', hdom', 𝓙'', hle, hfin⟩ := Framed.glue (ν := fun i ↦ (μ' i).bind K)
    (fun i hi ↦ (hbr i hi).2.1) (fun i hi ↦ (hbr i hi).2.2.1) (fun i hi ↦ (hbr i hi).2.2.2.1)
  change Distr.Keeps (ξ.bind μ') ((ξ.bind μ').bind K) ∧ _
  rw [PMF.bind_bind]
  refine ⟨fun D hD m hm ↦ ?_, ProbSpace.sum ξ 𝓠' V hd' hdom', 𝓙'', hfin,
    (show V ⊆ 𝓟.dom from ProbSpace.dom_mono hsum), 𝓠', V, hd', hdom', le_refl _, fun v hv ↦ ?_⟩
  · have hm' : (m : WithBot Mem) ∈ (ξ.bind fun i ↦ (μ' i).bind K).support :=
      (PMF.mem_support_iff _ _).mpr hm
    obtain ⟨i, hi, hmi⟩ := (PMF.mem_support_bind_iff _ _ _).mp hm'
    have hi' : ξ i ≠ 0 := (PMF.mem_support_iff _ _).mp hi
    exact (hbr i hi').1 D (fun m' hm'' ↦ hD m' (hsupp i hi' ((PMF.mem_support_iff _ _).mpr hm'')))
      m ((PMF.mem_support_iff _ _).mp hmi)
  · have hv' : ξ v ≠ 0 := (PMF.mem_support_iff _ _).mp hv
    exact (ψ v).mono (hle v hv') (hbr v hv').2.2.2.2

/-- The `NSplit` rule: the weakest precondition distributes over nondeterministic outcome
conjunctions. -/
lemma wp_nsplit {ψ : ι → OProp} :
    (& fun v ↦ wp_base 𝓘 F c (ψ v)) ⊢ wp_base 𝓘 F c (& ψ) := by
  rintro 𝓟 ⟨ξ, h⟩
  have hle : (⨁[ξ] ψ) ⊢ & ψ := fun _ h ↦ ⟨ξ, h⟩
  exact wp_conseq hle 𝓟 (wp_split (ξ := ξ) 𝓟 h)

lemma wp_weaken :
    wp 𝓘 c ψ ⊢ wp_weak 𝓘 c ψ := by
  intro 𝓟 hwp μ 𝓕 𝓙 _ hf ν hν
  exact hwp μ 𝓕 𝓙 True.intro hf ν hν

lemma wp_strengthen (h : ψ.Precise) :
    wp_weak 𝓘 c ψ ⊢ wp 𝓘 c ψ := by
  sorry

/-- The `Frame` rule: a frame that is independent of the program's resources is preserved. -/
lemma wp_frame :
    φ ∗ wp 𝓘 c ψ ⊢ wp 𝓘 c iprop(φ ∗ ψ) := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hd, hle, hφ, hwp⟩ μ 𝓕 𝓙 _ hf ν hν
  have hf' := hf.mono hle
  have hd₁ : Disjoint 𝓟₁.dom 𝓕.dom :=
    hf'.disj_frame.mono_left (Set.subset_union_left : 𝓟₁.dom ⊆ 𝓟₁.dom ∪ 𝓟₂.dom)
  -- Run the program with the frame extended by `𝓟₁`
  obtain ⟨hk, 𝓠, 𝓙', hf'', hdom, hψ⟩ := hwp μ (𝓟₁ ⊗ 𝓕) 𝓙 True.intro (hf'.right hd) ν hν
  have hd' : Disjoint 𝓟₁.dom 𝓠.dom :=
    (Set.disjoint_union_right.mp hf''.disj_frame).1.symm
  refine ⟨hk, 𝓟₁ ⊗ 𝓠, 𝓙', hf''.unright hd₁, ?_, 𝓟₁, 𝓠, hd', le_refl _, hφ, hψ⟩
  exact (Set.union_subset_union_right _ hdom).trans (ProbSpace.dom_mono hle)

/--
**Assignment rule that preserves the value of the assigned expression.**

If writing to `x` cannot change the value of `e` (hypothesis `he`), then the value of `e` is
still known after the assignment.  This is a strengthening of `wp_assign`, which only
returns the ownership of `e`; it is what makes it possible to re-establish an invariant that
constrains a variable read by the assignment.

After the assignment both `x` and `e` hold the value `v` deterministically, and they live in
disjoint parts of the memory, so the two certainties are returned as separate resources.
-/
lemma wp_assign_pres {𝓘 : Inv} {F : ProbSpace → Prop} (x : Var) (e : Expr) (ψ : OProp) (v : Val)
    (he : ∀ (σ : Mem) (w : Val), e (σ.extend x w) = e σ) :
    ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗
      ((iprop(⌈$ x == Expr.literal v⌉ ∗ ⌈e == Expr.literal v⌉)) -∗ ψ) ⊢
    wp_base 𝓘 F (x ::= e) ψ := sorry

/-- **Elimination of a nondeterministic choice in the precondition.**

If the postcondition is precise, then it is enough to establish the weakest precondition in
each branch of a nondeterministic choice. -/
lemma wp_nondet {κ : Type} [Countable κ] {ψ : OProp} (h : ψ.Precise) :
    OProp.nondet (fun (_ : κ) => wp_base 𝓘 F c ψ) ⊢ wp_base 𝓘 F c ψ :=
  Iris.BI.Entails.trans wp_nsplit (wp_conseq (OProp.nondet_collapse h))

lemma wp_exists {ι : Type} [Countable ι] {P : ι → MProp} :
    ((& fun i ↦ ⌈P i⌉) -∗ wp_base 𝓘 F c ψ)
    ⊢ ⌈ iprop( ∃ i, P i ) ⌉ -∗ wp_weak 𝓘 c ψ := by
  sorry

end Pcol
