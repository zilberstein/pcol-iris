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

/-- The `If` rule, when the guard is known to hold.  The guard must be monotone, so that its
value in the precondition is its value in the actual memories. -/
lemma wp_if_true {b : Expr} {c₁ c₂ : Cmd Act} {ψ : OProp} (hb : b.Mono) :
     ⌈b == Expr.literal 1⌉ ∧ wp_base 𝓘 F c₁ ψ ⊢ wp_base 𝓘 F (Cmd.if_stmt b c₁ c₂) ψ := by
  intro 𝓟 ⟨htrue, hwp⟩ μ 𝓟fr 𝓙 hF hf ν hν
  -- The guard holds in every initial memory
  have hb' : ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → b m = some 1 := fun m hm ↦ by
    obtain ⟨σ', hσ', -, hσ'b⟩ := Distr.Refines.sure hf.refines ((OProp.sure _).mono
      ((ProbSpace.le_product_left _ _).trans (ProbSpace.le_product_left _ _)) htrue) hm
    exact hb hσ' hσ'b
  refine hwp μ 𝓟fr 𝓙 hF hf ν ?_
  rw [Cmd.withInv, Cmd.to_pom, Pom.Semantics.lin_if_stmt] at hν
  obtain ⟨μ₀, hμ₀, K, hK, rfl⟩ := ConvexPowerset.mem_bind.mp hν
  have h' : μ₀ ∈ (ConvexPowerset.singleton' μ).set := hμ₀
  rw [ConvexPowerset.singleton'_set_eq] at h'
  obtain rfl := proper_dist_maximal hf.refines.bot_0 h'
  refine ConvexPowerset.mem_bind.mpr ⟨μ, hμ₀, K, fun y hy ↦ ?_, rfl⟩
  rcases y with _ | m
  · exact Set.mem_univ _
  · have htest : (Linearization.Sem.sem (Test.lift b) m : ConvexPowerset Bool) = pure true := by
      change (match b m with
        | some q => pure (decide (q ≠ 0))
        | none => ⊥ : ConvexPowerset Bool) = _
      rw [hb' m ((PMF.mem_support_iff _ _).mp hy)]
      norm_num
    have hK' : K m ∈ ((Linearization.Sem.sem (Test.lift b) m : ConvexPowerset Bool) >>=
        fun r ↦ (bif r then 𝓛 (c₁.withInv 𝓘).to_pom m else 𝓛 (c₂.withInv 𝓘).to_pom m :
          ConvexPowerset Mem)) := hK (m : WithBot Mem) hy
    rw [htest, ConvexPowerset.pure_bind] at hK'
    exact hK'

/-- A run of an assignment `x := e`, from a distribution framed with `𝓟₁ ⊗ 𝓟₂` where `e` is
known to have the value `v` in `𝓟₁`, is framed with `𝓟₁` updated by `x := v`, and `𝓟₂`. -/
lemma assign_run {x : Var} {e : Expr} {v : Val} (he : e.Mono) {𝓟₁ 𝓟₂ 𝓟fr 𝓙 : ProbSpace}
    {μ ν : Distr Mem} (hpre : ⌈e == Expr.literal v ∧ own ($ x)⌉ 𝓟₁)
    (hf₁ : Framed 𝓘 (𝓟₁ ⊗ 𝓟₂) 𝓟fr 𝓙 μ)
    (hν : ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 ((x ::= e).withInv 𝓘).to_pom) :
    ∃ hx : x ∈ 𝓟₁.dom, Distr.Keeps μ ν ∧
      ∃ T, Framed 𝓘 (𝓟₁.assign x v hx ⊗ 𝓟₂) 𝓟fr T ν := by
  change ν ∈ ConvexPowerset.singleton' μ >>=
    𝓛 (Pom.singleton (Label.act (⟨Act.assign x e, 𝓘⟩ : WithInv Act))) at hν
  rw [Pom.lin_act] at hν
  obtain ⟨K, rfl, hK⟩ := run_act hf₁.refines.bot_0 hν
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
      have hev : e (τ ⊎ m) = some v := he (hσ'.trans hle') hσ'e
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
    · exact absurd hf₁.refines.bot_0 ((PMF.mem_support_iff _ _).mp hy)
    · have hm : μ (m : WithBot Mem) ≠ 0 := (PMF.mem_support_iff _ _).mp hy
      obtain ⟨τ, hτ, h⟩ := hKm m hm _ hm''y
      exact ⟨m, τ, hm, hτ, Option.some.inj h⟩
  refine ⟨hx, fun D hD m'' hm'' ↦ ?_, ?_⟩
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
  refine ⟨T, hTinv, hf₁.disj_frame, ?_, hTref⟩
  rw [hT]; exact h𝓐I

/-- The `Assign` rule.  The expression must be local (`Expr.Local`): its value is known in
the precondition, and must not be changed by interference on the invariant's variables. -/
lemma wp_assign (x : Var) (e : Expr) (ψ : OProp) (v : Val) (he : e.Local) :
    ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗ ((⌈$ x == Expr.literal v ∧ own e⌉) -∗ ψ) ⊢
      wp_base 𝓘 F (x ::= e) ψ := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hd, hle, hpre, hwand⟩ μ 𝓟fr 𝓙 _ hf ν hν
  obtain ⟨hx, hk, T, hfT⟩ := assign_run he.mono hpre (hf.mono hle) hν
  set 𝓡 := 𝓟₁.assign x v hx
  have h𝓡 : OProp.sure iprop($ x == Expr.literal v ∧ own e) 𝓡 := by
    intro k hk
    obtain ⟨σ', hσ', hσ'd, -⟩ := (hpre hk).1
    refine ⟨Expr.var_equals_literal_iff.mpr (Mem.extend_apply_self _ _ _), ?_⟩
    exact ⟨σ'.extend x v, Mem.extend_mono hσ' x v, he.extend x v hσ'd⟩
  exact ⟨hk, 𝓡 ⊗ 𝓟₂, T, hfT, (show 𝓟₁.dom ∪ 𝓟₂.dom ⊆ 𝓟.dom from ProbSpace.dom_mono hle),
    ψ.mono (ProbSpace.product_comm hd) (hwand 𝓡 hd.symm h𝓡)⟩

/-- A run of a sampling `x :≈ Bern e`, from a distribution framed with `𝓟₁ ⊗ 𝓟₂` where `e`
is known to have the value `v` in `𝓟₁`, is framed with `𝓟₁` without `x`, an independent
sample of `x`, and `𝓟₂`. -/
lemma bern_run {x : Var} {e : Expr} {v : Val} (he : e.Mono) {𝓟₁ 𝓟₂ 𝓟fr 𝓙 : ProbSpace}
    {μ ν : Distr Mem} (hd : Disjoint 𝓟₁.dom 𝓟₂.dom)
    (hpre : ⌈e == Expr.literal v ∧ own ($ x)⌉ 𝓟₁)
    (hf₁ : Framed 𝓘 (𝓟₁ ⊗ 𝓟₂) 𝓟fr 𝓙 μ)
    (hν : ν ∈ ConvexPowerset.singleton' μ >>= 𝓛 ((x :≈ PExpr.Bern e).withInv 𝓘).to_pom) :
    x ∈ 𝓟₁.dom ∧ Distr.Keeps μ ν ∧
      ∃ T, Framed 𝓘 ((𝓟₁.restrictDom (𝓟₁.dom \ {x}) Set.sdiff_subset ⊗
        sampleSpace x (Bern v)) ⊗ 𝓟₂) 𝓟fr T ν := by
  classical
  change ν ∈ ConvexPowerset.singleton' μ >>=
    𝓛 (Pom.singleton (Label.act (⟨Act.samp x (PExpr.Bern e), 𝓘⟩ : WithInv Act))) at hν
  rw [Pom.lin_act] at hν
  obtain ⟨K, rfl, hK⟩ := run_act hf₁.refines.bot_0 hν
  -- The program's part of the space, with the frame
  set 𝓐 := (𝓟₁ ⊗ 𝓟₂) ⊗ 𝓟fr with h𝓐def
  have h𝓐 : 𝓐 ≼ μ := Distr.Refines.mono (ProbSpace.le_product_left _ _) hf₁.refines
  have hIJ : 𝓘.dom ⊆ 𝓙.dom := (OProp.sure_forget 𝓘.footprint hf₁.inv).1
  have h𝓐I : Disjoint 𝓐.dom 𝓘.dom := hf₁.disj_inv.mono_right hIJ
  have hIμ : ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → 𝓘.prop (m.restrict 𝓘.dom) := fun m hm ↦
    Distr.Refines.sure hf₁.refines ((OProp.sure 𝓘.to_MProp).mono
      (ProbSpace.le_product_right hf₁.disj_inv) hf₁.inv) hm
  have h𝓟₁𝓐 : 𝓟₁ ≤ 𝓐 :=
    (ProbSpace.le_product_left 𝓟₁ 𝓟₂).trans (ProbSpace.le_product_left _ _)
  have hpre𝓐 := (OProp.sure _).mono h𝓟₁𝓐 hpre
  have hx : x ∈ 𝓟₁.dom := by
    obtain ⟨k, hk⟩ := ProbSpace.support_nonempty 𝓟₁
    rw [← 𝓟₁.dom_valid k, Mem.mem_dom_iff]
    exact Option.isSome_iff_ne_none.mp (MProp.own_var_iff.mp (hpre hk).2)
  have hx𝓐 : x ∈ 𝓐.dom := Or.inl (Or.inl hx)
  have hxI : x ∉ 𝓘.dom := fun h ↦ Set.disjoint_left.mp h𝓐I hx𝓐 h
  -- The interference, followed by the sampling
  have hKm : ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → ∃ ρ ∈ 𝓘.replace m,
      K m = ρ.bind (ConvexPowerset.botElim (sampleDistr x (Bern v))) := by
    intro m hm
    obtain ⟨i, hi, him⟩ := Distr.Refines.exists_le h𝓐 hm
    obtain ⟨σ', hσ', -, hσ'e⟩ := (hpre𝓐 hi).1
    refine sem_samp_withInv (hIμ m hm) hxI (fun τ hτ ↦ ?_) (K m) (hK m hm)
    have hle' : 𝓐.state i ≤ (τ ⊎ m) := Mem.le_union_of_le him
      (by rw [𝓘.dom_valid hτ, 𝓐.dom_valid]; exact h𝓐I.symm)
    exact he (hσ'.trans hle') hσ'e
  choose ρ hρ hKρ using hKm
  let R : WithBot Mem → Distr Mem := ConvexPowerset.botElim fun m ↦
    if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none
  have hsplit : μ.bind K = (μ.bind R).bind (ConvexPowerset.botElim (sampleDistr x (Bern v))) := by
    rw [PMF.bind_bind]
    refine Distr.bind_congr_support' μ fun y hy ↦ ?_
    rcases y with _ | m
    · exact absurd hf₁.refines.bot_0 ((PMF.mem_support_iff _ _).mp hy)
    · have hm : μ (m : WithBot Mem) ≠ 0 := (PMF.mem_support_iff _ _).mp hy
      change K m = (if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none).bind _
      rw [dif_pos hm]; exact hKρ m hm
  -- The memories after the interference
  have hR : ∀ y ∈ (μ.bind R).support, ∃ (m τ : Mem), μ (m : WithBot Mem) ≠ 0 ∧ 𝓘.prop τ ∧
      y = ((τ ⊎ m : Mem) : WithBot Mem) := by
    intro y hy
    obtain ⟨z, hz, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
    rcases z with _ | m
    · exact absurd hf₁.refines.bot_0 ((PMF.mem_support_iff _ _).mp hz)
    · have hm : μ (m : WithBot Mem) ≠ 0 := (PMF.mem_support_iff _ _).mp hz
      change y ∈ (if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none).support at hy
      rw [dif_pos hm] at hy
      obtain ⟨σ', ⟨τ, hτ, rfl⟩, rfl⟩ := Inv.replace_supportedIn (hIμ m hm) _ (hρ m hm) y hy
      exact ⟨m, τ, hm, hτ, rfl⟩
  -- The spaces after the run
  set 𝓟₁' := 𝓟₁.restrictDom (𝓟₁.dom \ {x}) Set.sdiff_subset
  set B := sampleSpace x (Bern v)
  set 𝓐' := (𝓟₁' ⊗ 𝓟₂) ⊗ 𝓟fr
  have h123 : Disjoint (𝓟₁.dom ∪ 𝓟₂.dom) 𝓟fr.dom := hf₁.disj_frame
  have h1f : Disjoint 𝓟₁.dom 𝓟fr.dom := h123.mono_left Set.subset_union_left
  have h2f : Disjoint 𝓟₂.dom 𝓟fr.dom := h123.mono_left Set.subset_union_right
  have hxB : B.dom = {x} := rfl
  have h1'B : Disjoint 𝓟₁'.dom B.dom := by rw [hxB]; exact Set.disjoint_sdiff_left
  have h1'2 : Disjoint 𝓟₁'.dom 𝓟₂.dom := hd.mono_left Set.sdiff_subset
  have h1'f : Disjoint 𝓟₁'.dom 𝓟fr.dom := h1f.mono_left Set.sdiff_subset
  have h2B : Disjoint 𝓟₂.dom B.dom := by
    rw [hxB]; exact Set.disjoint_singleton_right.mpr fun h ↦ Set.disjoint_left.mp hd hx h
  have hfB : Disjoint 𝓟fr.dom B.dom := by
    rw [hxB]; exact Set.disjoint_singleton_right.mpr fun h ↦ Set.disjoint_left.mp h1f hx h
  have hsub1 : 𝓟₁'.dom ∪ B.dom ⊆ 𝓟₁.dom :=
    Set.union_subset Set.sdiff_subset (by rw [hxB]; exact Set.singleton_subset_iff.mpr hx)
  have hx𝓐' : x ∉ 𝓐'.dom := by
    rintro ((⟨-, h⟩ | h) | h)
    · exact h rfl
    · exact Set.disjoint_left.mp hd hx h
    · exact Set.disjoint_left.mp h1f hx h
  have h𝓐'le : ∀ i, 𝓐'.state i ≤ 𝓐.state i := fun i ↦ by
    simp only [𝓐', 𝓐, ProbSpace.product_state]
    refine Mem.union_mono (Mem.union_mono (Mem.restrict_le _ _) le_rfl ?_) le_rfl ?_
    · rw [𝓟₁.dom_valid, 𝓟₂.dom_valid]; exact hd
    · rw [Mem.dom_union, 𝓟₁.dom_valid, 𝓟₂.dom_valid, 𝓟fr.dom_valid]; exact h123
  -- The interference refines the program's part of the space without `x`
  have hA : 𝓐' ≼ μ.bind R := by
    refine Distr.Refines.bind (𝓐' := 𝓐') h𝓐 (fun E h ↦ h) (fun E _ ↦ rfl)
      fun i _ m hm him y hy ↦ ?_
    change y ∈ (if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none).support at hy
    rw [dif_pos hm] at hy
    obtain ⟨σ', ⟨τ, hτ, rfl⟩, rfl⟩ := Inv.replace_supportedIn (hIμ m hm) _ (hρ m hm) y hy
    refine ⟨_, rfl, (h𝓐'le i).trans (Mem.le_union_of_le him ?_)⟩
    rw [𝓘.dom_valid hτ, 𝓐.dom_valid]; exact h𝓐I.symm
  -- The sample is independent of it
  have hAB := Distr.Refines.prod hA (sampleSpace_refines x (Bern v))
    (by rw [hxB]; exact Set.disjoint_singleton_right.mpr hx𝓐')
    (c := fun a b ↦ (b.restrict {x} ⊎ a)) fun a b ha hb ↦ by
      refine ⟨?_, Mem.union_le (Mem.le_union_of_le (Mem.restrict_le _ _) ?_)
        (Mem.le_union_left _ _)⟩
      · rw [Mem.dom_union, Mem.restrict_dom]
        exact Set.union_subset (ha.trans Set.subset_union_right)
          fun y hy ↦ Or.inl ⟨hb hy, hy⟩
      · exact (Set.disjoint_singleton_left.mpr hx𝓐').mono (Mem.dom_restrict_subset _ _)
          (Mem.dom_restrict_subset _ _)
  have href : (𝓐' ⊗ B) ≼ μ.bind K := by
    rw [hsplit]
    convert hAB using 1
    refine Distr.bind_congr_support' _ fun y hy ↦ ?_
    obtain ⟨m, τ, -, -, rfl⟩ := hR y hy
    change PMF.map (fun b ↦ ((((τ ⊎ m).extend x b) : Mem) : WithBot Mem)) (Bern v) =
      PMF.map (Distr.liftMem _ _) (PMF.map _ (Bern v))
    rw [PMF.map_comp]
    congr 1
    funext u
    simp only [Function.comp_apply]
    change (((τ ⊎ m).extend x u : Mem) : WithBot Mem) =
      (((Mem.singleton x u).restrict {x} ⊎ (τ ⊎ m) : Mem) : WithBot Mem)
    rw [Mem.restrict_eq_self (dom_singleton x u).subset, Mem.singleton_union]
  -- The final memories
  have hfin : ∀ m'' : Mem, (μ.bind K) (m'' : WithBot Mem) ≠ 0 →
      ∃ (m τ : Mem) (b : Val), μ (m : WithBot Mem) ≠ 0 ∧ 𝓘.prop τ ∧
        m'' = (τ ⊎ m).extend x b := by
    intro m'' hm''
    rw [hsplit] at hm''
    obtain ⟨y, hy, hm''y⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hm'')
    obtain ⟨m, τ, hm, hτ, rfl⟩ := hR y hy
    obtain ⟨b, -, hb⟩ := (PMF.mem_support_map_iff _ _ _).mp hm''y
    exact ⟨m, τ, b, hm, hτ, (WithBot.coe_injective hb).symm⟩
  refine ⟨hx, fun D hD m'' hm'' ↦ ?_, ?_⟩
  · obtain ⟨m, τ, b, hm, -, rfl⟩ := hfin m'' hm''
    rw [Mem.dom_extend, Mem.dom_union]
    exact (hD m hm).trans (Set.subset_union_right.trans (Set.subset_insert _ _))
  -- The invariant's part of the space after the run
  obtain ⟨T, hT, hTref, hTst⟩ := Distr.Refines.pad href (U := 𝓘.dom) fun m'' hm'' ↦ by
    obtain ⟨m, τ, b, -, hτ, rfl⟩ := hfin m'' hm''
    rw [Mem.dom_extend, Mem.dom_union, 𝓘.dom_valid hτ]
    exact Set.subset_union_left.trans (Set.subset_insert _ _)
  have hTinv : OProp.sure 𝓘.to_MProp T := fun k _ ↦ by
    obtain ⟨m'', hm'', heq⟩ := hTst k
    obtain ⟨m, τ, b, -, hτ, rfl⟩ := hfin m'' hm''
    change 𝓘.prop ((T.state k).restrict 𝓘.dom)
    rw [heq, Mem.restrict_restrict, Set.inter_self, Mem.restrict_extend_of_notMem b hxI,
      Mem.restrict_union_left (𝓘.dom_valid hτ)]
    exact hτ
  -- Rearranging the factors
  have hre : (((𝓟₁' ⊗ B) ⊗ 𝓟₂) ⊗ 𝓟fr) ≤ (𝓐' ⊗ B) :=
    (ProbSpace.product_mono_left
      (ProbSpace.product_swap_right h2B (Set.disjoint_union_right.mpr ⟨h1'2, h1'B⟩))
      (Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨h1'f, h2f⟩, hfB.symm⟩)).trans
      (ProbSpace.product_swap_right hfB (Set.disjoint_union_left.mpr
        ⟨Set.disjoint_union_right.mpr ⟨h1'f, h1'B⟩, Set.disjoint_union_right.mpr ⟨h2f, h2B⟩⟩))
  have hsub𝓐 : ((𝓟₁'.dom ∪ B.dom) ∪ 𝓟₂.dom) ∪ 𝓟fr.dom ⊆ 𝓐.dom :=
    Set.union_subset_union_left _ (Set.union_subset_union_left _ hsub1)
  refine ⟨T, hTinv, ?_, ?_, Distr.Refines.mono (ProbSpace.product_mono_left hre ?_) hTref⟩
  · exact Set.disjoint_union_left.mpr ⟨h1f.mono_left hsub1, h2f⟩
  · rw [hT]; exact h𝓐I.mono_left hsub𝓐
  · rw [hT]
    refine Set.disjoint_union_left.mpr ⟨h𝓐I.mono_left ?_, ?_⟩
    · exact Set.union_subset_union_left _
        (Set.union_subset_union_left _ (Set.sdiff_subset : 𝓟₁'.dom ⊆ 𝓟₁.dom))
    · rw [hxB]; exact Set.disjoint_singleton_left.mpr hxI

/-- The `Bern` rule: sampling `x` makes it distributed as `Bern v`, independently of the rest
of the state.  As for assignments, the expression must be local. -/
lemma wp_bern (x : Var) (e : Expr) (v : Val) {ψ : OProp} (he : e.Local) :
    ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗ (($ x ~ Bern v ∧ ⌈own e⌉) -∗ ψ) ⊢
    wp_base 𝓘 F (x :≈ PExpr.Bern e) ψ := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hd, hle, hpre, hwand⟩ μ 𝓟fr 𝓙 _ hf ν hν
  obtain ⟨hx, hk, T, hfT⟩ := bern_run he.mono hd hpre (hf.mono hle) hν
  set 𝓟₁' := 𝓟₁.restrictDom (𝓟₁.dom \ {x}) Set.sdiff_subset
  set 𝓡 := 𝓟₁' ⊗ sampleSpace x (Bern v)
  have h1'B : Disjoint 𝓟₁'.dom (sampleSpace x (Bern v)).dom := Set.disjoint_sdiff_left
  have hsub : 𝓡.dom ⊆ 𝓟₁.dom :=
    Set.union_subset Set.sdiff_subset (Set.singleton_subset_iff.mpr hx)
  have h𝓡 : iprop(($ x ~ Bern v) ∧ ⌈own e⌉) 𝓡 := by
    refine ⟨(OProp.distributed_as ($ x) (Bern v)).mono (ProbSpace.le_product_right h1'B)
      (sampleSpace_distributed x _), fun k hk ↦ ?_⟩
    rw [ProbSpace.support_product] at hk
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hk
    obtain ⟨u, hu⟩ := sampleSpace_state hb
    obtain ⟨σ', hσ', hσ'd, -⟩ := (hpre ha).1
    change own e (𝓡.state (Nat.pairEquiv (a, b)))
    rw [ProbSpace.product_state, Equiv.symm_apply_apply, hu]
    refine ⟨σ'.extend x u, ?_, he.extend x u hσ'd⟩
    have := Mem.extend_le_restrict_union hσ' x u
    rwa [𝓟₁.dom_valid] at this
  exact ⟨hk, 𝓡 ⊗ 𝓟₂, T, hfT,
    (Set.union_subset_union_left _ hsub).trans
      (show 𝓟₁.dom ∪ 𝓟₂.dom ⊆ 𝓟.dom from ProbSpace.dom_mono hle),
    ψ.mono (ProbSpace.product_comm (hd.mono_left hsub)) (hwand 𝓡 (hd.mono_left hsub).symm h𝓡)⟩

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
  have hf₁ := hf.mono hle
  have h12f : Disjoint (𝓟₁.dom ∪ 𝓟₂.dom) 𝓟fr.dom := hf₁.disj_frame
  have h12fJ : Disjoint ((𝓟₁.dom ∪ 𝓟₂.dom) ∪ 𝓟fr.dom) 𝓙.dom := hf₁.disj_inv
  have h1f : Disjoint 𝓟₁.dom 𝓟fr.dom := h12f.mono_left Set.subset_union_left
  have h2J : Disjoint 𝓟₂.dom 𝓙.dom :=
    h12fJ.mono_left (Set.subset_union_right.trans Set.subset_union_left)
  have hfJ : Disjoint 𝓟fr.dom 𝓙.dom := h12fJ.mono_left Set.subset_union_right
  -- The shared resource becomes part of the invariant's space
  have hf' : Framed 𝓘 𝓟₂ 𝓟fr (𝓟₁ ⊗ 𝓙) μ := by
    refine ⟨(OProp.sure _).mono (ProbSpace.le_product_left _ _) h𝓘,
      h12f.mono_left Set.subset_union_right, ?_, ?_⟩
    · change Disjoint (𝓟₂.dom ∪ 𝓟fr.dom) (𝓟₁.dom ∪ 𝓙.dom)
      exact Set.disjoint_union_left.mpr ⟨Set.disjoint_union_right.mpr ⟨hdisj.symm, h2J⟩,
        Set.disjoint_union_right.mpr ⟨h1f.symm, hfJ⟩⟩
    · refine Distr.Refines.mono ((ProbSpace.product_assoc' _ _ _).trans
        (ProbSpace.product_mono_left ?_ h12fJ)) hf₁.refines
      exact (ProbSpace.product_comm (Set.disjoint_union_right.mpr ⟨hdisj, h1f⟩)).trans
        (ProbSpace.product_assoc' _ _ _)
  obtain ⟨hk, 𝓠, 𝓙', hfQ, hdomQ, hψ⟩ := hwp μ 𝓟fr (𝓟₁ ⊗ 𝓙) hF hf' ν hν'
  obtain ⟨𝓙₀, hJ₀, -, hfQ₀⟩ := hfQ.shrink_inv
  have h𝓘dom : 𝓘.dom ⊆ 𝓟₁.dom := (OProp.sure_forget 𝓘.footprint h𝓘).1
  have hQJ : Disjoint 𝓠.dom 𝓙₀.dom := hfQ₀.disj_inv.mono_left Set.subset_union_left
  have hfJ₀ : Disjoint 𝓟fr.dom 𝓙₀.dom := hfQ₀.disj_inv.mono_left Set.subset_union_right
  refine ⟨hk, 𝓠 ⊗ 𝓙₀, ProbSpace.unit, ⟨fun k _ ↦ ?_, ?_, ?_, ?_⟩, ?_,
    𝓠, 𝓙₀, hQJ, le_refl _, hψ, hfQ₀.inv⟩
  · change Mem.dom _ = ∅
    rw [Mem.restrict_dom]; exact Set.inter_empty _
  · exact Set.disjoint_union_left.mpr ⟨hfQ₀.disj_frame, hfJ₀.symm⟩
  · exact Set.disjoint_empty _
  · refine Distr.Refines.mono ?_ hfQ₀.refines
    exact ((ProbSpace.product_comm (Set.empty_disjoint _)).trans
      (ProbSpace.product_unit_le _)).trans (ProbSpace.product_swap_right hfJ₀
        (Set.disjoint_union_right.mpr ⟨hfQ₀.disj_frame, hQJ⟩))
  · change 𝓠.dom ∪ 𝓙₀.dom ⊆ 𝓟.dom
    rw [hJ₀]
    exact (Set.union_subset (hdomQ.trans Set.subset_union_right)
      (h𝓘dom.trans Set.subset_union_left)).trans (ProbSpace.dom_mono hle)

/-- The `Atom` rule: an atomic action may open the invariant, provided it re-establishes it.

A run of the action under the invariant consists of interference on the invariant's
variables, the action itself and a check of the invariant.  The distribution after the
interference is framed with the precondition and a space satisfying the invariant, from which
the action runs without interference; the nondeterministic choices of the action made from
different initial memories are averaged (`ConvexPowerset.mem_bind_of_mixture`). -/
lemma wp_atom {𝓘 : Inv} {F : ProbSpace → Prop} {a : Act} {ψ : OProp} :
    (OProp.sure 𝓘.to_MProp -∗ wp_base Inv.emp F (Cmd.act a) (iprop(ψ ∗ OProp.sure 𝓘.to_MProp)))
    ⊢ wp_base 𝓘 F (Cmd.act a) ψ := by
  classical
  intro 𝓟 hwand μ 𝓟fr 𝓙 hF hf ν hν
  change ν ∈ ConvexPowerset.singleton' μ >>=
    𝓛 (Pom.singleton (Label.act (⟨a, 𝓘⟩ : WithInv Act))) at hν
  rw [Pom.lin_act] at hν
  obtain ⟨K, rfl, hK⟩ := run_act hf.refines.bot_0 hν
  set 𝓐 := 𝓟 ⊗ 𝓟fr with h𝓐def
  have h𝓐 : 𝓐 ≼ μ := Distr.Refines.mono (ProbSpace.le_product_left _ _) hf.refines
  have hIJ : 𝓘.dom ⊆ 𝓙.dom := (OProp.sure_forget 𝓘.footprint hf.inv).1
  have h𝓐I : Disjoint 𝓐.dom 𝓘.dom := hf.disj_inv.mono_right hIJ
  have hIμ : ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → 𝓘.prop (m.restrict 𝓘.dom) := fun m hm ↦
    Distr.Refines.sure hf.refines ((OProp.sure 𝓘.to_MProp).mono
      (ProbSpace.le_product_right hf.disj_inv) hf.inv) hm
  -- Each run: interference, then the action, then the check
  have hdec : ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → ∃ ρ ∈ 𝓘.replace m,
      ∃ f : WithBot Mem → Distr Mem, (∀ x : Mem, (↑x : WithBot Mem) ∈ PMF.support ρ →
        f x ∈ (Linearization.Sem.sem a x >>= fun τ ↦ 𝓘.check τ : ConvexPowerset Mem)) ∧ K m = ρ.bind f :=
    fun m hm ↦ sem_withInv_decomp (hIμ m hm) _ (hK m hm)
  choose ρ hρ f hf' hKf using hdec
  let R : WithBot Mem → Distr Mem := ConvexPowerset.botElim fun m ↦
    if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none
  let G : WithBot Mem → WithBot Mem → Distr Mem := fun y ↦ Option.elim y (fun _ ↦ PMF.pure none)
    fun m ↦ if h : μ (m : WithBot Mem) ≠ 0 then f m h else fun _ ↦ PMF.pure none
  have hKRG : μ.bind K = μ.bind fun y ↦ (R y).bind (G y) := by
    refine Distr.bind_congr_support' μ fun y hy ↦ ?_
    rcases y with _ | m
    · exact absurd hf.refines.bot_0 ((PMF.mem_support_iff _ _).mp hy)
    · have hm : μ (m : WithBot Mem) ≠ 0 := (PMF.mem_support_iff _ _).mp hy
      change K m = (if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none).bind
        (if h : μ (m : WithBot Mem) ≠ 0 then f m h else fun _ ↦ PMF.pure none)
      rw [dif_pos hm, dif_pos hm]; exact hKf m hm
  set ρ' : Distr Mem := μ.bind R with hρ'def
  have hρsupp : ∀ (m : Mem) (hm : μ (m : WithBot Mem) ≠ 0) y, y ∈ PMF.support (ρ m hm) →
      y ∈ ρ'.support :=
    fun m hm y hy ↦ (PMF.mem_support_bind_iff _ _ _).mpr ⟨m, (PMF.mem_support_iff _ _).mpr hm,
      by change y ∈ (if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none).support
         rw [dif_pos hm]; exact hy⟩
  -- The memories after the interference
  have hR : ∀ y ∈ ρ'.support, ∃ (m τ : Mem), μ (m : WithBot Mem) ≠ 0 ∧ 𝓘.prop τ ∧
      y = ((τ ⊎ m : Mem) : WithBot Mem) := by
    intro y hy
    obtain ⟨z, hz, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
    rcases z with _ | m
    · exact absurd hf.refines.bot_0 ((PMF.mem_support_iff _ _).mp hz)
    · have hm : μ (m : WithBot Mem) ≠ 0 := (PMF.mem_support_iff _ _).mp hz
      change y ∈ (if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none).support at hy
      rw [dif_pos hm] at hy
      obtain ⟨σ', ⟨τ, hτ, rfl⟩, rfl⟩ := Inv.replace_supportedIn (hIμ m hm) _ (hρ m hm) y hy
      exact ⟨m, τ, hm, hτ, rfl⟩
  -- After the interference, the precondition and the frame are unchanged, and a space
  -- without probabilistic information satisfies the invariant
  have hA : 𝓐 ≼ ρ' := by
    refine Distr.Refines.bind (𝓐' := 𝓐) h𝓐 (fun E h ↦ h) (fun E _ ↦ rfl)
      fun i _ m hm him y hy ↦ ?_
    change y ∈ (if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none).support at hy
    rw [dif_pos hm] at hy
    obtain ⟨σ', ⟨τ, hτ, rfl⟩, rfl⟩ := Inv.replace_supportedIn (hIμ m hm) _ (hρ m hm) y hy
    refine ⟨_, rfl, Mem.le_union_of_le him ?_⟩
    rw [𝓘.dom_valid hτ, 𝓐.dom_valid]; exact h𝓐I.symm
  obtain ⟨T, hT, hTref, hTst⟩ := Distr.Refines.pad hA (U := 𝓘.dom) fun m'' hm'' ↦ by
    obtain ⟨m, τ, -, hτ, hy⟩ := hR _ ((PMF.mem_support_iff _ _).mpr hm'')
    cases WithBot.coe_injective hy
    rw [Mem.dom_union, 𝓘.dom_valid hτ]
    exact Set.subset_union_left
  have hTinv : OProp.sure 𝓘.to_MProp T := fun k _ ↦ by
    obtain ⟨m'', hm'', heq⟩ := hTst k
    obtain ⟨m, τ, -, hτ, hy⟩ := hR _ ((PMF.mem_support_iff _ _).mpr hm'')
    cases WithBot.coe_injective hy
    change 𝓘.prop ((T.state k).restrict 𝓘.dom)
    rw [heq, Mem.restrict_restrict, Set.inter_self, Mem.restrict_union_left (𝓘.dom_valid hτ)]
    exact hτ
  have hPT : Disjoint 𝓟.dom T.dom := by rw [hT]; exact h𝓐I.mono_left Set.subset_union_left
  have hfT : Disjoint 𝓟fr.dom T.dom := by rw [hT]; exact h𝓐I.mono_left Set.subset_union_right
  have hwp := hwand T hPT hTinv
  have hfe : Framed Inv.emp (𝓟 ⊗ T) 𝓟fr ProbSpace.unit ρ' := by
    refine ⟨fun k _ ↦ ?_, Set.disjoint_union_left.mpr ⟨hf.disj_frame, hfT.symm⟩,
      Set.disjoint_empty _, Distr.Refines.mono ?_ hTref⟩
    · change Mem.dom _ = ∅
      rw [Mem.restrict_dom]; exact Set.inter_empty _
    · exact ((ProbSpace.product_comm (Set.empty_disjoint _)).trans
        (ProbSpace.product_unit_le _)).trans (ProbSpace.product_swap_right hfT
          (Set.disjoint_union_right.mpr ⟨hf.disj_frame, hPT⟩))
  -- Every run of the action from the interfered distribution re-establishes the invariant
  have hgood : ∀ x : Mem, (↑x : WithBot Mem) ∈ ρ'.support →
      ∀ g ∈ (Linearization.Sem.sem a x : ConvexPowerset Mem), ∀ y ∈ PMF.support g,
        ∃ m'' : Mem, y = m'' ∧ 𝓘.prop (m''.restrict 𝓘.dom) := by
    intro x hx g hg y hy
    let Kg : WithBot Mem → Distr Mem := fun z ↦ if z = (x : WithBot Mem) then g else
      Option.elim z (PMF.pure none) fun x' ↦
        (Linearization.Sem.sem (⟨a, Inv.emp⟩ : WithInv Act) x' : ConvexPowerset Mem).nonempty.some
    have hν'' : ρ'.bind Kg ∈ ConvexPowerset.singleton' ρ' >>=
        𝓛 ((Cmd.act a).withInv Inv.emp).to_pom := by
      change _ ∈ ConvexPowerset.singleton' ρ' >>=
        𝓛 (Pom.singleton (Label.act (⟨a, Inv.emp⟩ : WithInv Act)))
      rw [Pom.lin_act]
      refine ConvexPowerset.mem_bind.mpr ⟨ρ', ConvexPowerset.self_mem_singleton' _, Kg,
        fun z _ ↦ ?_, rfl⟩
      rcases z with _ | x'
      · exact Set.mem_univ _
      · change Kg x' ∈ (Linearization.Sem.sem (⟨a, Inv.emp⟩ : WithInv Act) x' : ConvexPowerset Mem)
        by_cases hxx : (x' : WithBot Mem) = x
        · simp only [Kg, if_pos hxx]
          cases WithBot.coe_injective hxx
          rw [sem_withInv_emp]; exact hg
        · simp only [Kg, if_neg hxx]
          exact Set.Nonempty.some_mem _
    obtain ⟨-, 𝓠, 𝓙', hfQ, -, 𝓠₁, 𝓠₂, hd12, hle12, -, hI2⟩ :=
      hwp ρ' 𝓟fr ProbSpace.unit hF hfe _ hν''
    have hyν : y ∈ (ρ'.bind Kg).support := (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨x, hx, by simp only [Kg, if_pos rfl]; exact hy⟩
    rcases y with _ | m''
    · exact absurd hfQ.refines.bot_0 ((PMF.mem_support_iff _ _).mp hyν)
    · refine ⟨m'', rfl, Distr.Refines.sure hfQ.refines ((OProp.sure 𝓘.to_MProp).mono ?_ hI2)
        ((PMF.mem_support_iff _ _).mp hyν)⟩
      exact ((ProbSpace.le_product_right hd12).trans hle12).trans
        ((ProbSpace.le_product_left _ _).trans (ProbSpace.le_product_left _ _))
  -- The actual run is a run of the action from the interfered distribution
  have hν' : μ.bind K ∈ ConvexPowerset.singleton' ρ' >>=
      𝓛 ((Cmd.act a).withInv Inv.emp).to_pom := by
    change _ ∈ ConvexPowerset.singleton' ρ' >>=
      𝓛 (Pom.singleton (Label.act (⟨a, Inv.emp⟩ : WithInv Act)))
    rw [Pom.lin_act, hKRG]
    refine ConvexPowerset.mem_bind_of_mixture μ R fun y hy x hx ↦ ?_
    rcases y with _ | m
    · exact absurd hf.refines.bot_0 ((PMF.mem_support_iff _ _).mp hy)
    · have hm : μ (m : WithBot Mem) ≠ 0 := (PMF.mem_support_iff _ _).mp hy
      change (↑x : WithBot Mem) ∈
        (if h : μ (m : WithBot Mem) ≠ 0 then ρ m h else PMF.pure none).support at hx
      rw [dif_pos hm] at hx
      change (if h : μ (m : WithBot Mem) ≠ 0 then f m h else fun _ ↦ PMF.pure none) x ∈
        (Linearization.Sem.sem (⟨a, Inv.emp⟩ : WithInv Act) x : ConvexPowerset Mem)
      rw [dif_pos hm, sem_withInv_emp]
      exact mem_of_bind_check (hf' m hm x hx) (hgood x (hρsupp m hm _ hx))
  obtain ⟨hk, 𝓠, 𝓙', hfQ, hdomQ, 𝓠₁, 𝓠₂, hd12, hle12, hψ, hI2⟩ :=
    hwp ρ' 𝓟fr ProbSpace.unit hF hfe _ hν'
  -- The interference does not deallocate variables
  have hμρ : Distr.Keeps μ ρ' := fun D hD m' hm' ↦ by
    obtain ⟨m, τ, hm, -, hy⟩ := hR _ ((PMF.mem_support_iff _ _).mpr hm')
    cases WithBot.coe_injective hy
    rw [Mem.dom_union]; exact (hD m hm).trans Set.subset_union_right
  -- The invariant goes back to the invariant's space
  have h1 : 𝓠₁.dom ⊆ 𝓠.dom := ProbSpace.dom_mono ((ProbSpace.le_product_left _ _).trans hle12)
  have h2 : 𝓠₂.dom ⊆ 𝓠.dom :=
    ProbSpace.dom_mono ((ProbSpace.le_product_right hd12).trans hle12)
  have hQf : Disjoint 𝓠.dom 𝓟fr.dom := hfQ.disj_frame
  have hQfJ : Disjoint (𝓠.dom ∪ 𝓟fr.dom) 𝓙'.dom := hfQ.disj_inv
  have hI2dom : 𝓘.dom ⊆ 𝓠₂.dom := (OProp.sure_forget 𝓘.footprint hI2).1
  refine ⟨Distr.Keeps.trans hμρ hk, 𝓠₁, 𝓠₂ ⊗ 𝓙',
    ⟨(OProp.sure _).mono (ProbSpace.le_product_left _ _) hI2, hQf.mono_left h1, ?_, ?_⟩, ?_, hψ⟩
  · change Disjoint (𝓠₁.dom ∪ 𝓟fr.dom) (𝓠₂.dom ∪ 𝓙'.dom)
    exact Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_right.mpr ⟨hd12, hQfJ.mono_left (h1.trans Set.subset_union_left)⟩,
        Set.disjoint_union_right.mpr ⟨(hQf.mono_left h2).symm,
          hQfJ.mono_left Set.subset_union_right⟩⟩
  · refine Distr.Refines.mono ((ProbSpace.product_assoc' _ _ _).trans
      ((ProbSpace.product_mono_left (ProbSpace.product_swap_right (hQf.mono_left h2)
        (Set.disjoint_union_right.mpr ⟨hd12, hQf.mono_left h1⟩))
        (hQfJ.mono_left (Set.union_subset_union_left _ (Set.union_subset h1 h2)))).trans
      (ProbSpace.product_mono_left (ProbSpace.product_mono_left hle12 hQf) hQfJ))) hfQ.refines
  · intro y hy
    rcases hdomQ (h1 hy) with h | h
    · exact h
    · rw [hT] at h
      exact absurd (hI2dom h) (Set.disjoint_left.mp hd12 hy)

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
    (he : ∀ (σ : Mem) (w : Val), e (σ.extend x w) = e σ) (hmono : e.Mono) :
    ⌈e == Expr.literal v ∧ own ($ x)⌉ ∗
      ((iprop(⌈$ x == Expr.literal v⌉ ∗ ⌈e == Expr.literal v⌉)) -∗ ψ) ⊢
    wp_base 𝓘 F (x ::= e) ψ := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hd, hle, hpre, hwand⟩ μ 𝓟fr 𝓙 _ hf ν hν
  obtain ⟨hx, hk, T, hfT⟩ := assign_run hmono hpre (hf.mono hle) hν
  set 𝓡 := 𝓟₁.assign x v hx
  have hx𝓡 : {x} ⊆ 𝓡.dom := Set.singleton_subset_iff.mpr hx
  have hD𝓡 : 𝓡.dom \ {x} ⊆ 𝓡.dom := Set.sdiff_subset
  -- After the assignment, `x` and `e` are both known, on disjoint variables
  have h𝓡 : iprop(⌈$ x == Expr.literal v⌉ ∗ ⌈e == Expr.literal v⌉) 𝓡 := by
    refine ⟨ProbSpace.forget 𝓡 {x} hx𝓡, ProbSpace.forget 𝓡 (𝓡.dom \ {x}) hD𝓡,
      Set.disjoint_sdiff_right, ProbSpace.product_forget_le (ProbSpace.forget_le _ _) _,
      fun k _ ↦ ?_, fun k _ ↦ ?_⟩
    · obtain ⟨k', -, heq⟩ := ProbSpace.forget_state_restrict 𝓡 hx𝓡 k
      change ($ x == Expr.literal v) ((ProbSpace.forget 𝓡 {x} hx𝓡).state k)
      rw [heq, Expr.var_equals_literal_iff, Mem.restrict_apply_of_mem _ (Set.mem_singleton x)]
      exact Mem.extend_apply_self _ _ _
    · obtain ⟨k', hk', heq⟩ := ProbSpace.forget_state_restrict 𝓡 hD𝓡 k
      change (e == Expr.literal v) ((ProbSpace.forget 𝓡 (𝓡.dom \ {x}) hD𝓡).state k)
      obtain ⟨σ', hσ', -, hσ'e⟩ := (hpre hk').1
      have hs : 𝓡.state k' = (𝓟₁.state k').extend x v := rfl
      have hval : e (𝓡.state k') = some v := by rw [hs, he]; exact hmono hσ' hσ'e
      have hrestr : e ((𝓡.state k').restrict (𝓡.dom \ {x})) = some v := by
        rw [← he _ v, ← 𝓡.dom_valid k',
          Mem.extend_restrict_sdiff (by rw [hs]; exact Mem.extend_apply_self _ _ _)]
        exact hval
      rw [heq]
      exact MProp.upClose_of ⟨by rw [hrestr]; rfl, hrestr⟩
  exact ⟨hk, 𝓡 ⊗ 𝓟₂, T, hfT, (show 𝓟₁.dom ∪ 𝓟₂.dom ⊆ 𝓟.dom from ProbSpace.dom_mono hle),
    ψ.mono (ProbSpace.product_comm hd) (hwand 𝓡 hd.symm h𝓡)⟩

/-- **The sampling rule that preserves the value of the parameter.**  This is to `wp_bern`
what `wp_assign_pres` is to `wp_assign`: if writing to `x` cannot change the value of `e`,
then the value of `e` is still known after the sampling, and it is independent of the sampled
value. -/
lemma wp_bern_pres {𝓘 : Inv} {F : ProbSpace → Prop} {ψ : OProp} (x : Var) (e : Expr) (v : Val)
    (he : ∀ (σ : Mem) (w : Val), e (σ.extend x w) = e σ) (hmono : e.Mono) :
    ⌈e == Expr.literal v ∧ own (Expr.var x)⌉ ∗
        (((Expr.var x ~ Bern v) ∗ ⌈e == Expr.literal v⌉) -∗ ψ) ⊢
      wp_base 𝓘 F (x :≈ PExpr.Bern e) ψ := by
  rintro 𝓟 ⟨𝓟₁, 𝓟₂, hd, hle, hpre, hwand⟩ μ 𝓟fr 𝓙 _ hf ν hν
  obtain ⟨hx, hk, T, hfT⟩ := bern_run hmono hd hpre (hf.mono hle) hν
  set 𝓟₁' := 𝓟₁.restrictDom (𝓟₁.dom \ {x}) Set.sdiff_subset
  set 𝓡 := 𝓟₁' ⊗ sampleSpace x (Bern v)
  have h1'B : Disjoint 𝓟₁'.dom (sampleSpace x (Bern v)).dom := Set.disjoint_sdiff_left
  have hsub : 𝓡.dom ⊆ 𝓟₁.dom :=
    Set.union_subset Set.sdiff_subset (Set.singleton_subset_iff.mpr hx)
  -- The value of `e` is still known, without `x`
  have he' : OProp.sure iprop(e == Expr.literal v) 𝓟₁' := by
    intro k hk
    obtain ⟨σ', hσ', -, hσ'e⟩ := (hpre hk).1
    have hval : e (𝓟₁.state k) = some v := hmono hσ' hσ'e
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (MProp.own_var_iff.mp (hpre hk).2)
    have hrestr : e ((𝓟₁.state k).restrict (𝓟₁.dom \ {x})) = some v := by
      rw [← he _ w, ← 𝓟₁.dom_valid k, Mem.extend_restrict_sdiff hw]
      exact hval
    change (e == Expr.literal v) ((𝓟₁.state k).restrict (𝓟₁.dom \ {x}))
    exact MProp.upClose_of ⟨by rw [hrestr]; rfl, hrestr⟩
  have h𝓡 : iprop((Expr.var x ~ Bern v) ∗ ⌈e == Expr.literal v⌉) 𝓡 :=
    ⟨sampleSpace x (Bern v), 𝓟₁', h1'B.symm, ProbSpace.product_comm h1'B,
      sampleSpace_distributed x _, he'⟩
  exact ⟨hk, 𝓡 ⊗ 𝓟₂, T, hfT,
    (Set.union_subset_union_left _ hsub).trans
      (show 𝓟₁.dom ∪ 𝓟₂.dom ⊆ 𝓟.dom from ProbSpace.dom_mono hle),
    ψ.mono (ProbSpace.product_comm (hd.mono_left hsub)) (hwand 𝓡 (hd.mono_left hsub).symm h𝓡)⟩

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
