/-
The semantics of atomic actions run under an invariant.

`ConvexPowerset.SupportedIn S G` says that every distribution of `S` only produces
(terminating) outcomes in `G`.  It is preserved by the monad operations, which makes it
possible to describe the possible outcomes of an action: the invariant is checked, its
variables are replaced by arbitrary values satisfying it (interference by other threads),
the action runs, and the invariant is checked again.
-/
import PcolIris.Semantics.Invariant
import PcolIris.Logic.Framed

namespace ConvexPowerset

variable {α β : Type} {S : ConvexPowerset α} {G G' : Set α}

/-- Every distribution of `S` only produces (terminating) outcomes in `G`. -/
def SupportedIn (S : ConvexPowerset α) (G : Set α) : Prop :=
  ∀ ν ∈ S, ∀ y ∈ PMF.support ν, ∃ x ∈ G, y = (x : WithBot α)

lemma SupportedIn.mono (h : S.SupportedIn G) (hG : G ⊆ G') : S.SupportedIn G' :=
  fun ν hν y hy ↦ let ⟨x, hx, hxy⟩ := h ν hν y hy; ⟨x, hG hx, hxy⟩

lemma supportedIn_pure (x : α) : (pure x : ConvexPowerset α).SupportedIn {x} := by
  intro ν hν y hy
  rw [mem_pure] at hν
  subst hν
  exact ⟨x, rfl, (PMF.mem_support_pure_iff _ _).mp hy⟩

lemma SupportedIn.bind {k : α → ConvexPowerset β} {H : Set β} (hS : S.SupportedIn G)
    (hk : ∀ x ∈ G, (k x).SupportedIn H) : (S >>= k).SupportedIn H := by
  intro ν hν y hy
  obtain ⟨μ, hμ, f, hf, rfl⟩ := mem_bind.mp hν
  obtain ⟨z, hz, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
  obtain ⟨x, hx, rfl⟩ := hS μ hμ z hz
  exact hk x hx (f x) (hf x hz) y hy

lemma SupportedIn.nondet {ι : Type} [Finite ι] [Nonempty ι] {s : ι → ConvexPowerset α}
    (h : ∀ i, (s i).SupportedIn G) : (ConvexPowerset.nondet s).SupportedIn G := by
  intro ν hν y hy
  obtain ⟨ξ, k, hk, rfl⟩ := mem_nondet.mp hν
  obtain ⟨i, hi, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
  exact h i (k i) (hk i hi) y hy

/-- Every distribution of `S` is `d`. -/
def Det (S : ConvexPowerset α) (d : Distr α) : Prop := ∀ ν ∈ S, ν = d

lemma det_pure (x : α) : (pure x : ConvexPowerset α).Det (PMF.pure (some x)) :=
  fun _ hν ↦ (mem_pure x).mp hν

lemma det_singleton (μ : PMF α) : (ConvexPowerset.singleton μ).Det (PMF.to_distr μ) :=
  fun _ hν ↦ hν

/-- Extending a kernel on proper outcomes to `WithBot`. -/
noncomputable def botElim {β : Type} (D : α → Distr β) (y : WithBot α) : Distr β :=
  Option.elim y (PMF.pure none) D

lemma bind_eq_of_supportedIn {k : α → ConvexPowerset β} {D : α → Distr β} (hS : S.SupportedIn G)
    (hk : ∀ x ∈ G, (k x).Det (D x)) :
    ∀ ν ∈ S >>= k, ∃ ρ ∈ S, ν = ρ.bind (botElim D) := by
  intro ν hν
  obtain ⟨ρ, hρ, f, hf, rfl⟩ := mem_bind.mp hν
  refine ⟨ρ, hρ, Pcol.Distr.bind_congr_support' ρ fun y hy ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := hS ρ hρ y hy
  exact hk x hx _ (hf _ hy)

lemma Det.bind {k : α → ConvexPowerset β} {d : Distr α} {D : α → Distr β} (hS : S.Det d)
    (hd : d ⊥ = 0) (hk : ∀ x : α, (↑x : WithBot α) ∈ PMF.support d → (k x).Det (D x)) :
    (S >>= k).Det (d.bind (botElim D)) := by
  intro ν hν
  obtain ⟨ρ, hρ, f, hf, rfl⟩ := mem_bind.mp hν
  obtain rfl := hS ρ hρ
  refine Pcol.Distr.bind_congr_support' ρ fun y hy ↦ ?_
  rcases y with _ | x
  · exact absurd hd ((PMF.mem_support_iff _ _).mp hy)
  · exact hk x hy _ (hf _ hy)

end ConvexPowerset

namespace Pcol

open Linearization ConvexPowerset

namespace Inv

variable {𝓘 : Inv} {σ : Mem}

lemma check_of (h : 𝓘.prop (σ.restrict 𝓘.dom)) : 𝓘.check σ = pure σ := by
  classical
  exact if_pos h

/-- Replacing the invariant's part of a memory satisfying the invariant yields the memories
`τ ⊎ σ`, for `τ` satisfying the invariant. -/
lemma replace_supportedIn (h : 𝓘.prop (σ.restrict 𝓘.dom)) :
    (𝓘.replace σ).SupportedIn {σ' | ∃ τ, 𝓘.prop τ ∧ σ' = (τ ⊎ σ)} := by
  classical
  have hI : Nonempty 𝓘.prop_finite.toFinset := ⟨⟨_, 𝓘.prop_finite.mem_toFinset.mpr h⟩⟩
  change (if _ : Nonempty _ then ConvexPowerset.nondet _ else ⊥ : ConvexPowerset Mem).SupportedIn _
  rw [dif_pos hI]
  refine SupportedIn.nondet fun τ ↦ (supportedIn_pure _).mono ?_
  exact Set.singleton_subset_iff.mpr ⟨τ.val, 𝓘.prop_finite.mem_toFinset.mp τ.2, rfl⟩

end Inv

/-- The possible outcomes of an action run under an invariant, from a memory satisfying the
invariant: if the action, run after any interference, only produces memories in `G` that
satisfy the invariant, then so does the action run under the invariant. -/
lemma sem_withInv_supportedIn {a : Act} {𝓘 : Inv} {σ : Mem} (h : 𝓘.prop (σ.restrict 𝓘.dom))
    {G : Set Mem}
    (ha : ∀ τ, 𝓘.prop τ → (Sem.sem a (τ ⊎ σ) : ConvexPowerset Mem).SupportedIn
      {m | m ∈ G ∧ 𝓘.prop (m.restrict 𝓘.dom)}) :
    (Sem.sem (⟨a, 𝓘⟩ : WithInv Act) σ : ConvexPowerset Mem).SupportedIn G := by
  change (𝓘.check σ >>= fun σ ↦ 𝓘.replace σ >>= fun σ ↦ Sem.sem a σ >>= fun τ ↦ 𝓘.check τ
    : ConvexPowerset Mem).SupportedIn G
  rw [Inv.check_of h, ConvexPowerset.pure_bind]
  refine (Inv.replace_supportedIn h).bind fun σ' ⟨τ, hτ, hσ'⟩ ↦ ?_
  subst hσ'
  refine (ha τ hτ).bind fun m ⟨hm, hI⟩ ↦ ?_
  rw [Inv.check_of hI]
  exact (supportedIn_pure m).mono (Set.singleton_subset_iff.mpr hm)

/-- An assignment whose expression evaluates to `v` produces the updated memory. -/
lemma sem_assign_supportedIn {x : Var} {e : Expr} {σ : Mem} {v : Val} (he : e σ = some v) :
    (Sem.sem (Act.assign x e) σ : ConvexPowerset Mem).SupportedIn {σ.extend x v} := by
  change (match e σ with
    | some v => pure (σ.extend x v)
    | none => ⊥ : ConvexPowerset Mem).SupportedIn _
  rw [he]
  exact supportedIn_pure _

/-- The space `p`, with the variable `x` set to `v` in all its memories. -/
def ProbSpace.assign (p : ProbSpace) (x : Var) (v : Val) (hx : x ∈ p.dom) : ProbSpace where
  mspace := p.mspace
  μ := p.μ
  dom := p.dom
  state k := (p.state k).extend x v
  dom_valid k := by rw [Mem.dom_extend, p.dom_valid, Set.insert_eq_of_mem hx]
  complete := p.complete

/-! ### Sampling -/

lemma to_distr_eq_map {α : Type} (μ : PMF α) :
    (PMF.to_distr μ : PMF (WithBot α)) = μ.map WithBot.some := by
  refine PMF.ext fun y ↦ ?_
  change (PMF.to_distr μ).val y = (μ.map WithBot.some) y
  rw [PMF.map_apply]
  induction y using WithBot.recBotCoe with
  | bot =>
    show (0 : ENNReal) = _
    exact (ENNReal.tsum_eq_zero.mpr fun a ↦ if_neg WithBot.bot_ne_coe).symm
  | coe x =>
    show μ x = _
    rw [tsum_eq_single x (fun b hb ↦ if_neg fun h ↦ hb (WithBot.coe_injective h).symm),
      if_pos rfl]

/-- The outcome of sampling `x` from `ξ` in the memory `σ`. -/
noncomputable def sampleDistr (x : Var) (ξ : PMF Val) (σ : Mem) : Distr Mem :=
  ξ.map fun b ↦ some (σ.extend x b)

lemma sampleDistr_bot (x : Var) (ξ : PMF Val) (σ : Mem) : sampleDistr x ξ σ ⊥ = 0 := by
  change (ξ.map fun b ↦ (some (σ.extend x b) : WithBot Mem)) none = 0
  simp [PMF.map_apply]

lemma sem_samp_det {x : Var} {e : Expr} {σ : Mem} {v : Val} (he : e σ = some v) :
    (Sem.sem (Act.samp x (PExpr.Bern e)) σ : ConvexPowerset Mem).Det
      (sampleDistr x (Bern v) σ) := by
  have hB : PExpr.Bern e σ = some (Bern v) := by simp [PExpr.Bern, he]
  change (match PExpr.Bern e σ with
    | some μ => ConvexPowerset.singleton μ >>= fun v ↦ pure (σ.extend x v)
    | none => ⊥ : ConvexPowerset Mem).Det _
  rw [hB]
  change (ConvexPowerset.singleton (Bern v) >>= fun b ↦ pure (σ.extend x b)
    : ConvexPowerset Mem).Det _
  have h := (det_singleton (Bern v)).bind rfl (fun b _ ↦ det_pure (σ.extend x b))
  convert h using 1
  rw [to_distr_eq_map, PMF.bind_map]
  rfl

/-- The outcomes of a sampling `x :≈ Bern e` run under an invariant, from a memory `σ`
satisfying the invariant, in which `e` has the value `v` whatever the interference: some
interference `ρ` on the invariant's variables, followed by the sampling. -/
lemma sem_samp_withInv {x : Var} {e : Expr} {𝓘 : Inv} {σ : Mem} {v : Val}
    (h : 𝓘.prop (σ.restrict 𝓘.dom)) (hx : x ∉ 𝓘.dom)
    (he : ∀ τ, 𝓘.prop τ → e (τ ⊎ σ) = some v) :
    ∀ ν ∈ (Sem.sem (⟨Act.samp x (PExpr.Bern e), 𝓘⟩ : WithInv Act) σ : ConvexPowerset Mem),
      ∃ ρ ∈ 𝓘.replace σ, ν = ρ.bind (botElim (sampleDistr x (Bern v))) := by
  change ∀ ν ∈ (𝓘.check σ >>= fun σ ↦ 𝓘.replace σ >>= fun σ ↦
    Sem.sem (Act.samp x (PExpr.Bern e)) σ >>= fun τ ↦ 𝓘.check τ : ConvexPowerset Mem), _
  rw [Inv.check_of h, ConvexPowerset.pure_bind]
  refine bind_eq_of_supportedIn (Inv.replace_supportedIn h) fun σ' ⟨τ, hτ, hσ'⟩ ↦ ?_
  subst hσ'
  have hd := (sem_samp_det (x := x) (he τ hτ)).bind (sampleDistr_bot _ _ _)
    (k := fun m ↦ 𝓘.check m)
    (D := fun m ↦ PMF.pure (some m)) fun m hm ↦ ?_
  · convert hd using 1
    conv_lhs => rw [← PMF.bind_pure (sampleDistr x (Bern v) (τ ⊎ σ))]
    refine Pcol.Distr.bind_congr_support' _ fun y hy ↦ ?_
    rcases y with _ | m
    · simp [sampleDistr] at hy
    · rfl
  · obtain ⟨b, -, hb⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    cases Option.some.inj hb
    rw [Inv.check_of]
    · exact det_pure _
    · rw [Mem.restrict_extend_of_notMem b hx, Mem.restrict_union_left (𝓘.dom_valid hτ)]
      exact hτ

/-! ### The space of a fresh sample -/

lemma dom_singleton (x : Var) (u : Val) : (Mem.singleton x u).dom = {x} := by
  rw [Mem.singleton, Mem.dom_extend, Mem.emp_dom]; exact LawfulSingleton.insert_empty_eq x

/-- The space where `x` has the value `u`. -/
noncomputable def pointSpace (x : Var) (u : Val) : ProbSpace :=
  ProbSpace.trivialOn {x} (fun _ ↦ Mem.singleton x u) (fun _ ↦ dom_singleton x u)

lemma trivialOn_refines {V : Set Var} {σ : Mem} (hσ : σ.dom = V) :
    ProbSpace.trivialOn V (fun _ ↦ σ) (fun _ ↦ hσ) ≼ PMF.pure (σ : WithBot Mem) := by
  refine ⟨PMF.pure 0, fun _ ↦ σ, id, fun {E} hE ↦ ?_, fun _ _ ↦ le_refl _, ?_⟩
  · rw [tsum_subtype, ← PMF.toOuterMeasure_apply, ProbSpace.prob_coe]
    rcases ProbSpace.trivialOn_measurableSet hE with rfl | rfl
    · rw [MeasureTheory.measure_empty, Set.preimage_empty, (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
        (Set.disjoint_empty _)]
    · rw [MeasureTheory.measure_univ, Set.preimage_univ,
        (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)]
  · rw [PMF.pure_map]; rfl

lemma pointSpace_disjoint (x : Var) {u u' : Val} (h : u ≠ u') :
    Disjoint ((pointSpace x u).shift (Encodable.encode u)).support
      ((pointSpace x u').shift (Encodable.encode u')).support :=
  ProbSpace.disjoint_support_shift _ _ fun h' ↦ h (Encodable.encode_injective h')

/-- The space of a fresh sample of `x` from `ξ`: the `ξ`-average of the spaces where `x = u`
(on disjoint outcomes). -/
noncomputable def sampleSpace (x : Var) (ξ : PMF Val) : ProbSpace :=
  ProbSpace.sum ξ (fun u ↦ (pointSpace x u).shift (Encodable.encode u)) {x}
    (pointSpace_disjoint x) (fun _ ↦ rfl)

lemma sampleSpace_dom (x : Var) (ξ : PMF Val) : (sampleSpace x ξ).dom = {x} := rfl

lemma sampleSpace_refines (x : Var) (ξ : PMF Val) :
    sampleSpace x ξ ≼ ξ.map fun u ↦ ((Mem.singleton x u : Mem) : WithBot Mem) := by
  refine Distr.Refines.sum (hd := pointSpace_disjoint x) fun u _ ↦
    Distr.Refines.mono (ProbSpace.shift_le _ _) ?_
  exact trivialOn_refines (dom_singleton x u)

lemma sampleSpace_distributed (x : Var) (ξ : PMF Val) :
    ((($ x) ~ ξ) : OProp) (sampleSpace x ξ) := by
  refine ⟨_, {x}, pointSpace_disjoint x, fun _ ↦ rfl, le_refl _, fun u _ k _ ↦ ?_⟩
  change ($ x == Expr.literal u) (Mem.singleton x u)
  rw [Expr.var_equals_literal_iff]
  exact Mem.extend_apply_self _ _ _

lemma sampleSpace_state {x : Var} {ξ : PMF Val} {k : ℕ} (hk : k ∈ (sampleSpace x ξ).support) :
    ∃ u, (sampleSpace x ξ).state k = Mem.singleton x u := by
  have hk' := hk
  rw [sampleSpace, ProbSpace.support_sum] at hk'
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hk'
  obtain ⟨u, -, hu⟩ := hk'
  refine ⟨u, ?_⟩
  change ProbSpace.sumState _ {x} k = _
  rw [ProbSpace.sumState_of_mem (𝓟 := fun u ↦ (pointSpace x u).shift (Encodable.encode u))
    (pointSpace_disjoint x) hu]
  rfl

/-- A run of an action from `μ`, as a kernel. -/
lemma run_act {a : WithInv Act} {μ ν : Distr Mem} (hμ : μ ⊥ = 0)
    (hν : ν ∈ ConvexPowerset.singleton' μ >>= Sem.sem a) :
    ∃ K : WithBot Mem → Distr Mem, ν = μ.bind K ∧
      ∀ m : Mem, μ (m : WithBot Mem) ≠ 0 → K m ∈ (Sem.sem a m : ConvexPowerset Mem) := by
  obtain ⟨μ₀, hμ₀, K, hK, rfl⟩ := ConvexPowerset.mem_bind.mp hν
  have h' : μ₀ ∈ (ConvexPowerset.singleton' μ).set := hμ₀
  rw [ConvexPowerset.singleton'_set_eq] at h'
  obtain rfl := proper_dist_maximal hμ h'
  exact ⟨K, rfl, fun m hm ↦ hK m ((PMF.mem_support_iff _ _).mpr hm)⟩

end Pcol
