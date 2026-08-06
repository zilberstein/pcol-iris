/-
Locality (frame) conditions for the actions and tests of a thread, and the consequences of
those conditions for the semantics of an action annotated with an invariant.
-/
import PcolIris.Logic.ParStructure
import PcolIris.Semantics.Invariant

namespace Pcol

open ConvexPowerset Linearization

/-! ### Assumptions inside the convex powerset -/

open Classical in
/-- `assume P m` is `pure m` if `P m` holds, and the everywhere-undefined element otherwise.
It is used to record the fact that a computation only produces outcomes satisfying `P`. -/
noncomputable def assume (P : Mem → Prop) (m : Mem) : ConvexPowerset Mem :=
  if P m then pure m else ⊥

lemma assume_pos {P : Mem → Prop} {m : Mem} (h : P m) : assume P m = pure m := by
  classical
  rw [assume, if_pos h]

lemma assume_neg {P : Mem → Prop} {m : Mem} (h : ¬ P m) : assume P m = ⊥ := by
  classical
  rw [assume, if_neg h]

lemma minProb_bot {α : Type} (E : Set α) : minProb (⊥ : ConvexPowerset α) E = 0 := by
  refine le_antisymm ?_ bot_le
  refine le_of_le_of_eq (minProb_le_mem (μ := PMF.pure (⊥ : WithBot α)) (Set.mem_univ _)) ?_
  refine Eq.trans (tsum_congr fun y ↦ ?_) tsum_zero
  exact PMF.pure_apply_of_ne _ _ (by simp)

lemma bot_bind {α β : Type} (f : α → ConvexPowerset β) : (⊥ : ConvexPowerset α) >>= f = ⊥ :=
  ContinuousMonad.bind_strict

/-! ### Invariant checks -/

namespace Inv

variable {𝓘 : Inv}

lemma check_eq_assume (σ : Mem) :
    𝓘.check σ = assume (fun m ↦ 𝓘.prop (m.restrict 𝓘.dom)) σ := rfl

lemma prop_dom {τ : Mem} (h : 𝓘.prop τ) : τ.dom = 𝓘.dom := 𝓘.dom_valid h

end Inv

open Classical in
/-- The memory `σ` with its invariant part replaced by `τ`. -/
noncomputable def Inv.hav (𝓘 : Inv) (τ σ : Mem) : Mem :=
  fun x ↦ if x ∈ 𝓘.dom then τ x else σ x

lemma Inv.hav_apply_of_mem {𝓘 : Inv} {τ σ : Mem} {x : Var} (h : x ∈ 𝓘.dom) :
    𝓘.hav τ σ x = τ x := by
  classical
  rw [Inv.hav, if_pos h]

lemma Inv.hav_apply_of_notMem {𝓘 : Inv} {τ σ : Mem} {x : Var} (h : x ∉ 𝓘.dom) :
    𝓘.hav τ σ x = σ x := by
  classical
  rw [Inv.hav, if_neg h]

lemma Inv.replace_bind (𝓘 : Inv) (σ : Mem) (g : Mem → ConvexPowerset Mem) :
    𝓘.replace σ >>= g = Nondet.nondet fun τ : 𝓘.prop_finite.toFinset ↦ g (𝓘.hav τ.val σ) := by
  rw [Inv.replace, Linearizable.bind_additive]
  congr 1
  funext τ
  rw [pure_bind]
  rfl

open Classical in
/-- The semantics of an invariant-annotated action: check the invariant, havoc the invariant
part of the memory, run the action, and check the invariant again. -/
lemma sem_withInv_eq_ite (a : Act) (𝓘 : Inv) (σ : Mem) :
    (Sem.sem (⟨a, 𝓘⟩ : WithInv Act) σ : ConvexPowerset Mem) =
      if 𝓘.prop (σ.restrict 𝓘.dom) then
        Nondet.nondet (fun τ : 𝓘.prop_finite.toFinset ↦
          (Sem.sem a (𝓘.hav τ.val σ) : ConvexPowerset Mem) >>= fun σ₃ ↦ 𝓘.check σ₃)
      else ⊥ := by
  simp only [Sem.sem]
  by_cases h : 𝓘.prop (σ.restrict 𝓘.dom)
  · rw [if_pos h, Inv.check, if_pos h, pure_bind, Inv.replace_bind]
  · rw [if_neg h, Inv.check, if_neg h, bot_bind]

/-! ### Locality of actions and tests -/

/-- An action is local to the footprint `W`: it reads and writes only variables in `W`. -/
def ActLocal (a : Act) (W : Set Var) : Prop :=
  ∀ m : Mem, (Sem.sem a m : ConvexPowerset Mem) =
    (Sem.sem a (m.restrict W) : ConvexPowerset Mem) >>= fun m' ↦ pure (Mem.union m' m)

/-- An action run on a memory with domain `W` only produces memories with domain `W`. -/
def ActDomStable (a : Act) (W : Set Var) : Prop :=
  ∀ m : Mem, m.dom = W →
    (Sem.sem a m : ConvexPowerset Mem) =
      (Sem.sem a m : ConvexPowerset Mem) >>= assume (fun m' ↦ m'.dom = W)

/-- A test reads only the variables in `X`. -/
def TestLocal (b : Test) (X : Set Var) : Prop :=
  ∀ m : Mem, (Sem.sem b m : ConvexPowerset Bool) = Sem.sem b (m.restrict X)

/-- All the actions of the thread `α` are local to `X ∪ 𝓘.dom` and preserve that domain, and
all its tests read only `X`.  This is the (necessary) hypothesis that the thread stays inside
its own footprint, the invariant being the only shared state. -/
def ThreadLocal (α : Lpo (Label (WithInv Act) Test)) (X : Set Var) (𝓘 : Inv) : Prop :=
  ∀ x ∈ α.nodes,
    match α.lab x with
    | Label.act a => ActLocal a.action (X ∪ 𝓘.dom) ∧ ActDomStable a.action (X ∪ 𝓘.dom)
    | Label.test b => TestLocal b X
    | _ => True


/-! ### Consequences of locality for invariant-annotated actions -/

lemma bind_congr_of_domStable {s : ConvexPowerset Mem} {W : Set Var}
    (hs : s = s >>= assume (fun m' ↦ Mem.dom m' = W)) (f g : Mem → ConvexPowerset Mem)
    (h : ∀ m₃ : Mem, Mem.dom m₃ = W → f m₃ = g m₃) : s >>= f = s >>= g := by
  conv_lhs => rw [hs]
  conv_rhs => rw [hs]
  rw [bind_assoc, bind_assoc]
  congr 1
  funext m₃
  by_cases hd : Mem.dom m₃ = W
  · rw [assume_pos hd, pure_bind, pure_bind, h m₃ hd]
  · rw [assume_neg hd, bot_bind, bot_bind]

/-- The invariant-annotated action `⟨a, 𝓘⟩` has the frame property of `a`. -/
theorem sem_withInv_frame {a : Act} {𝓘 : Inv} {W : Set Var} (hD : 𝓘.dom ⊆ W)
    (h₁ : ActLocal a W) (h₂ : ActDomStable a W) {m : Mem} (hm : W ⊆ m.dom) :
    (Sem.sem (⟨a, 𝓘⟩ : WithInv Act) m : ConvexPowerset Mem) =
      (Sem.sem (⟨a, 𝓘⟩ : WithInv Act) (m.restrict W) : ConvexPowerset Mem) >>=
        fun m' ↦ pure (Mem.union m' m) := by
  classical
  have hres : Mem.restrict (show Mem from m.restrict W) 𝓘.dom = m.restrict 𝓘.dom := by
    rw [Mem.restrict_restrict, Set.inter_eq_self_of_subset_right hD]
  rw [sem_withInv_eq_ite, sem_withInv_eq_ite, hres]
  by_cases h : 𝓘.prop (m.restrict 𝓘.dom)
  · rw [if_pos h, if_pos h, Linearizable.bind_additive]
    congr 1
    funext τ
    have hτ : 𝓘.prop τ.val := (Set.Finite.mem_toFinset _).mp τ.property
    have hτdom : Mem.dom τ.val = 𝓘.dom := 𝓘.dom_valid hτ
    set n : Mem := 𝓘.hav τ.val m with hn_def
    have hdomn : Mem.dom n = m.dom := by
      ext x
      by_cases hx : x ∈ 𝓘.dom
      · simp only [Mem.mem_dom_iff, hn_def, Inv.hav_apply_of_mem hx]
        constructor
        · intro _; exact Mem.mem_dom_iff.mp (hm (hD hx))
        · intro _; exact Mem.mem_dom_iff.mp (hτdom ▸ hx)
      · simp only [Mem.mem_dom_iff, hn_def, Inv.hav_apply_of_notMem hx]
    have hdomnW : Mem.dom (show Mem from n.restrict W) = W := by
      rw [Mem.restrict_dom, hdomn]
      exact Set.inter_eq_self_of_subset_right hm
    have hn : 𝓘.hav τ.val (show Mem from m.restrict W) = (show Mem from n.restrict W) := by
      funext x
      by_cases hx : x ∈ W
      · rw [Mem.restrict_apply_of_mem _ hx]
        by_cases hxD : x ∈ 𝓘.dom
        · rw [Inv.hav_apply_of_mem hxD, hn_def, Inv.hav_apply_of_mem hxD]
        · rw [Inv.hav_apply_of_notMem hxD, hn_def, Inv.hav_apply_of_notMem hxD,
            Mem.restrict_apply_of_mem _ hx]
      · rw [Mem.restrict_apply_of_notMem _ hx]
        have hxD : x ∉ 𝓘.dom := fun hc ↦ hx (hD hc)
        rw [Inv.hav_apply_of_notMem hxD, Mem.restrict_apply_of_notMem _ hx]
    rw [hn]
    conv_lhs => rw [h₁ n]
    rw [bind_assoc, bind_assoc]
    refine bind_congr_of_domStable (h₂ _ hdomnW) _ _ ?_
    intro m₃ hm₃
    rw [pure_bind]
    have hrestr : Mem.restrict (m₃.union n) 𝓘.dom = m₃.restrict 𝓘.dom :=
      Mem.restrict_union_of_subset_dom (by rw [hm₃]; exact hD) n
    have hunion : m₃.union n = m₃.union m := by
      refine Mem.union_congr_right ?_
      intro x hx
      rw [hm₃] at hx
      exact Inv.hav_apply_of_notMem (fun hc ↦ hx (hD hc))
    rw [Inv.check, Inv.check, hrestr]
    by_cases hp : 𝓘.prop (m₃.restrict 𝓘.dom)
    · rw [if_pos hp, if_pos hp, pure_bind, hunion]
    · rw [if_neg hp, if_neg hp, bot_bind]
  · rw [if_neg h, if_neg h, bot_bind]

/-- An invariant-annotated action run on a memory of domain `W` produces only memories of
domain `W` whose invariant part satisfies the invariant. -/
theorem sem_withInv_assume {a : Act} {𝓘 : Inv} {W : Set Var} (hD : 𝓘.dom ⊆ W)
    (h₂ : ActDomStable a W) {p : Mem} (hp : Mem.dom p = W) :
    (Sem.sem (⟨a, 𝓘⟩ : WithInv Act) p : ConvexPowerset Mem) =
      (Sem.sem (⟨a, 𝓘⟩ : WithInv Act) p : ConvexPowerset Mem) >>=
        assume (fun m' ↦ Mem.dom m' = W ∧ 𝓘.prop (m'.restrict 𝓘.dom)) := by
  classical
  rw [sem_withInv_eq_ite]
  by_cases h : 𝓘.prop (p.restrict 𝓘.dom)
  · rw [if_pos h, Linearizable.bind_additive]
    congr 1
    funext τ
    have hτ : 𝓘.prop τ.val := (Set.Finite.mem_toFinset _).mp τ.property
    have hτdom : Mem.dom τ.val = 𝓘.dom := 𝓘.dom_valid hτ
    have hdomn : Mem.dom (𝓘.hav τ.val p) = W := by
      rw [← hp]
      ext x
      by_cases hx : x ∈ 𝓘.dom
      · simp only [Mem.mem_dom_iff, Inv.hav_apply_of_mem hx]
        constructor
        · intro _; exact Mem.mem_dom_iff.mp (hp ▸ hD hx)
        · intro _; exact Mem.mem_dom_iff.mp (hτdom ▸ hx)
      · simp only [Mem.mem_dom_iff, Inv.hav_apply_of_notMem hx]
    rw [bind_assoc]
    refine bind_congr_of_domStable (h₂ _ hdomn) _ _ ?_
    intro m₃ hm₃
    rw [Inv.check]
    by_cases hq : 𝓘.prop (m₃.restrict 𝓘.dom)
    · rw [if_pos hq, pure_bind, assume_pos ⟨hm₃, hq⟩]
    · rw [if_neg hq, bot_bind]
  · rw [if_neg h, bot_bind]

/-- An invariant-annotated action does not see the invariant part of the memory: two memories
with the same footprint part and both satisfying the invariant give the same semantics. -/
theorem sem_withInv_indep {a : Act} {𝓘 : Inv} {X : Set Var} {p p' : Mem}
    (hp : Mem.dom p = X ∪ 𝓘.dom) (hp' : Mem.dom p' = X ∪ 𝓘.dom)
    (hX : p.restrict X = p'.restrict X)
    (hi : 𝓘.prop (p.restrict 𝓘.dom)) (hi' : 𝓘.prop (p'.restrict 𝓘.dom)) :
    (Sem.sem (⟨a, 𝓘⟩ : WithInv Act) p : ConvexPowerset Mem) =
      (Sem.sem (⟨a, 𝓘⟩ : WithInv Act) p' : ConvexPowerset Mem) := by
  classical
  rw [sem_withInv_eq_ite, sem_withInv_eq_ite, if_pos hi, if_pos hi']
  congr 1
  funext τ
  have hhav : 𝓘.hav τ.val p = 𝓘.hav τ.val p' := by
    funext x
    by_cases hxD : x ∈ 𝓘.dom
    · rw [Inv.hav_apply_of_mem hxD, Inv.hav_apply_of_mem hxD]
    · rw [Inv.hav_apply_of_notMem hxD, Inv.hav_apply_of_notMem hxD]
      by_cases hxX : x ∈ X
      · have := congrFun hX x
        rwa [Mem.restrict_apply_of_mem _ hxX, Mem.restrict_apply_of_mem _ hxX] at this
      · have h1 : x ∉ Mem.dom p := by rw [hp]; exact fun hc ↦ hc.elim hxX hxD
        have h2 : x ∉ Mem.dom p' := by rw [hp']; exact fun hc ↦ hc.elim hxX hxD
        rw [Mem.notMem_dom_iff.mp h1, Mem.notMem_dom_iff.mp h2]
  rw [hhav]

/-! ### The locality hypotheses are satisfiable

An assignment whose target variable and whose expression stay inside the footprint `W` is
local to `W` and preserves the domain `W`; a test whose expression only reads `X` reads only
`X`.  These lemmas show that `ActLocal`, `ActDomStable` and `TestLocal` are not vacuous. -/

lemma Mem.dom_extend (m : Mem) (x : Var) (v : Val) :
    Mem.dom (m.extend x v) = insert x m.dom := by
  ext y
  by_cases h : x = y
  · subst h
    simp only [Set.mem_insert_iff, true_or, iff_true]
    change (if x = x then (v : Option Val) else m x) ≠ none
    rw [if_pos rfl]
    exact Option.some_ne_none v
  · have : Mem.extend m x v y = m y := if_neg h
    change Mem.extend m x v y ≠ none ↔ _
    rw [this]
    simp only [Set.mem_insert_iff]
    exact ⟨fun hc ↦ Or.inr hc, fun hc ↦ hc.elim (fun hy ↦ absurd hy.symm h) id⟩

theorem ActLocal.assign {x : Var} {e : Expr} {W : Set Var}
    (he : ∀ m : Mem, e m = e (show Mem from m.restrict W)) :
    ActLocal (Act.assign x e) W := by
  intro m
  have h1 : (Sem.sem (Act.assign x e) m : ConvexPowerset Mem)
      = match e m with
        | some v => pure (m.extend x v)
        | none => ⊥ := rfl
  have h2 : (Sem.sem (Act.assign x e) (show Mem from m.restrict W) : ConvexPowerset Mem)
      = match e m with
        | some v => pure ((show Mem from m.restrict W).extend x v)
        | none => ⊥ := by
    rw [he m]; rfl
  rw [h1, h2]
  cases hv : e m with
  | none => exact (bot_bind _).symm
  | some v =>
    dsimp only
    rw [pure_bind]
    congr 1
    funext y
    by_cases hxy : x = y
    · subst hxy
      change (if x = x then (v : Option Val) else m x)
        = Mem.union (Mem.extend (Mem.restrict m W) x v) m x
      rw [if_pos rfl]
      change _ = match Mem.extend (Mem.restrict m W) x v x with
        | some w => (w : Option Val)
        | none => m x
      rw [show Mem.extend (Mem.restrict m W) x v x = some v from if_pos rfl]
    · change (if x = y then (v : Option Val) else m y)
        = Mem.union (Mem.extend (Mem.restrict m W) x v) m y
      rw [if_neg hxy]
      change _ = match Mem.extend (Mem.restrict m W) x v y with
        | some w => (w : Option Val)
        | none => m y
      rw [show Mem.extend (Mem.restrict m W) x v y = Mem.restrict m W y from if_neg hxy]
      by_cases hy : y ∈ W
      · rw [Mem.restrict_apply_of_mem m hy]
        cases hmy : m y with
        | none => rfl
        | some w => rfl
      · rw [Mem.restrict_apply_of_notMem m hy]

theorem ActDomStable.assign {x : Var} {e : Expr} {W : Set Var} (hx : x ∈ W) :
    ActDomStable (Act.assign x e) W := by
  intro m hm
  have h1 : (Sem.sem (Act.assign x e) m : ConvexPowerset Mem)
      = match e m with
        | some v => pure (m.extend x v)
        | none => ⊥ := rfl
  rw [h1]
  cases hv : e m with
  | none => exact (bot_bind _).symm
  | some v =>
    dsimp only
    rw [pure_bind, assume_pos]
    rw [Mem.dom_extend, hm, Set.insert_eq_self.mpr hx]

theorem TestLocal.lift {e : Expr} {X : Set Var}
    (he : ∀ m : Mem, e m = e (show Mem from m.restrict X)) :
    TestLocal (Test.lift e) X := by
  intro m
  have h1 : (Sem.sem (Test.lift e) m : ConvexPowerset Bool)
      = match e m with
        | some q => pure (decide (q ≠ 0))
        | none => ⊥ := rfl
  have h2 : (Sem.sem (Test.lift e) (show Mem from m.restrict X) : ConvexPowerset Bool)
      = match e m with
        | some q => pure (decide (q ≠ 0))
        | none => ⊥ := by
    rw [he m]; rfl
  rw [h1, h2]

end Pcol
