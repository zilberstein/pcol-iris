import PcolIris.OProp.MProp
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

def emp : Inv where
  dom := ∅
  prop σ := σ.dom = ∅
  dom_finite := Set.finite_empty
  dom_valid := fun h ↦ h
  prop_finite := by
    refine (Set.finite_singleton (fun (_ : Var) ↦ none)).subset ?_
    intro σ hdom; ext1 x
    have := Set.eq_empty_iff_forall_notMem.mp hdom x
    simp only [Mem.dom, ne_eq, Set.mem_setOf_eq, Decidable.not_not] at this;
    exact this

def to_MProp (𝓘 : Inv) : MProp := {
  prop σ := 𝓘.prop (σ.restrict 𝓘.dom)
  upcl := by
    intro σ τ hle h
    have heq : σ.restrict 𝓘.dom = τ.restrict 𝓘.dom := by
      funext x; unfold Mem.restrict; by_cases hx : x ∈ 𝓘.dom
      · simp only [hx, ↓reduceIte]
        have := 𝓘.dom_valid h ▸ σ.restrict_dom 𝓘.dom; rw [this] at hx
        have ⟨v, hv⟩ := hx.1 |> Option.ne_none_iff_exists.mp
        rw [← hv]; symm; have := hv.symm ▸ hle x; exact this
      · simp only [hx, ↓reduceIte]
    simpa only [Membership.mem, Set.Mem, ← heq]
}

/-- The order on invariants: `𝓘 ≤ 𝓙` when `𝓘` factors as `𝓙 ∗ 𝓚` for an invariant `𝓚` on the
remaining variables.  Concretely, `𝓙` owns fewer variables, every memory satisfying `𝓘`
restricts to one satisfying `𝓙`, and replacing the `𝓙`-part of a memory satisfying `𝓘` by any
memory satisfying `𝓙` again satisfies `𝓘`.

This is the order along which invariant-sensitive execution is monotone (Lemma 5.3 of the
paper, stated there for `I ∗ J`): a larger invariant allows more interference.  A mere
projection would not do, since other threads could then change the variables of `𝓙` without
preserving the correlations that `𝓘` imposes with the other variables. -/
structure LE_Inv (𝓘 𝓙 : Inv) : Prop where
  dom : 𝓙.dom ⊆ 𝓘.dom
  proj : ∀ {σ}, 𝓘.prop σ → 𝓙.prop (σ.restrict 𝓙.dom)
  mix : ∀ {σ τ}, 𝓘.prop σ → 𝓙.prop τ → 𝓘.prop (τ ⊎ σ)

instance : LE Inv where
  le := LE_Inv

/-- Replacing the whole memory of an invariant by another one. -/
lemma union_eq_of_prop {𝓘 : Inv} {σ τ : Mem} (hτ : 𝓘.prop τ) (hσ : σ.dom = 𝓘.dom) :
    (τ ⊎ σ) = τ := by
  funext x
  by_cases hx : x ∈ τ.dom
  · exact Mem.union_apply_of_mem_dom hx
  · rw [Mem.union_apply_of_notMem_dom hx, Mem.notMem_dom_iff.mp hx]
    rw [𝓘.dom_valid hτ, ← hσ] at hx
    exact Mem.notMem_dom_iff.mp hx

/-- Restricting a memory to the domain of an invariant it satisfies does not change it. -/
lemma restrict_of_prop {𝓘 : Inv} {σ : Mem} (h : 𝓘.prop σ) : σ.restrict 𝓘.dom = σ := by
  rw [← 𝓘.dom_valid h, Mem.restrict_self]

/-- The memories of `𝓙` that are restrictions of memories of `𝓘` and the memories of `𝓘`. -/
lemma restrict_union_restrict {𝓙 : Inv} {σ τ : Mem} (hτ : 𝓙.prop τ) (hsub : 𝓙.dom ⊆ σ.dom) :
    (τ ⊎ σ).restrict 𝓙.dom = τ := by
  rw [Mem.restrict_union_left (𝓙.dom_valid hτ)]

instance : Preorder Inv where
  le_refl 𝓘 := by
    refine ⟨Set.Subset.refl _, fun h ↦ by rwa [restrict_of_prop h], fun hσ hτ ↦ ?_⟩
    rwa [union_eq_of_prop hτ (𝓘.dom_valid hσ)]
  le_trans 𝓘 𝓙 𝓚 hle₁ hle₂ := by
    refine ⟨hle₂.dom.trans hle₁.dom, fun h ↦ ?_, fun {σ τ} hσ hτ ↦ ?_⟩
    · have := hle₂.proj (hle₁.proj h)
      rwa [Mem.restrict_restrict, Set.inter_eq_self_of_subset_right hle₂.dom] at this
    · -- mix `τ` into the `𝓙`-part of `σ`, and then that into `σ`
      have hρ : 𝓙.prop (τ ⊎ σ.restrict 𝓙.dom) := hle₂.mix (hle₁.proj hσ) hτ
      have := hle₁.mix hσ hρ
      rwa [Mem.union_assoc, Mem.union_restrict_self] at this

instance : PartialOrder Inv where
  le_antisymm 𝓘 𝓙 hle hge := by
    have heq := Set.Subset.antisymm hge.dom hle.dom
    ext1
    · exact heq
    · ext σ; constructor
      · intro h; have := hle.proj h; rwa [← heq, restrict_of_prop h] at this
      · intro h; have := hge.proj h; rwa [heq, restrict_of_prop h] at this

/-- The invariant without variables is the largest one. -/
lemma le_emp (𝓘 : Inv) : 𝓘 ≤ emp := by
  refine ⟨Set.empty_subset _, fun _ ↦ ?_, fun {σ τ} hσ hτ ↦ ?_⟩
  · show Mem.dom _ = ∅
    rw [Mem.restrict_dom]; exact Set.inter_empty _
  · have hτ' : τ = Mem.emp := by
      funext x; exact Mem.notMem_dom_iff.mp (by rw [show τ.dom = ∅ from hτ]; exact id)
    rwa [hτ', Mem.emp_union]

/-- Two comparable invariants with the same domain are equal, unless the smaller one is
empty (an empty invariant is below every invariant with fewer variables). -/
lemma eq_of_le_of_dom_eq {L M : Inv} (hle : L ≤ M) (hdom : M.dom = L.dom)
    (hne : (∃ ρ, L.prop ρ) ∨ ¬ ∃ σ, M.prop σ) : M = L := by
  ext1
  · exact hdom
  · ext σ
    rcases hne with ⟨ρ, hρ⟩ | hM
    · constructor
      · intro h
        have := hle.mix hρ h
        rwa [union_eq_of_prop h (by rw [L.dom_valid hρ, hdom])] at this
      · intro h
        have := hle.proj h
        rwa [hdom, restrict_of_prop h] at this
    · constructor
      · intro h; exact absurd ⟨σ, h⟩ hM
      · intro h
        have := hle.proj h
        exact absurd ⟨_, this⟩ hM

open Classical in
/-- The key used to find the greatest element of a directed set of invariants: invariants
with fewer variables are larger, and among invariants with the same variables, nonempty ones
are larger. -/
noncomputable def key (𝓘 : Inv) : ℕ :=
  2 * 𝓘.dom.ncard + if ∃ σ, 𝓘.prop σ then 0 else 1

lemma key_lt_of_dom_ssubset {L M : Inv} (h : M.dom ⊂ L.dom) : M.key < L.key := by
  have := Set.ncard_lt_ncard h L.dom_finite
  unfold key; split_ifs <;> omega

/-- A directed set of invariants has a greatest element. -/
lemma exists_greatest (d : DSet Inv) : ∃ L ∈ d, ∀ 𝓙 ∈ d, 𝓙 ≤ L := by
  have hne : {n : ℕ | ∃ 𝓙 ∈ d, 𝓙.key = n}.Nonempty := by
    obtain ⟨𝓙, h𝓙⟩ := d.nonempty; exact ⟨𝓙.key, 𝓙, h𝓙, rfl⟩
  obtain ⟨L, hL, hkey⟩ := Nat.sInf_mem hne
  refine ⟨L, hL, fun 𝓙 h𝓙 ↦ ?_⟩
  obtain ⟨M, hM, hle₁, hle₂⟩ := d.directed _ h𝓙 _ hL
  have hmin : L.key ≤ M.key := by rw [hkey]; exact Nat.sInf_le ⟨M, hM, rfl⟩
  have hdom : M.dom = L.dom := by
    by_contra hne
    exact absurd (key_lt_of_dom_ssubset (Set.ssubset_iff_subset_ne.mpr ⟨hle₂.dom, hne⟩)) (by omega)
  have heq : M = L := by
    refine eq_of_le_of_dom_eq hle₂ hdom ?_
    by_contra hc
    push_neg at hc
    obtain ⟨hL', ⟨σ, hσ⟩⟩ := hc
    have : M.key < L.key := by
      unfold key; rw [hdom, if_pos ⟨σ, hσ⟩, if_neg (by simpa using hL')]; omega
    omega
  exact heq ▸ hle₁

noncomputable instance : DCPO Inv where
  dSup d := (exists_greatest d).choose
  lubOfDirected d := by
    obtain ⟨hL, hmax⟩ := (exists_greatest d).choose_spec
    exact ⟨fun _ h ↦ hmax _ h, fun _ hu ↦ hu hL⟩

/-- The supremum of a directed set of invariants is attained: it is a member of the set. -/
lemma dSup_mem (d : DSet Inv) : ∃ L ∈ d, d.dSup = L :=
  ⟨_, (exists_greatest d).choose_spec.1, rfl⟩

instance : ScottCompact Inv where
  scottCompact 𝓘 := by
    intro d hle
    obtain ⟨L, hL, heq⟩ := dSup_mem d
    exact ⟨L, hL, heq ▸ hle⟩

open Classical in
noncomputable def check (𝓘 : Inv) (σ : Mem) : ConvexPowerset Mem :=
  if 𝓘.prop (σ.restrict 𝓘.dom) then pure σ else ⊥

lemma check_monotone (σ : Mem) : Monotone (check · σ) := by
  intro 𝓘 𝓙 hle; simp only [check]
  by_cases h : 𝓘.prop (σ.restrict 𝓘.dom)
  · rw [if_pos h]
    have h' := hle.proj h
    rw [Mem.restrict_restrict, Set.inter_eq_self_of_subset_right hle.dom] at h'
    rw [if_pos h']
  · rw [if_neg h]; exact bot_le

open Classical in
noncomputable def replace (𝓘 : Inv) (σ : Mem) : ConvexPowerset Mem :=
  Nondet.nondet fun (τ : 𝓘.prop_finite.toFinset) ↦
    pure (τ ⊎ σ)

lemma bot_bind {α β : Type} (f : α → ConvexPowerset β) : (⊥ : ConvexPowerset α) >>= f = ⊥ := by
  refine le_antisymm (le_iff_supset.mpr fun ν _ ↦ ?_) bot_le
  refine ConvexPowerset.mem_bind.mpr ⟨PMF.pure ⊥, Set.mem_univ _, fun _ ↦ ν, ?_, ?_⟩
  · intro x hx
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact Set.mem_univ _
  · rw [PMF.pure_bind]

/-- If `σ` satisfies the larger invariant `𝓘`, then every way of replacing the `𝓙`-part of `σ`
is also a way of replacing its `𝓘`-part. -/
lemma replace_le {𝓘 𝓙 : Inv} (hle : 𝓘 ≤ 𝓙) {σ : Mem} (h : 𝓘.prop (σ.restrict 𝓘.dom)) :
    replace 𝓘 σ ≤ replace 𝓙 σ := by
  classical
  have hmemI : ∀ {τ}, 𝓘.prop τ → τ ∈ 𝓘.prop_finite.toFinset :=
    fun hτ ↦ 𝓘.prop_finite.mem_toFinset.mpr hτ
  have hmemJ : ∀ {τ}, τ ∈ 𝓙.prop_finite.toFinset → 𝓙.prop τ :=
    fun hτ ↦ 𝓙.prop_finite.mem_toFinset.mp hτ
  have hI : Nonempty 𝓘.prop_finite.toFinset := ⟨⟨_, hmemI h⟩⟩
  have hJ : Nonempty 𝓙.prop_finite.toFinset := by
    have := hle.proj h
    rw [Mem.restrict_restrict, Set.inter_eq_self_of_subset_right hle.dom] at this
    exact ⟨⟨_, 𝓙.prop_finite.mem_toFinset.mpr this⟩⟩
  -- The embedding of the memories of `𝓙` into those of `𝓘`
  let e : 𝓙.prop_finite.toFinset → 𝓘.prop_finite.toFinset := fun τ ↦
    ⟨τ.val ⊎ σ.restrict 𝓘.dom, hmemI (hle.mix h (hmemJ τ.2))⟩
  have he : ∀ τ, ((e τ).val ⊎ σ) = (τ.val ⊎ σ) := by
    intro τ
    change ((τ.val ⊎ σ.restrict 𝓘.dom) ⊎ σ) = _
    rw [Mem.union_assoc, Mem.union_restrict_self]
  have hinj : Function.Injective e := by
    intro τ τ' heq
    have h' := congrArg (fun (ρ : 𝓘.prop_finite.toFinset) ↦ ρ.val.restrict 𝓙.dom) heq
    simp only [e] at h'
    rw [Mem.restrict_union_left (𝓙.dom_valid (hmemJ τ.2)),
      Mem.restrict_union_left (𝓙.dom_valid (hmemJ τ'.2))] at h'
    exact Subtype.ext h'
  rw [le_iff_supset]
  intro ν hν
  change ν ∈ (if _ : Nonempty _ then ConvexPowerset.nondet _ else ⊥ : ConvexPowerset Mem)
  change ν ∈ (if _ : Nonempty _ then ConvexPowerset.nondet _ else ⊥ : ConvexPowerset Mem) at hν
  rw [dif_pos hI]
  rw [dif_pos hJ] at hν
  obtain ⟨ξ, k, hk, rfl⟩ := ConvexPowerset.mem_nondet.mp hν
  refine ConvexPowerset.mem_nondet.mpr ⟨ξ.map e, Function.extend e k (fun _ ↦ ξ.bind k), ?_, ?_⟩
  · intro i hi
    rw [PMF.support_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    simp only [Function.comp_apply]
    rw [hinj.extend_apply, he]
    exact hk j hj
  · rw [PMF.bind_map]
    congr 1
    funext j
    exact (hinj.extend_apply _ _ j).symm

/-- Checking and then replacing the invariant is monotone in the invariant: a larger
invariant allows more interference (Lemma 5.3 of the paper). -/
lemma checkReplace_monotone (σ : Mem) : Monotone (fun (𝓘 : Inv) ↦ check 𝓘 σ >>= replace 𝓘) := by
  intro 𝓘 𝓙 hle
  simp only
  by_cases h : 𝓘.prop (σ.restrict 𝓘.dom)
  · have h' := hle.proj h
    rw [Mem.restrict_restrict, Set.inter_eq_self_of_subset_right hle.dom] at h'
    rw [check, if_pos h, pure_bind, check, if_pos h', pure_bind]
    exact replace_le hle h
  · rw [check, if_neg h, bot_bind]
    exact bot_le

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

namespace WithInv

/-- The action component is monotone. -/
lemma inv_monotone {act : Type} : Monotone (fun a : WithInv act => a.inv) :=
  fun _ _ hle ↦ hle.2

/-- The invariants occurring in a directed set of annotated actions form a directed set. -/
def invs {act : Type} (d : DSet (WithInv act)) : DSet Inv :=
  d.image (fun a ↦ a.inv) inv_monotone

/-- All the elements of a directed set of annotated actions carry the same action. -/
lemma action_eq_of_mem {act : Type} (d : DSet (WithInv act)) {a : WithInv act} (ha : a ∈ d) :
    a.action = d.nonempty.choose.action := by
  obtain ⟨c, _, hle₁, hle₂⟩ := d.directed a ha _ d.nonempty.choose_spec
  rw [hle₁.1, ← hle₂.1]

end WithInv

noncomputable instance {act : Type} : DCPO (WithInv act) where
  dSup d := ⟨d.nonempty.choose.action, (WithInv.invs d).dSup⟩
  lubOfDirected d := by
    constructor
    · intro a ha
      exact ⟨WithInv.action_eq_of_mem d ha, DSet.le_dSup (Set.mem_image_of_mem _ ha)⟩
    · intro u hu
      refine ⟨(hu d.nonempty.choose_spec).1, DSet.dSup_le ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact (hu ha).2

instance {act : Type} : ScottCompact (WithInv act) where
  scottCompact a := by
    intro d hle
    obtain ⟨j, hj, hjle⟩ :=
      ScottCompact.scottCompact a.inv (WithInv.invs d) hle.2
    obtain ⟨z, hz, rfl⟩ := (Set.mem_image _ _ _).mp hj
    refine ⟨z, hz, ?_, hjle⟩
    rw [hle.1]
    exact (WithInv.action_eq_of_mem d hz).symm

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
    show (Inv.check 𝓘 σ >>= fun σ ↦ Inv.replace 𝓘 σ >>= fun σ ↦
        Sem.sem a σ >>= fun τ ↦ Inv.check 𝓘 τ) ≤
      (Inv.check 𝓙 σ >>= fun σ ↦ Inv.replace 𝓙 σ >>= fun σ ↦
        Sem.sem a σ >>= fun τ ↦ Inv.check 𝓙 τ)
    rw [← bind_assoc (Inv.check 𝓘 σ) (Inv.replace 𝓘), ← bind_assoc (Inv.check 𝓙 σ) (Inv.replace 𝓙)]
    refine ConvexPowerset.bind_monotone (Inv.checkReplace_monotone σ hle) ?_
    intro σ; apply ConvexPowerset.bind_monotone (le_refl _)
    intro τ; exact Inv.check_monotone _ hle

/-- A singleton pomset is monotone in its label. -/
lemma pom_singleton_mono {l : Type} [PartialOrder l] [OrderBot l] {ℓ ℓ' : l} (h : ℓ ≤ ℓ') :
    Pom.singleton ℓ ≤ Pom.singleton ℓ' := by
  refine ⟨Lpo.singleton default ℓ, rfl, Lpo.singleton default ℓ', rfl, ?_⟩
  refine ⟨Set.Subset.refl _, fun _ _ _ h ↦ h.elim, fun _ _ _ _ ↦ rfl, fun x ↦ ?_,
    fun _ _ ↦ rfl, fun _ hx ↦ Or.inl hx⟩
  change (if default = x then ℓ else ⊥) ≤ (if default = x then ℓ' else ⊥)
  split_ifs
  · exact h
  · exact le_refl _

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
    change (Pom.Semantics.while_body _ _)^[n] ⊥ ≤ (Pom.Semantics.while_body _ _)^[n] ⊥
    induction n with
    | zero => exact le_refl _
    | succ n ihn =>
      rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ',
        Function.comp_apply]
      unfold Pom.Semantics.while_body Pom.Semantics.if_stmt Pom.Semantics.seq
      exact Pom.guard_monotone _ (le_refl _) (Pom.seq_monotone ih ihn) (le_refl _)
  | act a =>
    simp only [withInv, to_pom]
    exact pom_singleton_mono (show (⟨a, 𝓘⟩ : WithInv act) ≤ ⟨a, 𝓙⟩ from ⟨rfl, hle⟩)

end Cmd


end Pcol
