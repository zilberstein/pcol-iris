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
