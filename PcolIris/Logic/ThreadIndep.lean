/-
A thread that is local to its own footprint cannot observe the invariant part of the memory:
the probability that it establishes its postcondition does not depend on which invariant
state it is started in.

This is the key ingredient that lets the two threads of a parallel composition be analysed in
isolation: whatever the other thread does to the shared invariant state is already covered by
the nondeterministic havoc that each invariant-annotated action performs.
-/
import PcolIris.Logic.Locality

namespace Pcol

open ConvexPowerset Linearization

/-! ### Separating conjunction with the invariant -/

/-- For memories with domain `X ∪ 𝓘.dom`, membership in `A ∗ 𝓘` splits into the two parts. -/
lemma mem_sep_iff {A : Set Mem} {X : Set Var} {𝓘 : Inv}
    (hA : ∀ σ ∈ A, Mem.dom σ = X) (hdisj : Disjoint X 𝓘.dom)
    {p : Mem} (hp : Mem.dom p = X ∪ 𝓘.dom) :
    p ∈ Mem.sep A 𝓘.prop ↔ (p.restrict X ∈ A ∧ 𝓘.prop (p.restrict 𝓘.dom)) := by
  constructor
  · rintro ⟨a, ha, i, hi, rfl⟩
    have hda : Mem.dom a = X := hA a ha
    have hdi : Mem.dom i = 𝓘.dom := 𝓘.dom_valid hi
    have h1 : Mem.restrict (a.union i) X = a := by
      rw [Mem.restrict_union, Mem.restrict_eq_self (le_of_eq hda),
        Mem.restrict_eq_emp (by rw [hdi]; exact hdisj.symm), Mem.union_emp]
    have h2 : Mem.restrict (a.union i) 𝓘.dom = i := by
      rw [Mem.restrict_union, Mem.restrict_eq_emp (by rw [hda]; exact hdisj),
        Mem.restrict_eq_self (le_of_eq hdi), Mem.emp_union]
    rw [h1, h2]
    exact ⟨ha, hi⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.restrict X, h1, p.restrict 𝓘.dom, h2,
      (Mem.union_restrict_restrict (le_of_eq hp)).symm⟩

/-! ### `minProb` of a bind with pointwise equal continuations -/

lemma minProb_bind_congr {γ δ : Type} (s : ConvexPowerset γ) (F G : γ → ConvexPowerset δ)
    (E : Set δ) (h : ∀ x, minProb (F x) E = minProb (G x) E) :
    minProb (s >>= F) E = minProb (s >>= G) E := by
  rw [minProb_bind, minProb_bind]
  exact iInf_congr fun μ ↦ iInf_congr fun _ ↦ tsum_congr fun x ↦ by rw [h x]

/-! ### Independence of a local thread from the invariant state -/

section

variable {α : Lpofin (Label (WithInv Act) Test)} {A : Set Mem} {X : Set Var} {𝓘 : Inv}

open Classical in
/-- **Invariant independence.**  The worst-case probability that a local thread establishes
`A ∗ 𝓘` does not depend on the invariant state it starts from. -/
theorem lin_rec_indep
    (hinv : α.HasInv 𝓘) (hloc : ThreadLocal α X 𝓘)
    (hA : ∀ σ ∈ A, Mem.dom σ = X) (hdisj : Disjoint X 𝓘.dom) :
    ∀ (n : ℕ) (s : Finset Node) (φ : Form Node) (p p' : Mem), s.card ≤ n →
      (∀ y ∈ s, y ∈ α.nodes) →
      Mem.dom p = X ∪ 𝓘.dom → Mem.dom p' = X ∪ 𝓘.dom →
      p.restrict X = p'.restrict X →
      𝓘.prop (p.restrict 𝓘.dom) → 𝓘.prop (p'.restrict 𝓘.dom) →
      minProb (Lpofin.lin_rec α s φ p) (Mem.sep A 𝓘.prop) =
        minProb (Lpofin.lin_rec α s φ p') (Mem.sep A 𝓘.prop) := by
  intro n
  induction n with
  | zero =>
    intro s φ p p' hcard hs hdp hdp' hX hi hi'
    have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hs0
    rw [Lpofin.lin_rec, Lpofin.lin_rec, if_pos Lpofin.next_empty, if_pos Lpofin.next_empty]
    rw [minProb_pure, minProb_pure]
    congr 1
    refine propext ?_
    rw [mem_sep_iff hA hdisj hdp, mem_sep_iff hA hdisj hdp', hX]
    exact and_congr_right fun _ ↦ ⟨fun _ ↦ hi', fun _ ↦ hi⟩
  | succ n ih =>
    intro s φ p p' hcard hs hdp hdp' hX hi hi'
    by_cases hnext : Lpofin.next α s φ = ∅
    · rw [Lpofin.lin_rec, Lpofin.lin_rec, if_pos hnext, if_pos hnext]
      rw [minProb_pure, minProb_pure]
      congr 1
      refine propext ?_
      rw [mem_sep_iff hA hdisj hdp, mem_sep_iff hA hdisj hdp', hX]
      exact and_congr_right fun _ ↦ ⟨fun _ ↦ hi', fun _ ↦ hi⟩
    · rw [Lpofin.lin_rec, Lpofin.lin_rec, if_neg hnext, if_neg hnext]
      have hne : Nonempty ↑(Lpofin.next α s φ) := by
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hnext
        exact ⟨⟨x, hx⟩⟩
      have hnd : ∀ f : ↑(Lpofin.next α s φ) → ConvexPowerset Mem,
          (Nondet.nondet f : ConvexPowerset Mem) = ConvexPowerset.nondet f :=
        fun f ↦ dif_pos hne
      rw [hnd, hnd, minProb_nondet, minProb_nondet]
      refine iInf_congr fun x ↦ ?_
      have hxs : x.val ∈ s := (Finset.mem_filter.mp x.property).2.1
      have hxα : x.val ∈ α.nodes := hs x.val hxs
      have hcard' : (s.erase x.val).card ≤ n := by
        have h1 : (s.erase x.val).card + 1 = s.card := Finset.card_erase_add_one hxs
        omega
      cases hlab : α.lab x.val with
      | bot => simp only [Lpofin.lin_node, hlab]
      | fork =>
        simp only [Lpofin.lin_node, hlab]
        exact ih _ φ p p' hcard' (fun y hy ↦ hs y (Finset.mem_of_mem_erase hy))
          hdp hdp' hX hi hi'
      | act ac =>
        obtain ⟨a0, i0⟩ := ac
        have hac : i0 = 𝓘 := by
          have := hinv x.val hxα
          conv at this => arg 2; exact hlab
          exact this
        subst hac
        simp only [Lpofin.lin_node, hlab]
        rw [sem_withInv_indep hdp hdp' hX hi hi']
      | test b =>
        have hb : TestLocal b X := by
          have := hloc x.val hxα
          conv at this => arg 2; exact hlab
          exact this
        simp only [Lpofin.lin_node, hlab]
        rw [hb p, hb p', hX]
        refine minProb_bind_congr _ _ _ _ fun r ↦ ?_
        refine ih _ _ p p' ?_ ?_ hdp hdp' hX hi hi'
        · exact le_trans (Finset.card_le_card Lpofin.filter_by_outcome_sub_erase) hcard'
        · exact fun y hy ↦
            hs y (Finset.mem_of_mem_erase (Lpofin.filter_by_outcome_sub_erase hy))

end

end Pcol
