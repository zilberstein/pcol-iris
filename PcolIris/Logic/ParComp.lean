/-
The parallel-composition (frame) law for the worst-case probability semantics.

The two threads of `α ∥ β` are analysed in isolation: each is assumed to be *local* to its own
footprint (`ThreadLocal`), the invariant `𝓘` being the only shared state.  Under those
hypotheses the worst-case probability that the parallel composition establishes `A ∗ B ∗ 𝓘` is
at least the product of the worst-case probabilities that the threads establish `A ∗ 𝓘` and
`B ∗ 𝓘`.
-/
import PcolIris.Logic.ThreadIndep

namespace Pcol

open ConvexPowerset Linearization

/-! ### Generic `minProb` lemmas used by the induction -/

/-- A product of `minProb`s of `pure`s. -/
lemma minProb_pure_mul_le {γ : Type} {x y z : γ} {E F G : Set γ}
    (h : x ∈ E → y ∈ F → z ∈ G) :
    minProb (pure x) E * minProb (pure y) F ≤ minProb (pure z) G := by
  classical
  by_cases hx : x ∈ E
  · by_cases hy : y ∈ F
    · rw [minProb_pure_of_mem hx, minProb_pure_of_mem hy, minProb_pure_of_mem (h hx hy),
        one_mul]
    · rw [minProb_pure_of_notMem hy, mul_zero]
      exact bot_le
  · rw [minProb_pure_of_notMem hx, zero_mul]
    exact bot_le

/-- The `assume`-guarded form of `minProb_bind_mul_mono`: it is enough to compare the two
continuations on the outcomes satisfying `Q`, provided `s` only produces such outcomes. -/
lemma minProb_bind_mul_mono_assume {γ : Type} (s : ConvexPowerset Mem) (Q : Mem → Prop)
    (hs : s = s >>= assume Q) (F G : Mem → ConvexPowerset γ) (E E' : Set γ) (c : ENNReal)
    (h : ∀ m', Q m' → minProb (G m') E' * c ≤ minProb (F m') E) :
    minProb (s >>= G) E' * c ≤ minProb (s >>= F) E := by
  conv_lhs => rw [hs]
  conv_rhs => rw [hs]
  rw [bind_assoc, bind_assoc]
  refine minProb_bind_mul_mono _ _ _ _ _ _ fun m' _ ↦ ?_
  by_cases hq : Q m'
  · rw [assume_pos hq, pure_bind, pure_bind]
    exact h m' hq
  · rw [assume_neg hq, bot_bind, bot_bind, minProb_bot, zero_mul]
    exact bot_le

/-- A schedulable node bounds the worst case of a linearization from above. -/
lemma minProb_lin_rec_le_lin_node {a : Lpofin (Label (WithInv Act) Test)} {s : Finset Node}
    {φ : Form Node} {st : Mem} {E : Set Mem} {x : Node} (hx : x ∈ Lpofin.next a s φ)
    (hxs : x ∈ s) :
    minProb (Lpofin.lin_rec a s φ st) E ≤ minProb (Lpofin.lin_node a s φ x hxs st) E := by
  classical
  have hne : Lpofin.next a s φ ≠ ∅ := fun h ↦ by rw [h] at hx; exact absurd hx (by simp)
  have hnonempty : Nonempty ↑(Lpofin.next a s φ) := by exact ⟨⟨x, hx⟩⟩
  rw [Lpofin.lin_rec, if_neg hne]
  rw [show (Nondet.nondet (fun y : ↑(Lpofin.next a s φ) =>
        Lpofin.lin_node a s φ y.val (Finset.mem_filter.mp y.property).2.1 st) :
      ConvexPowerset Mem) = ConvexPowerset.nondet _ from dif_pos hnonempty]
  rw [minProb_nondet]
  exact iInf_le _ (⟨x, hx⟩ : ↑(Lpofin.next a s φ))

/-! ### Splitting a memory into the two footprints and the invariant -/

section Split

variable {A B : Set Mem} {X₁ X₂ : Set Var} {𝓘 : Inv}

/-- A memory whose two thread-local restrictions satisfy `A ∗ 𝓘` and `B ∗ 𝓘` satisfies
`A ∗ B ∗ 𝓘`. -/
lemma mem_sep_of_restrict
    (hA : ∀ σ ∈ A, Mem.dom σ = X₁) (hB : ∀ σ ∈ B, Mem.dom σ = X₂)
    (hdA : Disjoint X₁ 𝓘.dom) (hdB : Disjoint X₂ 𝓘.dom)
    {m : Mem} (hm : Mem.dom m = X₁ ∪ X₂ ∪ 𝓘.dom)
    (h₁ : m.restrict (X₁ ∪ 𝓘.dom) ∈ Mem.sep A 𝓘.prop)
    (h₂ : m.restrict (X₂ ∪ 𝓘.dom) ∈ Mem.sep B 𝓘.prop) :
    m ∈ Mem.sep A (Mem.sep B 𝓘.prop) := by
  have hsub₁ : X₁ ∪ 𝓘.dom ⊆ Mem.dom m := by
    rw [hm]; exact Set.union_subset_union_left _ Set.subset_union_left
  have hsub₂ : X₂ ∪ 𝓘.dom ⊆ Mem.dom m := by
    rw [hm]; exact Set.union_subset_union_left _ Set.subset_union_right
  have hd₁ : Mem.dom (show Mem from m.restrict (X₁ ∪ 𝓘.dom)) = X₁ ∪ 𝓘.dom := by
    rw [Mem.restrict_dom]; exact Set.inter_eq_self_of_subset_right hsub₁
  have hd₂ : Mem.dom (show Mem from m.restrict (X₂ ∪ 𝓘.dom)) = X₂ ∪ 𝓘.dom := by
    rw [Mem.restrict_dom]; exact Set.inter_eq_self_of_subset_right hsub₂
  obtain ⟨ha, -⟩ := (mem_sep_iff hA hdA hd₁).mp h₁
  obtain ⟨hb, hi⟩ := (mem_sep_iff hB hdB hd₂).mp h₂
  rw [Mem.restrict_restrict, Set.union_inter_cancel_left] at ha
  rw [Mem.restrict_restrict, Set.union_inter_cancel_left] at hb
  rw [Mem.restrict_restrict, Set.union_inter_cancel_right] at hi
  refine ⟨m.restrict X₁, ha, m.restrict (X₂ ∪ 𝓘.dom), ?_, ?_⟩
  · exact ⟨m.restrict X₂, hb, m.restrict 𝓘.dom, hi,
      (Mem.restrict_union_restrict m X₂ 𝓘.dom).symm⟩
  · rw [Mem.restrict_union_restrict, ← Set.union_assoc, ← hm, Mem.restrict_self]

end Split

/-! ### The parallel-composition law -/

section Main

variable {α β : Lpofin (Label (WithInv Act) Test)} {r : Node}
  {hr₁ : r ∉ α.nodes} {hr₂ : r ∉ β.nodes} {hdn : Disjoint α.nodes β.nodes}
  {A B : Set Mem} {X₁ X₂ : Set Var} {𝓘 : Inv}

/-- **Parallel composition, recursive form.**  Two local threads scheduled together do at
least as well as the product of what they do in isolation. -/
theorem lin_rec_par_mul
    (hinv₁ : α.HasInv 𝓘) (hinv₂ : β.HasInv 𝓘)
    (hloc₁ : ThreadLocal α X₁ 𝓘) (hloc₂ : ThreadLocal β X₂ 𝓘)
    (hA : ∀ σ ∈ A, Mem.dom σ = X₁) (hB : ∀ σ ∈ B, Mem.dom σ = X₂)
    (hdA : Disjoint X₁ 𝓘.dom) (hdB : Disjoint X₂ 𝓘.dom) (hdX : Disjoint X₁ X₂) :
    ∀ (n : ℕ) (s₁ s₂ : Finset Node) (φ₁ φ₂ : Form Node) (m : Mem),
      s₁.card + s₂.card ≤ n →
      (∀ y ∈ s₁, y ∈ α.nodes) → (∀ y ∈ s₂, y ∈ β.nodes) →
      φ₁.DependsOn (α.nodes \ ↑s₁) → φ₂.DependsOn (β.nodes \ ↑s₂) →
      φ₁.sat → φ₂.sat →
      Mem.dom m = X₁ ∪ X₂ ∪ 𝓘.dom → 𝓘.prop (m.restrict 𝓘.dom) →
      minProb (Lpofin.lin_rec α s₁ φ₁ (show Mem from m.restrict (X₁ ∪ 𝓘.dom)))
          (Mem.sep A 𝓘.prop) *
        minProb (Lpofin.lin_rec β s₂ φ₂ (show Mem from m.restrict (X₂ ∪ 𝓘.dom)))
          (Mem.sep B 𝓘.prop) ≤
      minProb (Lpofin.lin_rec (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) (φ₁.and φ₂) m)
        (Mem.sep A (Mem.sep B 𝓘.prop)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro s₁ s₂ φ₁ φ₂ m hcard _ _ _ _ _ _ hdm _
    have h1 : s₁ = ∅ := Finset.card_eq_zero.mp (by omega)
    have h2 : s₂ = ∅ := Finset.card_eq_zero.mp (by omega)
    subst h1; subst h2
    rw [Lpofin.lin_rec, Lpofin.lin_rec, Lpofin.lin_rec, if_pos Lpofin.next_empty,
      if_pos Lpofin.next_empty,
      if_pos (show Lpofin.next (Lpofin.par hr₁ hr₂ hdn) (∅ ∪ ∅) (φ₁.and φ₂) = ∅ by
        rw [Finset.empty_union]; exact Lpofin.next_empty)]
    exact minProb_pure_mul_le (mem_sep_of_restrict hA hB hdA hdB hdm)
  | succ n ih =>
    intro s₁ s₂ φ₁ φ₂ m hcard hs₁ hs₂ hd₁ hd₂ hsat₁ hsat₂ hdm hi
    have hdep₁ : φ₁.DependsOn α.nodes := Form.DependsOn.monotone _ Set.sdiff_subset hd₁
    have hdep₂ : φ₂.DependsOn β.nodes := Form.DependsOn.monotone _ Set.sdiff_subset hd₂
    have hnextP : Lpofin.next (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) (φ₁.and φ₂)
        = Lpofin.next α s₁ φ₁ ∪ Lpofin.next β s₂ φ₂ :=
      Lpofin.next_par hs₁ hs₂ hdep₁ hdep₂ hsat₁ hsat₂
    by_cases hE : Lpofin.next (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) (φ₁.and φ₂) = ∅
    · have hE12 : Lpofin.next α s₁ φ₁ = ∅ ∧ Lpofin.next β s₂ φ₂ = ∅ := by
        rw [hnextP] at hE; exact Finset.union_eq_empty.mp hE
      rw [Lpofin.lin_rec, Lpofin.lin_rec, Lpofin.lin_rec, if_pos hE12.1, if_pos hE12.2,
        if_pos hE]
      exact minProb_pure_mul_le (mem_sep_of_restrict hA hB hdA hdB hdm)
    · have hneP : Nonempty ↑(Lpofin.next (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) (φ₁.and φ₂)) := by
        obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hE
        exact ⟨⟨y, hy⟩⟩
      have hunfold : Lpofin.lin_rec (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) (φ₁.and φ₂) m
          = ConvexPowerset.nondet
              (fun y : ↑(Lpofin.next (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) (φ₁.and φ₂)) =>
                Lpofin.lin_node (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) (φ₁.and φ₂) y.val
                  (Finset.mem_filter.mp y.property).2.1 m) := by
        rw [Lpofin.lin_rec, if_neg hE]
        exact dif_pos hneP
      rw [hunfold, minProb_nondet]
      refine le_iInf fun y ↦ ?_
      have hy : y.val ∈ Lpofin.next α s₁ φ₁ ∪ Lpofin.next β s₂ φ₂ := by
        rw [← hnextP]; exact y.property
      have hW₁sub : X₁ ∪ 𝓘.dom ⊆ Mem.dom m := by
        rw [hdm]; exact Set.union_subset_union_left _ Set.subset_union_left
      have hW₂sub : X₂ ∪ 𝓘.dom ⊆ Mem.dom m := by
        rw [hdm]; exact Set.union_subset_union_left _ Set.subset_union_right
      have hdomW₁ : Mem.dom (show Mem from m.restrict (X₁ ∪ 𝓘.dom)) = X₁ ∪ 𝓘.dom := by
        rw [Mem.restrict_dom]; exact Set.inter_eq_self_of_subset_right hW₁sub
      have hdomW₂ : Mem.dom (show Mem from m.restrict (X₂ ∪ 𝓘.dom)) = X₂ ∪ 𝓘.dom := by
        rw [Mem.restrict_dom]; exact Set.inter_eq_self_of_subset_right hW₂sub
      have hD₁ : 𝓘.dom ⊆ X₁ ∪ 𝓘.dom := Set.subset_union_right
      have hD₂ : 𝓘.dom ⊆ X₂ ∪ 𝓘.dom := Set.subset_union_right
      rcases Finset.mem_union.mp hy with hy₁ | hy₂
      · -- the left thread takes the step
        have hys₁ : y.val ∈ s₁ := (Finset.mem_filter.mp hy₁).2.1
        have hyα : y.val ∈ α.nodes := hs₁ y.val hys₁
        have hys₂ : y.val ∉ s₂ := fun hc ↦ Set.disjoint_left.mp hdn hyα (hs₂ y.val hc)
        have hlabP : (Lpofin.par hr₁ hr₂ hdn).lab y.val = α.lab y.val :=
          Lpofin.par_lab_left hr₁ hr₂ hdn hyα
        have herase : (s₁ ∪ s₂).erase y.val = s₁.erase y.val ∪ s₂ := by
          rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hys₂]
        have hcard' : (s₁.erase y.val).card + s₂.card ≤ n := by
          have := Finset.card_erase_add_one hys₁
          omega
        have hs₁' : ∀ z ∈ s₁.erase y.val, z ∈ α.nodes :=
          fun z hz ↦ hs₁ z (Finset.mem_of_mem_erase hz)
        have hd₁' : φ₁.DependsOn (α.nodes \ ↑(s₁.erase y.val)) :=
          Form.DependsOn.monotone _
            (Set.sdiff_subset_sdiff_right (by exact_mod_cast Finset.erase_subset _ _)) hd₁
        refine le_trans (mul_le_mul_left (minProb_lin_rec_le_lin_node hy₁ hys₁) _) ?_
        cases hlab : α.lab y.val with
        | bot =>
          simp only [Lpofin.lin_node, hlabP, hlab]
          rw [minProb_bot, zero_mul]
          exact bot_le
        | fork =>
          simp only [Lpofin.lin_node, hlabP, hlab, herase]
          exact ih (s₁.erase y.val) s₂ φ₁ φ₂ m hcard' hs₁' hs₂ hd₁' hd₂ hsat₁ hsat₂ hdm hi
        | act ac =>
          obtain ⟨a0, i0⟩ := ac
          have hac : i0 = 𝓘 := by
            have := hinv₁ y.val hyα
            conv at this => arg 2; exact hlab
            exact this
          subst i0
          obtain ⟨hlocA, hlocD⟩ := by
            have := hloc₁ y.val hyα; conv at this => arg 2; exact hlab
            exact this
          simp only [Lpofin.lin_node, hlabP, hlab, herase]
          rw [sem_withInv_frame (W := X₁ ∪ 𝓘.dom) hD₁ hlocA hlocD hW₁sub, ConvexPowerset.bind_assoc]
          simp only [pure_bind]
          refine minProb_bind_mul_mono_assume _
            (fun m' ↦ Mem.dom m' = X₁ ∪ 𝓘.dom ∧ 𝓘.prop (m'.restrict 𝓘.dom))
            (sem_withInv_assume hD₁ hlocD hdomW₁) _ _ _ _ _ ?_
          rintro m' ⟨hm'dom, hm'inv⟩
          have hdm₂ : Mem.dom (m'.union m) = X₁ ∪ X₂ ∪ 𝓘.dom := by
            rw [Mem.dom_union, hm'dom, hdm]
            ext v; simp only [Set.mem_union]; tauto
          have hres₁ : Mem.restrict (m'.union m) (X₁ ∪ 𝓘.dom) = m' :=
            Mem.restrict_union_left hm'dom m
          have hresI : Mem.restrict (m'.union m) 𝓘.dom = Mem.restrict m' 𝓘.dom :=
            Mem.restrict_union_of_subset_dom (by rw [hm'dom]; exact hD₁) m
          have hi₂ : 𝓘.prop (Mem.restrict (m'.union m) 𝓘.dom) := by rw [hresI]; exact hm'inv
          have hres₂ : Mem.restrict (m'.union m) X₂ = Mem.restrict m X₂ :=
            Mem.restrict_union_of_disjoint
              (by rw [hm'dom]; exact Set.disjoint_union_left.mpr ⟨hdX, hdB.symm⟩) m
          have hbeta : minProb (Lpofin.lin_rec β s₂ φ₂
                (show Mem from (m'.union m).restrict (X₂ ∪ 𝓘.dom))) (Mem.sep B 𝓘.prop)
              = minProb (Lpofin.lin_rec β s₂ φ₂
                (show Mem from m.restrict (X₂ ∪ 𝓘.dom))) (Mem.sep B 𝓘.prop) := by
            refine lin_rec_indep hinv₂ hloc₂ hB hdB s₂.card s₂ φ₂ _ _ le_rfl hs₂ ?_ hdomW₂ ?_ ?_ ?_
            · rw [Mem.restrict_dom, hdm₂]
              exact Set.inter_eq_self_of_subset_right
                (Set.union_subset_union_left _ Set.subset_union_right)
            · rw [Mem.restrict_restrict, Mem.restrict_restrict, Set.union_inter_cancel_left,
                hres₂]
            · rw [Mem.restrict_restrict, Set.union_inter_cancel_right, hresI]; exact hm'inv
            · rw [Mem.restrict_restrict, Set.union_inter_cancel_right]; exact hi
          calc minProb (Lpofin.lin_rec α (s₁.erase y.val) φ₁ m') (Mem.sep A 𝓘.prop) *
                minProb (Lpofin.lin_rec β s₂ φ₂ (show Mem from m.restrict (X₂ ∪ 𝓘.dom)))
                  (Mem.sep B 𝓘.prop)
              = minProb (Lpofin.lin_rec α (s₁.erase y.val) φ₁
                    (show Mem from (m'.union m).restrict (X₁ ∪ 𝓘.dom))) (Mem.sep A 𝓘.prop) *
                  minProb (Lpofin.lin_rec β s₂ φ₂
                    (show Mem from (m'.union m).restrict (X₂ ∪ 𝓘.dom))) (Mem.sep B 𝓘.prop) := by
                rw [hres₁, hbeta]
            _ ≤ _ := ih (s₁.erase y.val) s₂ φ₁ φ₂ (m'.union m) hcard' hs₁' hs₂ hd₁' hd₂
                    hsat₁ hsat₂ hdm₂ hi₂
        | test b =>
          have hb : TestLocal b X₁ := by
            have := hloc₁ y.val hyα
            conv at this => arg 2; exact hlab
            exact this
          simp only [Lpofin.lin_node, hlabP, hlab]
          have hsem : (Sem.sem b (show Mem from m.restrict (X₁ ∪ 𝓘.dom)) :
              ConvexPowerset Bool) = Sem.sem b m := by
            rw [hb (show Mem from m.restrict (X₁ ∪ 𝓘.dom)), hb m, Mem.restrict_restrict,
              Set.union_inter_cancel_left]
          rw [hsem]
          refine minProb_bind_mul_mono _ _ _ _ _ _ fun rb _ ↦ ?_
          have hsubf : Lpofin.filter_by_outcome α s₁ y.val rb ⊆ s₁.erase y.val :=
            Lpofin.filter_by_outcome_sub_erase
          rw [Lpofin.filter_by_outcome_par_left rb hs₁ hs₂ hyα, Form.and_comm_assoc]
          refine ih (Lpofin.filter_by_outcome α s₁ y.val rb) s₂ _ φ₂ m ?_ ?_ hs₂ ?_ hd₂ ?_
            hsat₂ hdm hi
          · have := Finset.card_le_card hsubf
            omega
          · exact fun z hz ↦ hs₁' z (hsubf hz)
          · refine Form.DependsOn.monotone _ ?_
              (Form.DependsOn.and hd₁ (Form.dependsOn_ite_literal y.val rb))
            rintro v (⟨hvα, hvs⟩ | rfl)
            · exact ⟨hvα, fun hc ↦ hvs (Finset.mem_of_mem_erase (hsubf hc))⟩
            · exact ⟨hyα, fun hc ↦ (Finset.mem_erase.mp (hsubf hc)).1 rfl⟩
          · exact Form.sat_and_of_disjoint hd₁ (Form.dependsOn_ite_literal y.val rb)
              (Set.disjoint_singleton_right.mpr (fun hc ↦ hc.2 hys₁)) hsat₁
              (Form.sat_ite_literal y.val rb)
      · -- the right thread takes the step
        have hys₂ : y.val ∈ s₂ := (Finset.mem_filter.mp hy₂).2.1
        have hyβ : y.val ∈ β.nodes := hs₂ y.val hys₂
        have hys₁ : y.val ∉ s₁ := fun hc ↦ Set.disjoint_left.mp hdn (hs₁ y.val hc) hyβ
        have hlabP : (Lpofin.par hr₁ hr₂ hdn).lab y.val = β.lab y.val :=
          Lpofin.par_lab_right hr₁ hr₂ hdn hyβ
        have herase : (s₁ ∪ s₂).erase y.val = s₁ ∪ s₂.erase y.val := by
          rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hys₁]
        have hcard' : s₁.card + (s₂.erase y.val).card ≤ n := by
          have := Finset.card_erase_add_one hys₂
          omega
        have hs₂' : ∀ z ∈ s₂.erase y.val, z ∈ β.nodes :=
          fun z hz ↦ hs₂ z (Finset.mem_of_mem_erase hz)
        have hd₂' : φ₂.DependsOn (β.nodes \ ↑(s₂.erase y.val)) :=
          Form.DependsOn.monotone _
            (Set.sdiff_subset_sdiff_right (by exact_mod_cast Finset.erase_subset _ _)) hd₂
        refine le_trans (mul_le_mul_right (minProb_lin_rec_le_lin_node hy₂ hys₂) _) ?_
        rw [mul_comm]
        cases hlab : β.lab y.val with
        | bot =>
          simp only [Lpofin.lin_node, hlabP, hlab]
          rw [minProb_bot, zero_mul]
          exact bot_le
        | fork =>
          simp only [Lpofin.lin_node, hlabP, hlab, herase]
          rw [mul_comm]
          exact ih s₁ (s₂.erase y.val) φ₁ φ₂ m hcard' hs₁ hs₂' hd₁ hd₂' hsat₁ hsat₂ hdm hi
        | act ac =>
          obtain ⟨a0, i0⟩ := ac
          have hac : i0 = 𝓘 := by
            have := hinv₂ y.val hyβ
            conv at this => arg 2; exact hlab
            exact this
          subst i0
          obtain ⟨hlocA, hlocD⟩ := by
            have := hloc₂ y.val hyβ; conv at this => arg 2; exact hlab
            exact this
          simp only [Lpofin.lin_node, hlabP, hlab, herase]
          rw [sem_withInv_frame (W := X₂ ∪ 𝓘.dom) hD₂ hlocA hlocD hW₂sub, ConvexPowerset.bind_assoc]
          simp only [pure_bind]
          refine minProb_bind_mul_mono_assume _
            (fun m' ↦ Mem.dom m' = X₂ ∪ 𝓘.dom ∧ 𝓘.prop (m'.restrict 𝓘.dom))
            (sem_withInv_assume hD₂ hlocD hdomW₂) _ _ _ _ _ ?_
          rintro m' ⟨hm'dom, hm'inv⟩
          have hdm₂ : Mem.dom (m'.union m) = X₁ ∪ X₂ ∪ 𝓘.dom := by
            rw [Mem.dom_union, hm'dom, hdm]
            ext v; simp only [Set.mem_union]; tauto
          have hres₂ : Mem.restrict (m'.union m) (X₂ ∪ 𝓘.dom) = m' :=
            Mem.restrict_union_left hm'dom m
          have hresI : Mem.restrict (m'.union m) 𝓘.dom = Mem.restrict m' 𝓘.dom :=
            Mem.restrict_union_of_subset_dom (by rw [hm'dom]; exact hD₂) m
          have hi₂ : 𝓘.prop (Mem.restrict (m'.union m) 𝓘.dom) := by rw [hresI]; exact hm'inv
          have hres₁ : Mem.restrict (m'.union m) X₁ = Mem.restrict m X₁ :=
            Mem.restrict_union_of_disjoint
              (by rw [hm'dom]; exact Set.disjoint_union_left.mpr ⟨hdX.symm, hdA.symm⟩) m
          have halpha : minProb (Lpofin.lin_rec α s₁ φ₁
                (show Mem from (m'.union m).restrict (X₁ ∪ 𝓘.dom))) (Mem.sep A 𝓘.prop)
              = minProb (Lpofin.lin_rec α s₁ φ₁
                (show Mem from m.restrict (X₁ ∪ 𝓘.dom))) (Mem.sep A 𝓘.prop) := by
            refine lin_rec_indep hinv₁ hloc₁ hA hdA s₁.card s₁ φ₁ _ _ le_rfl hs₁ ?_ hdomW₁ ?_ ?_ ?_
            · rw [Mem.restrict_dom, hdm₂]
              exact Set.inter_eq_self_of_subset_right
                (Set.union_subset_union_left _ Set.subset_union_left)
            · rw [Mem.restrict_restrict, Mem.restrict_restrict, Set.union_inter_cancel_left,
                hres₁]
            · rw [Mem.restrict_restrict, Set.union_inter_cancel_right, hresI]; exact hm'inv
            · rw [Mem.restrict_restrict, Set.union_inter_cancel_right]; exact hi
          calc minProb (Lpofin.lin_rec β (s₂.erase y.val) φ₂ m') (Mem.sep B 𝓘.prop) *
                minProb (Lpofin.lin_rec α s₁ φ₁ (show Mem from m.restrict (X₁ ∪ 𝓘.dom)))
                  (Mem.sep A 𝓘.prop)
              = minProb (Lpofin.lin_rec α s₁ φ₁
                    (show Mem from (m'.union m).restrict (X₁ ∪ 𝓘.dom))) (Mem.sep A 𝓘.prop) *
                  minProb (Lpofin.lin_rec β (s₂.erase y.val) φ₂
                    (show Mem from (m'.union m).restrict (X₂ ∪ 𝓘.dom))) (Mem.sep B 𝓘.prop) := by
                rw [hres₂, halpha, mul_comm]
            _ ≤ _ := ih s₁ (s₂.erase y.val) φ₁ φ₂ (m'.union m) hcard' hs₁ hs₂' hd₁ hd₂'
                    hsat₁ hsat₂ hdm₂ hi₂
        | test b =>
          have hb : TestLocal b X₂ := by
            have := hloc₂ y.val hyβ
            conv at this => arg 2; exact hlab
            exact this
          simp only [Lpofin.lin_node, hlabP, hlab]
          have hsem : (Sem.sem b (show Mem from m.restrict (X₂ ∪ 𝓘.dom)) :
              ConvexPowerset Bool) = Sem.sem b m := by
            rw [hb (show Mem from m.restrict (X₂ ∪ 𝓘.dom)), hb m, Mem.restrict_restrict,
              Set.union_inter_cancel_left]
          rw [hsem]
          refine minProb_bind_mul_mono _ _ _ _ _ _ fun rb _ ↦ ?_
          have hsubf : Lpofin.filter_by_outcome β s₂ y.val rb ⊆ s₂.erase y.val :=
            Lpofin.filter_by_outcome_sub_erase
          rw [Lpofin.filter_by_outcome_par_right rb hs₁ hs₂ hyβ, Form.and_assoc, mul_comm]
          refine ih s₁ (Lpofin.filter_by_outcome β s₂ y.val rb) φ₁ _ m ?_ hs₁ ?_ hd₁ ?_
            hsat₁ ?_ hdm hi
          · have := Finset.card_le_card hsubf
            omega
          · exact fun z hz ↦ hs₂' z (hsubf hz)
          · refine Form.DependsOn.monotone _ ?_
              (Form.DependsOn.and hd₂ (Form.dependsOn_ite_literal y.val rb))
            rintro v (⟨hvβ, hvs⟩ | rfl)
            · exact ⟨hvβ, fun hc ↦ hvs (Finset.mem_of_mem_erase (hsubf hc))⟩
            · exact ⟨hyβ, fun hc ↦ (Finset.mem_erase.mp (hsubf hc)).1 rfl⟩
          · exact Form.sat_and_of_disjoint hd₂ (Form.dependsOn_ite_literal y.val rb)
              (Set.disjoint_singleton_right.mpr (fun hc ↦ hc.2 hys₂)) hsat₂
              (Form.sat_ite_literal y.val rb)

/-- **Parallel composition, top level.**  The worst-case probability that `α ∥ β` establishes
`A ∗ B ∗ 𝓘` from a memory `m` split into the two footprints and the invariant is at least the
product of the two threads' worst-case probabilities. -/
theorem lin_par_mul
    (hinv₁ : α.HasInv 𝓘) (hinv₂ : β.HasInv 𝓘)
    (hloc₁ : ThreadLocal α X₁ 𝓘) (hloc₂ : ThreadLocal β X₂ 𝓘)
    (hA : ∀ σ ∈ A, Mem.dom σ = X₁) (hB : ∀ σ ∈ B, Mem.dom σ = X₂)
    (hdA : Disjoint X₁ 𝓘.dom) (hdB : Disjoint X₂ 𝓘.dom) (hdX : Disjoint X₁ X₂)
    {m : Mem} (hdm : Mem.dom m = X₁ ∪ X₂ ∪ 𝓘.dom) (hi : 𝓘.prop (m.restrict 𝓘.dom)) :
    minProb (Lpofin.lin α (show Mem from m.restrict (X₁ ∪ 𝓘.dom))) (Mem.sep A 𝓘.prop) *
        minProb (Lpofin.lin β (show Mem from m.restrict (X₂ ∪ 𝓘.dom))) (Mem.sep B 𝓘.prop) ≤
      minProb (Lpofin.lin (Lpofin.par hr₁ hr₂ hdn) m) (Mem.sep A (Mem.sep B 𝓘.prop)) := by
  classical
  have hnext := Lpofin.next_par_root (hr₁ := hr₁) (hr₂ := hr₂) (hdn := hdn)
  have herase := Lpofin.par_nodes_finset_erase_root (hr₁ := hr₁) (hr₂ := hr₂) (hdn := hdn)
  have hne : Lpofin.next (Lpofin.par hr₁ hr₂ hdn) (Lpofin.par hr₁ hr₂ hdn).nodes_finset
      Form.true ≠ ∅ := by
    rw [hnext]; exact Finset.singleton_ne_empty r
  have hstep : (Lpofin.lin (Lpofin.par hr₁ hr₂ hdn) m : ConvexPowerset Mem)
      = Lpofin.lin_rec (Lpofin.par hr₁ hr₂ hdn) (α.nodes_finset ∪ β.nodes_finset)
          Form.true m := by
    change Lpofin.lin_rec (Lpofin.par hr₁ hr₂ hdn) _ Form.true m = _
    rw [Lpofin.lin_rec, if_neg hne, Nondet.finset_singleton r hnext]
    simp only [Lpofin.lin_node, Lpofin.par_lab_root, herase]
  have hdepT : ∀ (a : Lpofin (Label (WithInv Act) Test)),
      (Form.true : Form Node).DependsOn (a.nodes \ ↑a.nodes_finset) :=
    fun _ ↦ Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true
  have hsatT : (Form.true : Form Node).sat := ⟨∅, trivial⟩
  refine le_of_le_of_eq (lin_rec_par_mul (hr₁ := hr₁) (hr₂ := hr₂) (hdn := hdn)
      hinv₁ hinv₂ hloc₁ hloc₂ hA hB hdA hdB hdX
      (α.nodes_finset.card + β.nodes_finset.card) α.nodes_finset β.nodes_finset
      Form.true Form.true m le_rfl
      (fun y hy ↦ (Set.Finite.mem_toFinset _).mp hy)
      (fun y hy ↦ (Set.Finite.mem_toFinset _).mp hy)
      (hdepT α) (hdepT β) hsatT hsatT hdm hi) ?_
  rw [Form.true_and, ← hstep]

/-- **Lemma C.3, repaired.**  The frame law for parallel composition, under the extra
hypotheses that each thread is local to its own footprint (`ThreadLocal`) and that the two
postconditions are domain-uniform.

These hypotheses are necessary: without them the statement is false, see
`Pcol.par_comp_fin_counterexample` in `PcolIris/Logic/ParCounterexample.lean`. -/
theorem par_comp_fin_local
    {σ₁ σ₂ τ τ₁ τ₂ : Mem}
    (hinv₁ : α.HasInv 𝓘) (hinv₂ : β.HasInv 𝓘)
    (hloc₁ : ThreadLocal α σ₁.dom 𝓘) (hloc₂ : ThreadLocal β σ₂.dom 𝓘)
    (hA : ∀ σ ∈ A, Mem.dom σ = σ₁.dom) (hB : ∀ σ ∈ B, Mem.dom σ = σ₂.dom)
    (hτ : 𝓘.prop τ) (hτ₁ : 𝓘.prop τ₁) (hτ₂ : 𝓘.prop τ₂)
    (hd₁ : Disjoint τ.dom σ₁.dom) (hd₂ : Disjoint τ.dom σ₂.dom)
    (hd : Disjoint σ₁.dom σ₂.dom) :
    minProb (Lpofin.lin (Lpofin.par hr₁ hr₂ hdn) (σ₁.union (σ₂.union τ)))
        (Mem.sep A (Mem.sep B 𝓘.prop)) ≥
      minProb (Lpofin.lin α (σ₁.union τ₁)) (Mem.sep A 𝓘.prop) *
        minProb (Lpofin.lin β (σ₂.union τ₂)) (Mem.sep B 𝓘.prop) := by
  classical
  have hdτ : Mem.dom τ = 𝓘.dom := 𝓘.dom_valid hτ
  have hdτ₁ : Mem.dom τ₁ = 𝓘.dom := 𝓘.dom_valid hτ₁
  have hdτ₂ : Mem.dom τ₂ = 𝓘.dom := 𝓘.dom_valid hτ₂
  have hdA : Disjoint σ₁.dom 𝓘.dom := by rw [← hdτ]; exact hd₁.symm
  have hdB : Disjoint σ₂.dom 𝓘.dom := by rw [← hdτ]; exact hd₂.symm
  set m : Mem := σ₁.union (σ₂.union τ) with hm
  have hdm : Mem.dom m = σ₁.dom ∪ σ₂.dom ∪ 𝓘.dom := by
    rw [hm, Mem.dom_union, Mem.dom_union, hdτ, Set.union_assoc]
  have hmI : Mem.restrict m 𝓘.dom = τ := by
    rw [hm, Mem.restrict_union_of_disjoint hdA, Mem.restrict_union_of_disjoint hdB,
      Mem.restrict_eq_self (le_of_eq hdτ)]
  have hi : 𝓘.prop (Mem.restrict m 𝓘.dom) := by rw [hmI]; exact hτ
  have hm1 : Mem.restrict m σ₁.dom = σ₁ := Mem.restrict_union_left rfl _
  have hm2 : Mem.restrict m σ₂.dom = σ₂ := by
    rw [hm, Mem.restrict_union_of_disjoint hd, Mem.restrict_union_left rfl]
  have hmW₁ : Mem.restrict m (σ₁.dom ∪ 𝓘.dom) = σ₁.union τ := by
    rw [← Mem.restrict_union_restrict, hm1, hmI]
  have hmW₂ : Mem.restrict m (σ₂.dom ∪ 𝓘.dom) = σ₂.union τ := by
    rw [← Mem.restrict_union_restrict, hm2, hmI]
  -- the two threads do not see which invariant state they are started in
  have hdomU : ∀ {ρ : Mem} {X : Set Var}, Mem.dom ρ = X → Disjoint X 𝓘.dom →
      ∀ {t : Mem}, Mem.dom t = 𝓘.dom → Mem.dom (ρ.union t) = X ∪ 𝓘.dom := by
    intro ρ X hρ _ t ht
    rw [Mem.dom_union, hρ, ht]
  have hresU : ∀ {ρ : Mem} {X : Set Var}, Mem.dom ρ = X →
      ∀ {t : Mem}, Mem.restrict (ρ.union t) X = ρ := by
    intro ρ X hρ t
    exact Mem.restrict_union_left hρ t
  have hresI : ∀ {ρ : Mem} {X : Set Var}, Mem.dom ρ = X → Disjoint X 𝓘.dom →
      ∀ {t : Mem}, Mem.dom t = 𝓘.dom → Mem.restrict (ρ.union t) 𝓘.dom = t := by
    intro ρ X hρ hdisj t ht
    rw [Mem.restrict_union_of_disjoint (by rw [hρ]; exact hdisj),
      Mem.restrict_eq_self (le_of_eq ht)]
  have hα : minProb (Lpofin.lin α (σ₁.union τ)) (Mem.sep A 𝓘.prop)
      = minProb (Lpofin.lin α (σ₁.union τ₁)) (Mem.sep A 𝓘.prop) := by
    refine lin_rec_indep hinv₁ hloc₁ hA hdA α.nodes_finset.card α.nodes_finset Form.true _ _
      le_rfl (fun y hy ↦ (Set.Finite.mem_toFinset _).mp hy)
      (hdomU rfl hdA hdτ) (hdomU rfl hdA hdτ₁) ?_ ?_ ?_
    · rw [hresU rfl, hresU rfl]
    · rw [hresI rfl hdA hdτ]; exact hτ
    · rw [hresI rfl hdA hdτ₁]; exact hτ₁
  have hβ : minProb (Lpofin.lin β (σ₂.union τ)) (Mem.sep B 𝓘.prop)
      = minProb (Lpofin.lin β (σ₂.union τ₂)) (Mem.sep B 𝓘.prop) := by
    refine lin_rec_indep hinv₂ hloc₂ hB hdB β.nodes_finset.card β.nodes_finset Form.true _ _
      le_rfl (fun y hy ↦ (Set.Finite.mem_toFinset _).mp hy)
      (hdomU rfl hdB hdτ) (hdomU rfl hdB hdτ₂) ?_ ?_ ?_
    · rw [hresU rfl, hresU rfl]
    · rw [hresI rfl hdB hdτ]; exact hτ
    · rw [hresI rfl hdB hdτ₂]; exact hτ₂
  have := lin_par_mul (hr₁ := hr₁) (hr₂ := hr₂) (hdn := hdn) (A := A) (B := B)
    hinv₁ hinv₂ hloc₁ hloc₂ hA hB hdA hdB hd hdm hi
  rw [hmW₁, hmW₂, hα, hβ] at this
  exact this

end Main

end Pcol
