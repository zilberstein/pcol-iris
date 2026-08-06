/-
Structural facts about the parallel composition `Lpofin.par` of two labelled partial orders,
and about the scheduling relation `Lpofin.next` on it.

The main results are `Lpofin.next_par` and `Lpofin.filter_by_outcome_par`, which say that a
schedule of `α ∥ β` is exactly an interleaving of a schedule of `α` with a schedule of `β`.
-/
import Pom.Semantics

import PcolIris.Logic.MemUnion
import PcolIris.Logic.MinProbLemmas
import PcolIris.Semantics.Invariant

namespace Lpo

open Pcol

def HasInv {act test : Type} (α : Lpo (Label (WithInv act) test)) (𝓘 : Inv) : Prop :=
  ∀ x ∈ α.nodes, match α.lab x with
  | Label.act a => a.inv = 𝓘
  | _ => true

end Lpo

namespace Lpofin

open Pcol

variable {act test : Type}

noncomputable def par {x : Node} {α β : Lpofin (Label act test)}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes) :
    Lpofin (Label act test) :=
  ⟨Lpo.par hx hx' hd Label.fork_ne_bot,
    Set.finite_insert.mpr (Set.finite_union.mpr ⟨α.property, β.property⟩)⟩

def HasInv (α : Lpofin (Label (WithInv act) test)) (𝓘 : Inv) : Prop :=
  α.val.HasInv 𝓘

end Lpofin

namespace Pom

open Pcol

variable {act test : Type}

def HasInv (p : Pom (Label (WithInv act) test)) (𝓘 : Inv) : Prop :=
  ∀ α ∈ p, α.HasInv 𝓘

namespace HasInv

lemma to_lpo_trunc {p : Pom (Label (WithInv act) test)} {α : Lpo (Label (WithInv act) test)}
    {𝓘 : Inv} (h : p.HasInv 𝓘) (hmem : α ∈ p) {n : ℕ} :
    (α.trunc n).HasInv 𝓘 := by
  intro x ⟨hx, _⟩; by_cases hlev : α.rel.lev x < n
  · conv => arg 2; exact if_pos hlev
    exact h α hmem x hx
  · conv => arg 2; exact if_neg hlev

lemma of_withInv (c : Cmd act) (𝓘 : Inv) : (c.withInv 𝓘).to_pom.HasInv 𝓘 := by
  sorry

end HasInv

end Pom

namespace Form

variable {γ : Type}

/-- `p ≤ χ` says exactly that `p ∧ ¬χ` is unsatisfiable. -/
lemma le_iff_not_sat {p χ : Form γ} : p ≤ χ ↔ ¬ (p.and χ.not).sat := by
  constructor
  · rintro h ⟨v, hv, hn⟩
    exact hn (h v hv)
  · intro h v hv
    by_contra hn
    exact h ⟨v, hv, hn⟩

/-- Conjoining a satisfiable formula that depends on disjoint variables does not change which
formulae are entailed, as long as the conclusion also depends on the original variables. -/
lemma le_and_indep {p q χ : Form γ} {S T : Set γ}
    (hp : p.DependsOn S) (hq : q.DependsOn T) (hχ : χ.DependsOn S)
    (hd : Disjoint S T) (hqsat : q.sat) :
    (p.and q ≤ χ) ↔ (p ≤ χ) := by
  have hpχ : (p.and χ.not).DependsOn S := by
    have := DependsOn.and hp (DependsOn.not hχ)
    rwa [Set.union_self] at this
  have hkey : Form.sat ((p.and χ.not).and q) ↔ Form.sat (p.and χ.not) :=
    sat_and_indep hpχ hq hd hqsat
  rw [le_iff_not_sat, le_iff_not_sat, ← hkey]
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨v, ⟨hp', hq'⟩, hn⟩; exact ⟨v, ⟨hp', hn⟩, hq'⟩
  · rintro ⟨v, ⟨hp', hn⟩, hq'⟩; exact ⟨v, ⟨hp', hq'⟩, hn⟩

/-- A literal, or its negation, is always satisfiable. -/
lemma sat_literal_cond (x : γ) (b : Bool) :
    Form.sat (bif b then Form.literal x else (Form.literal x).not) := by
  cases b with
  | true => exact ⟨{x}, rfl⟩
  | false => exact ⟨∅, fun h ↦ h⟩

lemma dependsOn_literal_cond (x : γ) (b : Bool) :
    Form.DependsOn (bif b then Form.literal x else (Form.literal x).not) {x} := by
  cases b with
  | true => exact DependsOn.literal
  | false => exact DependsOn.not DependsOn.literal

/-- The test-outcome literal used by `Lpofin.lin_node`, in its `ite` form, is satisfiable. -/
lemma sat_ite_literal (x : γ) (b : Bool) :
    Form.sat (if b then Form.literal x else (Form.literal x).not) := by
  cases b
  · exact ⟨∅, fun h ↦ h⟩
  · exact ⟨{x}, rfl⟩

lemma dependsOn_ite_literal (x : γ) (b : Bool) :
    Form.DependsOn (if b then Form.literal x else (Form.literal x).not) {x} := by
  cases b
  · exact DependsOn.not DependsOn.literal
  · exact DependsOn.literal

/-- Conjoining a satisfiable formula on disjoint variables preserves satisfiability. -/
lemma sat_and_of_disjoint {p q : Form γ} {S T : Set γ}
    (hp : p.DependsOn S) (hq : q.DependsOn T) (hd : Disjoint S T)
    (hpsat : p.sat) (hqsat : q.sat) : (p.and q).sat :=
  (sat_and_indep hp hq hd hqsat).mpr hpsat

end Form

namespace Lpofin

open Linearization

section ParAccessors

variable {act test : Type} {x : Node} {α β : Lpofin (Label act test)}
  (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes)

lemma par_nodes : (Lpofin.par hx hx' hd).nodes = insert x (α.nodes ∪ β.nodes) := rfl

lemma par_rel (y z : Node) :
    (Lpofin.par hx hx' hd).rel y z ↔
      (x = y ∧ z ∈ α.nodes ∪ β.nodes) ∨ α.rel y z ∨ β.rel y z := Iff.rfl

open Classical in
lemma par_lab (y : Node) :
    (Lpofin.par hx hx' hd).lab y =
      if x = y then Label.fork else if y ∈ α.nodes then α.lab y else β.lab y := rfl

lemma par_form (y : Node) (v : Set Node) :
    (Lpofin.par hx hx' hd).form y v ↔
      (x = y) ∨ (y ∈ α.nodes ∧ (α.form y).and Form.true v) ∨
        (y ∈ β.nodes ∧ (β.form y).and Form.true v) := Iff.rfl

include hx hx' hd

lemma par_lab_left {y : Node} (hy : y ∈ α.nodes) :
    (Lpofin.par hx hx' hd).lab y = α.lab y := by
  classical
  rw [par_lab, if_neg (fun h ↦ hx (by rw [h]; exact hy)), if_pos hy]

lemma par_lab_right {y : Node} (hy : y ∈ β.nodes) :
    (Lpofin.par hx hx' hd).lab y = β.lab y := by
  classical
  rw [par_lab, if_neg (fun h ↦ hx' (by rw [h]; exact hy)), if_neg (Set.disjoint_right.mp hd hy)]

lemma par_form_left {y : Node} (hy : y ∈ α.nodes) :
    (Lpofin.par hx hx' hd).form y = α.form y := by
  funext v
  refine propext ?_
  rw [par_form]
  constructor
  · rintro (h | ⟨-, h, -⟩ | ⟨h, -⟩)
    · exact absurd (show x ∈ α.nodes by rw [h]; exact hy) hx
    · exact h
    · exact absurd h (Set.disjoint_left.mp hd hy)
  · intro h
    exact Or.inr (Or.inl ⟨hy, h, trivial⟩)

lemma par_form_right {y : Node} (hy : y ∈ β.nodes) :
    (Lpofin.par hx hx' hd).form y = β.form y := by
  funext v
  refine propext ?_
  rw [par_form]
  constructor
  · rintro (h | ⟨h, -⟩ | ⟨-, h, -⟩)
    · exact absurd (show x ∈ β.nodes by rw [h]; exact hy) hx'
    · exact absurd h (Set.disjoint_right.mp hd hy)
    · exact h
  · intro h
    exact Or.inr (Or.inr ⟨hy, h, trivial⟩)

lemma par_rel_left {y z : Node} (hy : y ∈ α.nodes) :
    (Lpofin.par hx hx' hd).rel z y ↔ (z = x ∨ α.rel z y) := by
  rw [par_rel]
  constructor
  · rintro (⟨h, -⟩ | h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
    · exact absurd (β.val.property.rel_dom h).2 (Set.disjoint_left.mp hd hy)
  · rintro (rfl | h)
    · exact Or.inl ⟨rfl, Or.inl hy⟩
    · exact Or.inr (Or.inl h)

lemma par_rel_right {y z : Node} (hy : y ∈ β.nodes) :
    (Lpofin.par hx hx' hd).rel z y ↔ (z = x ∨ β.rel z y) := by
  rw [par_rel]
  constructor
  · rintro (⟨h, -⟩ | h | h)
    · exact Or.inl h.symm
    · exact absurd (α.val.property.rel_dom h).2 (Set.disjoint_right.mp hd hy)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl ⟨rfl, Or.inr hy⟩
    · exact Or.inr (Or.inr h)

lemma par_nodes_finset :
    (Lpofin.par hx hx' hd).nodes_finset =
      insert x (α.nodes_finset ∪ β.nodes_finset) := by
  ext y
  simp only [Lpofin.nodes_finset, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_union]
  exact Iff.rfl

end ParAccessors

open Classical in
/-- Membership in the set of schedulable nodes. -/
lemma mem_next_iff {l : Type} [Bot l] (a : Lpofin l) (s : Finset Node) (φ : Form Node)
    (y : Node) :
    y ∈ Lpofin.next a s φ ↔
      y ∈ a.nodes ∧ y ∈ s ∧ φ ≤ a.form y ∧ ∀ z, a.rel z y → z ∉ s := by
  rw [Lpofin.next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset]
  exact and_congr_right fun _ ↦ Iff.rfl

/-- The formula attached to a node depends only on the nodes of the pomset. -/
lemma form_dependsOn_nodes {l : Type} [Bot l] (a : Lpofin l) {y : Node} (hy : y ∈ a.nodes) :
    (a.form y).DependsOn a.nodes := by
  refine Form.DependsOn.monotone _ ?_ (a.val.property.form y hy).1
  intro z hz
  exact (a.val.property.rel_dom hz).1

section Interleaving

variable {act test : Type} {r : Node} {α β : Lpofin (Label act test)}
  {hr₁ : r ∉ α.nodes} {hr₂ : r ∉ β.nodes} {hdn : Disjoint α.nodes β.nodes}
  {s₁ s₂ : Finset Node} {φ₁ φ₂ : Form Node}

/-- **Interleaving.**  A node is schedulable in `α ∥ β` (after the fork node has been run)
exactly when it is schedulable in the thread it belongs to. -/
theorem next_par
    (hs₁ : ∀ y ∈ s₁, y ∈ α.nodes) (hs₂ : ∀ y ∈ s₂, y ∈ β.nodes)
    (hdep₁ : φ₁.DependsOn α.nodes) (hdep₂ : φ₂.DependsOn β.nodes)
    (hsat₁ : φ₁.sat) (hsat₂ : φ₂.sat) :
    Lpofin.next (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) (φ₁.and φ₂) =
      Lpofin.next α s₁ φ₁ ∪ Lpofin.next β s₂ φ₂ := by
  classical
  have hr₁s : r ∉ s₁ := fun h ↦ hr₁ (hs₁ r h)
  have hr₂s : r ∉ s₂ := fun h ↦ hr₂ (hs₂ r h)
  ext y
  rw [Finset.mem_union, mem_next_iff, mem_next_iff, mem_next_iff]
  constructor
  · rintro ⟨hyn, hys, hyf, hyr⟩
    rcases Finset.mem_union.mp hys with hy₁ | hy₂
    · have hyα : y ∈ α.nodes := hs₁ y hy₁
      refine Or.inl ⟨hyα, hy₁, ?_, ?_⟩
      · rw [par_form_left hr₁ hr₂ hdn hyα] at hyf
        exact (Form.le_and_indep hdep₁ hdep₂ (form_dependsOn_nodes α hyα) hdn hsat₂).mp hyf
      · intro z hz hzs
        exact hyr z ((par_rel_left hr₁ hr₂ hdn hyα).mpr (Or.inr hz))
          (Finset.mem_union_left _ hzs)
    · have hyβ : y ∈ β.nodes := hs₂ y hy₂
      refine Or.inr ⟨hyβ, hy₂, ?_, ?_⟩
      · rw [par_form_right hr₁ hr₂ hdn hyβ] at hyf
        rw [Form.and_comm] at hyf
        exact (Form.le_and_indep hdep₂ hdep₁ (form_dependsOn_nodes β hyβ) hdn.symm hsat₁).mp hyf
      · intro z hz hzs
        exact hyr z ((par_rel_right hr₁ hr₂ hdn hyβ).mpr (Or.inr hz))
          (Finset.mem_union_right _ hzs)
  · rintro (⟨hyα, hy₁, hyf, hyr⟩ | ⟨hyβ, hy₂, hyf, hyr⟩)
    · refine ⟨?_, Finset.mem_union_left _ hy₁, ?_, ?_⟩
      · rw [par_nodes]
        exact Set.mem_insert_of_mem _ (Or.inl hyα)
      · rw [par_form_left hr₁ hr₂ hdn hyα]
        exact (Form.le_and_indep hdep₁ hdep₂ (form_dependsOn_nodes α hyα) hdn hsat₂).mpr hyf
      · intro z hz
        rcases (par_rel_left hr₁ hr₂ hdn hyα).mp hz with rfl | hz'
        · exact fun hc ↦ (Finset.mem_union.mp hc).elim hr₁s hr₂s
        · refine fun hc ↦ (Finset.mem_union.mp hc).elim (hyr z hz') ?_
          intro hz₂
          exact Set.disjoint_left.mp hdn (α.val.property.rel_dom hz').1 (hs₂ z hz₂)
    · refine ⟨?_, Finset.mem_union_right _ hy₂, ?_, ?_⟩
      · rw [par_nodes]
        exact Set.mem_insert_of_mem _ (Or.inr hyβ)
      · rw [par_form_right hr₁ hr₂ hdn hyβ, Form.and_comm]
        exact (Form.le_and_indep hdep₂ hdep₁ (form_dependsOn_nodes β hyβ) hdn.symm hsat₁).mpr hyf
      · intro z hz
        rcases (par_rel_right hr₁ hr₂ hdn hyβ).mp hz with rfl | hz'
        · exact fun hc ↦ (Finset.mem_union.mp hc).elim hr₁s hr₂s
        · refine fun hc ↦ (Finset.mem_union.mp hc).elim ?_ (hyr z hz')
          intro hz₁
          exact Set.disjoint_left.mp hdn (hs₁ z hz₁) (β.val.property.rel_dom hz').1

open Classical in
lemma mem_filter_by_outcome_iff {l : Type} [Bot l] (a : Lpofin l) (s : Finset Node) (x z : Node)
    (b : Bool) :
    z ∈ Lpofin.filter_by_outcome a s x b ↔
      z ∈ s.erase x ∧
        Form.sat ((a.form z).and (bif b then Form.literal x else (Form.literal x).not)) := by
  rw [Lpofin.filter_by_outcome, Finset.mem_filter]

/-- Filtering the remaining nodes after a test of the left thread only affects that thread. -/
theorem filter_by_outcome_par_left {x : Node} (b : Bool)
    (hs₁ : ∀ y ∈ s₁, y ∈ α.nodes) (hs₂ : ∀ y ∈ s₂, y ∈ β.nodes) (hx : x ∈ α.nodes) :
    Lpofin.filter_by_outcome (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) x b =
      Lpofin.filter_by_outcome α s₁ x b ∪ s₂ := by
  classical
  have hxs₂ : x ∉ s₂ := fun h ↦ Set.disjoint_left.mp hdn hx (hs₂ x h)
  have hlit : Form.DependsOn (bif b then Form.literal x else (Form.literal x).not) {x} :=
    Form.dependsOn_literal_cond x b
  have hlitsat : Form.sat (bif b then Form.literal x else (Form.literal x).not) :=
    Form.sat_literal_cond x b
  ext z
  rw [mem_filter_by_outcome_iff, Finset.mem_union, mem_filter_by_outcome_iff,
    Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxs₂, Finset.mem_union]
  constructor
  · rintro ⟨hz, hsat⟩
    rcases hz with hz₁ | hz₂
    · refine Or.inl ⟨hz₁, ?_⟩
      rwa [par_form_left hr₁ hr₂ hdn (hs₁ z (Finset.mem_of_mem_erase hz₁))] at hsat
    · exact Or.inr hz₂
  · rintro (⟨hz₁, hsat⟩ | hz₂)
    · refine ⟨Or.inl hz₁, ?_⟩
      rwa [par_form_left hr₁ hr₂ hdn (hs₁ z (Finset.mem_of_mem_erase hz₁))]
    · have hzβ : z ∈ β.nodes := hs₂ z hz₂
      refine ⟨Or.inr hz₂, ?_⟩
      rw [par_form_right hr₁ hr₂ hdn hzβ]
      refine Form.sat_and_of_disjoint (form_dependsOn_nodes β hzβ) hlit ?_
        ((β.val.property.form_dom z).mpr hzβ) hlitsat
      exact Set.disjoint_singleton_right.mpr (Set.disjoint_left.mp hdn hx)

/-- Filtering the remaining nodes after a test of the right thread only affects that thread. -/
theorem filter_by_outcome_par_right {x : Node} (b : Bool)
    (hs₁ : ∀ y ∈ s₁, y ∈ α.nodes) (hs₂ : ∀ y ∈ s₂, y ∈ β.nodes) (hx : x ∈ β.nodes) :
    Lpofin.filter_by_outcome (Lpofin.par hr₁ hr₂ hdn) (s₁ ∪ s₂) x b =
      s₁ ∪ Lpofin.filter_by_outcome β s₂ x b := by
  classical
  have hxs₁ : x ∉ s₁ := fun h ↦ Set.disjoint_left.mp hdn (hs₁ x h) hx
  have hlit : Form.DependsOn (bif b then Form.literal x else (Form.literal x).not) {x} :=
    Form.dependsOn_literal_cond x b
  have hlitsat : Form.sat (bif b then Form.literal x else (Form.literal x).not) :=
    Form.sat_literal_cond x b
  ext z
  rw [mem_filter_by_outcome_iff, Finset.mem_union, mem_filter_by_outcome_iff,
    Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxs₁, Finset.mem_union]
  constructor
  · rintro ⟨hz, hsat⟩
    rcases hz with hz₁ | hz₂
    · exact Or.inl hz₁
    · refine Or.inr ⟨hz₂, ?_⟩
      rwa [par_form_right hr₁ hr₂ hdn (hs₂ z (Finset.mem_of_mem_erase hz₂))] at hsat
  · rintro (hz₁ | ⟨hz₂, hsat⟩)
    · have hzα : z ∈ α.nodes := hs₁ z hz₁
      refine ⟨Or.inl hz₁, ?_⟩
      rw [par_form_left hr₁ hr₂ hdn hzα]
      refine Form.sat_and_of_disjoint (form_dependsOn_nodes α hzα) hlit ?_
        ((α.val.property.form_dom z).mpr hzα) hlitsat
      exact Set.disjoint_singleton_right.mpr (Set.disjoint_right.mp hdn hx)
    · refine ⟨Or.inr hz₂, ?_⟩
      rwa [par_form_right hr₁ hr₂ hdn (hs₂ z (Finset.mem_of_mem_erase hz₂))]

/-- Initially only the fork node of `α ∥ β` is schedulable. -/
theorem next_par_root :
    Lpofin.next (Lpofin.par hr₁ hr₂ hdn) (Lpofin.par hr₁ hr₂ hdn).nodes_finset Form.true
      = {r} := by
  classical
  have hrn : r ∈ (Lpofin.par hr₁ hr₂ hdn).nodes := by
    rw [par_nodes]; exact Set.mem_insert _ _
  have hrf : r ∈ (Lpofin.par hr₁ hr₂ hdn).nodes_finset :=
    (Set.Finite.mem_toFinset _).mpr hrn
  have hnorel : ∀ z, ¬ (Lpofin.par hr₁ hr₂ hdn).rel z r := by
    intro z hz
    rcases (par_rel hr₁ hr₂ hdn z r).mp hz with ⟨-, h⟩ | h | h
    · exact h.elim hr₁ hr₂
    · exact hr₁ (α.val.property.rel_dom h).2
    · exact hr₂ (β.val.property.rel_dom h).2
  ext y
  rw [mem_next_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hyn, -, -, hyr⟩
    rw [par_nodes] at hyn
    rcases hyn with h | h
    · exact h
    · exact absurd hrf (hyr r ((par_rel hr₁ hr₂ hdn r y).mpr (Or.inl ⟨rfl, h⟩)))
  · rintro rfl
    exact ⟨hrn, hrf, fun v _ ↦ (par_form hr₁ hr₂ hdn _ v).mpr (Or.inl rfl),
      fun z hz ↦ absurd hz (hnorel z)⟩

/-- After the fork node has been scheduled, the remaining nodes of `α ∥ β` are exactly the
nodes of the two threads. -/
theorem par_nodes_finset_erase_root :
    (Lpofin.par hr₁ hr₂ hdn).nodes_finset.erase r = α.nodes_finset ∪ β.nodes_finset := by
  classical
  rw [par_nodes_finset, Finset.erase_insert]
  intro hc
  rcases Finset.mem_union.mp hc with h | h
  · exact hr₁ ((Set.Finite.mem_toFinset _).mp h)
  · exact hr₂ ((Set.Finite.mem_toFinset _).mp h)

lemma par_lab_root : (Lpofin.par hr₁ hr₂ hdn).lab r = Label.fork := by
  classical
  rw [par_lab, if_pos rfl]

end Interleaving

end Lpofin
