import PcolIris.OProp.Laws

/-!
# Proof mode support for almost sure assertions

Instances that let the Iris proof mode move between `⌈P⌉ ∗ ⌈Q⌉` and `⌈P ∗ Q⌉`:

- `icombine h₁ h₂ as h` turns `h₁ : ⌈P⌉` and `h₂ : ⌈Q⌉` into `h : ⌈P ∗ Q⌉` (always sound,
  `OProp.sure_sep_intro`);
- intro and cases patterns destruct `⌈P ∗ Q⌉` into `⌈P⌉` and `⌈Q⌉` when both assertions have
  a known footprint (`OProp.sure_sep_elim`). Footprints are found by the type class
  `MProp.HasFootprint`, which covers ownership of variables, equations between variables and
  literals, and separating conjunctions and conjunctions of those.
-/

namespace Pcol

namespace MProp

/-- The assertion `P` has footprint `V` (see `MProp.Footprint`). -/
class HasFootprint (P : MProp) (V : outParam (Set Var)) : Prop where
  footprint : P.Footprint V

instance : HasFootprint (Iris.BI.BIBase.emp : MProp) ∅ := ⟨Footprint.emp⟩

instance (x : Var) (v : Val) : HasFootprint ($ x == Expr.literal v) {x} :=
  ⟨Footprint.var_equals_literal x v⟩

instance (x : Var) : HasFootprint (own ($ x)) {x} := ⟨Footprint.own_var x⟩

instance {P Q : MProp} {V W : Set Var} [hP : HasFootprint P V] [hQ : HasFootprint Q W] :
    HasFootprint iprop(P ∗ Q) (V ∪ W) :=
  ⟨hP.footprint.sep hQ.footprint⟩

instance {P Q : MProp} {V W : Set Var} [hP : HasFootprint P V] [hQ : HasFootprint Q W] :
    HasFootprint iprop(P ∧ Q) (V ∪ W) :=
  ⟨hP.footprint.and hQ.footprint⟩

end MProp

namespace OProp

open Iris.ProofMode in
instance {P Q : MProp} : CombineSepAs (⌈P⌉ : OProp) ⌈Q⌉ ⌈iprop(P ∗ Q)⌉ := ⟨sure_sep_intro⟩

open Iris.ProofMode in
instance {P Q : MProp} {V W : Set Var} [hP : MProp.HasFootprint P V]
    [hQ : MProp.HasFootprint Q W] : IntoSep (⌈iprop(P ∗ Q)⌉ : OProp) ⌈P⌉ ⌈Q⌉ :=
  ⟨sure_sep_elim hP.footprint hQ.footprint⟩

end OProp

end Pcol
