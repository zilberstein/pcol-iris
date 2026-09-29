/-
Algebraic laws of the product of probability spaces.
-/
import PcolIris.OProp.SumProd

namespace Pcol

namespace ProbSpace

/-- The product of probability spaces is monotone in its left argument.  Since the memory of
a product is a left-biased union, the variables gained by the left factor must not clash with
the right factor. -/
lemma product_mono_left {p p' q : ProbSpace} (h : p ≤ p') (hd : Disjoint p'.dom q.dom) :
    (p ⊗ q) ≤ (p' ⊗ q) := by
  sorry

/-- The product of probability spaces is monotone in its right argument. -/
lemma product_mono_right {p q q' : ProbSpace} (h : q ≤ q') (hd : Disjoint p.dom q.dom) :
    (p ⊗ q) ≤ (p ⊗ q') := by
  sorry

end ProbSpace

end Pcol
