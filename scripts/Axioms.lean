/-
Prints the axioms used by the main results, so that it is visible which of them still depend
on `sorryAx`.  Run with `lake env lean scripts/Axioms.lean`.
-/
import PcolIris

open Pcol

#print axioms ProbSpace.product_assoc
#print axioms ProbSpace.product_comm
#print axioms ProbSpace.product_mono
#print axioms Pom.par_comp
#print axioms lemma_C6
#print axioms wp_seq
#print axioms wp_par
#print axioms wp_frame
#print axioms wp_split
