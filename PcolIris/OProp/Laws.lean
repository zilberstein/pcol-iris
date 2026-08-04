import PcolIris.OProp.OProp

namespace Pcol
namespace OProp

lemma oplus_distrib (ξ : PMF Val) (φ : Val → OProp) (ψ : OProp) :
    (⨁[ ξ ] φ) ∗ ψ ⊢ ⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ) := sorry

lemma oplus_distrib' (ξ : PMF Val) (φ : Val → OProp) (ψ : OProp) (h : ψ.Precise) :
    (⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ)) ⊢ (⨁[ ξ ] φ) ∗ ψ := by
  sorry

end OProp
end Pcol
