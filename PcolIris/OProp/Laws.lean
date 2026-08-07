import PcolIris.OProp.OProp

namespace Pcol
namespace OProp

lemma sure_weaken {P Q : MProp} (h : P ⊢ Q) : ⌈P⌉ ⊢ ⌈Q⌉ := by
  intro 𝓟 hP i hi; apply Set.mem_preimage.mpr
  exact hP hi |> Set.mem_preimage.mp |> h _

lemma sure_sep {P Q : MProp} :
    ⌈ iprop(P ∗ Q) ⌉ ⊣⊢ ⌈P⌉ ∗ ⌈Q⌉ := by
  constructor
  · intro 𝓟 hsure; sorry
  · intro 𝓟 ⟨𝓟₁, 𝓟₂, hdisj, hle, hP, hQ⟩ k hk
    sorry

lemma oplus_distrib (ξ : PMF Val) (φ : Val → OProp) (ψ : OProp) :
    (⨁[ ξ ] φ) ∗ ψ ⊢ ⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ) := sorry

lemma oplus_distrib' (ξ : PMF Val) (φ : Val → OProp) (ψ : OProp) (h : ψ.Precise) :
    (⨁[ ξ ] fun v ↦ iprop(φ v ∗ ψ)) ⊢ (⨁[ ξ ] φ) ∗ ψ := by
  sorry

end OProp
end Pcol
