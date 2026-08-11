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

lemma oplus_weaken {ξ : PMF Val} {φ ψ : Val → OProp} (h : ∀ v ∈ ξ.support, φ v ⊢ ψ v) :
    (⨁[ξ] φ) ⊢ ⨁[ξ] ψ := by
  intro 𝓟 ⟨𝓠, V, hdsj, hdom, hsum, hφ⟩
  refine ⟨𝓠, V, hdsj, hdom, hsum, ?_⟩
  intro v hv; exact h v hv (𝓠 v) <| hφ v hv

end OProp

namespace Precise

lemma sure (P : MProp) : (OProp.sure P).Precise := sorry

lemma sep {φ ψ : OProp} (hφ : φ.Precise) (hψ : ψ.Precise) : iprop(φ ∗ ψ).Precise := by sorry

lemma oplus {ξ : PMF Val} {φ : Val → OProp} (h : ∀ v ∈ ξ.support, (φ v).Precise) :
    (⨁[ξ] φ).Precise := by sorry

end Precise

end Pcol
