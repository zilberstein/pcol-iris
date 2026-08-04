import PcolIris.Semantics.Linearization

namespace Pcol

open Linearization

instance : Sem Act Mem (ConvexPowerset Mem) where
  sem a σ := match a with
  | Act.assign x e =>
    match e σ with
    | some v => pure <| σ.extend x v
    | none => ⊥
  | Act.samp x d =>
    match d σ with
    | some μ => (ConvexPowerset.singleton μ) >>= fun v ↦ pure (σ.extend x v)
    | none => ⊥
  sem_mono _ _ hle := by subst hle; rfl

namespace Inv

open Classical in
noncomputable def check (𝓘 : Inv) (σ : Mem) : ConvexPowerset Mem :=
  if 𝓘.prop (σ.restrict 𝓘.dom) then pure σ else ⊥

open Classical in
noncomputable def replace (𝓘 : Inv) (σ : Mem) : ConvexPowerset Mem :=
  Nondet.nondet fun τ : 𝓘.prop_finite.toFinset ↦
    pure fun x ↦ if x ∈ 𝓘.dom then τ.val x else σ x

end Inv

@[reducible]
noncomputable def sem_act_with_inv (𝓘 : Inv) : Sem Act Mem (ConvexPowerset Mem) where
  sem a σ := do
    let σ ← 𝓘.check σ
    let σ ← 𝓘.replace σ
    let τ ← Sem.sem a σ
    𝓘.check τ
  sem_mono _ _ hle := by subst hle; rfl

instance : Sem Test Mem (ConvexPowerset Bool) where
  sem b σ := match b with
  | Test.lift e =>
    match e σ with
    | some q => pure <| decide (q ≠ 0)
    | none => ⊥
  | Test.nd => ConvexPowerset.nondet pure
  | Test.prob e =>
    match e σ with
    | some p =>
      ConvexPowerset.bernoulli (p := min 1 (Real.toNNReal p)) Std.min_le_left
        (pure Bool.true)
        (pure Bool.false)
    | none => ⊥
  sem_mono _ _ hle := by subst hle; rfl

namespace Cmd

noncomputable def to_pom (c : Cmd) : Pom (Label Act Test) :=
  match c with
  | skip => Pom.Semantics.skip
  | seq c₁ c₂ => c₁.to_pom.seq c₂.to_pom
  | if_stmt e c₁ c₂ => Pom.Semantics.if_stmt (Test.lift e) c₁.to_pom c₂.to_pom
  | prob e c₁ c₂ => Pom.Semantics.if_stmt (Test.prob e) c₁.to_pom c₂.to_pom
  | nd c₁ c₂ => Pom.Semantics.if_stmt Test.nd c₁.to_pom c₂.to_pom
  | par c₁ c₂ => Pom.Semantics.par c₁.to_pom c₂.to_pom
  | while_loop e c => Pom.Semantics.while_loop (Test.lift e) c.to_pom
  | act a => Pom.singleton (Label.act a)

end Cmd

end Pcol
