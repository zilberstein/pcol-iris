import PcolIris.Semantics.Mem

namespace Pcol

namespace Expr

def literal (v : ℚ) : Expr := fun _ ↦ v
def var (x : Var) : Expr := fun σ ↦ σ x

end Expr

inductive Act : Type where
| assign : Var →  Expr → Act
| samp : Var → PExpr → Act

inductive Cmd (act : Type) : Type where
| skip : Cmd act
| seq : Cmd act → Cmd act → Cmd act
| if_stmt : Expr → Cmd act → Cmd act → Cmd act
| prob : Expr → Cmd act → Cmd act → Cmd act
| nd : Cmd act → Cmd act → Cmd act
| par : Cmd act → Cmd act → Cmd act
| while_loop : Expr → Cmd act → Cmd act
| act : act → Cmd act

infixr:10 " ⨟ " => Cmd.seq
infixr:60 " ::= " => fun x e ↦ Cmd.act (Act.assign x e)
infixr:60  " :≈ " => fun x d ↦ Cmd.act (Act.samp x d)
notation:35 "if( " e " ){ " c₁ " }else{ " c₂ "}" => Cmd.if_stmt e c₁ c₂
notation:35 "if( " e " ){ " c " }" => Cmd.if_stmt e c Cmd.skip
notation:30 "while( " e " ){ " c "}" => Cmd.while_loop e c
notation:50 c₁ " ⊕[ " e " ] " c₂ => Cmd.prob e c₁ c₂
infixl:50 " & " => Cmd.nd
prefix:70 "$" => Expr.var

/-- Type class instances to give nice syntax to arithmetic and numbers -/
instance {n : Nat} : OfNat Expr n where ofNat := Expr.literal n
instance : OfScientific Expr where ofScientific x b y :=
  Expr.literal <| OfScientific.ofScientific x b y
instance : HAdd Expr Expr Expr where hAdd e₁ e₂ σ := HAdd.hAdd <$> e₁ σ <*> e₂ σ
instance : HSub Expr Expr Expr where hSub e₁ e₂ σ := HSub.hSub <$> e₁ σ <*> e₂ σ
instance : HMul Expr Expr Expr where hMul e₁ e₂ σ := HMul.hMul <$> e₁ σ <*> e₂ σ
instance : HDiv Expr Expr Expr where hDiv e₁ e₂ σ := HDiv.hDiv <$> e₁ σ <*> e₂ σ

def Bern (e : Expr) : PExpr := sorry

def example_prog : Cmd Act :=
  "x" ::= 0 ⨟
  "i" ::= 0 ⨟
  while( $"b" ){
    "x" :≈ Bern 0.5 ⨟
    "i" ::= $"i" + 1
  }


end Pcol
