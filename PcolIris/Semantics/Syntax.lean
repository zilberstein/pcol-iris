import PcolIris.Semantics.Mem

namespace Pcol

namespace Expr

def literal (v : ℚ) : Expr := fun _ ↦ v
def var (x : Var) : Expr := fun σ ↦ σ x

end Expr

inductive Act : Type where
| assign : Var →  Expr → Act
| samp : Var → PExpr → Act

inductive Cmd : Type where
| skip : Cmd
| seq : Cmd → Cmd → Cmd
| if_stmt : Expr → Cmd → Cmd → Cmd
| prob : Expr → Cmd → Cmd → Cmd
| nd : Cmd → Cmd → Cmd
| par : Cmd → Cmd → Cmd
| while_loop : Expr → Cmd → Cmd
| act : Act → Cmd

end Pcol
