/-
Lists the declarations of this project that use `sorry` directly (as opposed to depending on
another declaration that does).  Run with `lake env lean scripts/Sorries.lean`.
-/
import PcolIris

open Lean Elab Command

elab "#list_sorries" : command => do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if !(`PcolIris).isPrefixOf mod then continue
    if n.isInternal then continue
    if ci.getUsedConstantsAsSet.contains ``sorryAx then out := out.push n
  let sorted := out.qsort (·.toString < ·.toString)
  logInfo m!"{sorted.size} declarations use sorry directly:\n{sorted.toList}"

#list_sorries
