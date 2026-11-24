import Lean
import RH.Statement

/-!
Lists everything `RH.RiemannHypothesis` depends on. Run it from the project root with

    lake build RH.Statement && lake env lean scripts/Audit.lean
-/

open Lean

/-- All constants reachable from the given ones, through types, values and constructors. -/
partial def reachable (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reachable env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => reachable env rest seen
    | some ci =>
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      let ctors := match ci with
        | .inductInfo v => v.ctors
        | _ => []
      reachable env (used.toList ++ ctors ++ rest) seen

#print axioms RH.RiemannHypothesis

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let all := (reachable env [`RH.RiemannHypothesis] {}).toList
  let outside := all.filter (fun n => !(`RH).isPrefixOf n)
  let classes := all.filter (fun n => isClass env n)
  logInfo m!"constants outside this file ({outside.length}): {outside.map toString |>.mergeSort}"
  logInfo m!"type classes: {classes}"
