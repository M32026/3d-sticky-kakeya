import Lean.Elab.Command
import Lean.Util.NumObjs

/-!
# Proof-term size diagnostics

Import this module in a slow Lean source file and pass the declarations to
inspect to `reportNumObjs`.
-/

namespace MyLeanRepo.Diagnostics

open Lean Elab Command

/-- Report expression DAG size and fully expanded size for the requested
declarations. -/
def reportNumObjs (names : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for name in names do
    let some info := env.find? name
      | throwError "missing declaration {name}"
    let typeObjs ← info.type.numObjs
    match info.value? (allowOpaque := true) with
    | none =>
        logInfo m!"{name}: typeObjs={typeObjs}, no value"
    | some value =>
        let valueObjs ← value.numObjs
        logInfo m!"{name}: typeObjs={typeObjs}, valueObjs={valueObjs}, extend={value.sizeWithoutSharing}"

end MyLeanRepo.Diagnostics
