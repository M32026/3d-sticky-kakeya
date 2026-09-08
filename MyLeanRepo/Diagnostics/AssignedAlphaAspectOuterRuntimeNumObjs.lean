import MyLeanRepo.Diagnostics.NumObjs
import MyLeanRepo.Kakeya.Streamlined.BalancedKatzTao.MainLemmaTwo.AssignedAlphaAspectOuterRuntime

open Lean Elab Command

run_cmd MyLeanRepo.Diagnostics.reportNumObjs #[
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.FixedOuterData,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.fixedOuterData_exists,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.SnapshotRun,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.SnapshotConclusion,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.SnapshotRun.exists_conclusion,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.Prepared,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.Runtime,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.run,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.Conclusion,
  `Kakeya.Streamlined.AssignedAlphaAspectOuterRuntime.exists_conclusion
]
