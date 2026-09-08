import MyLeanRepo.Diagnostics.NumObjs
import MyLeanRepo.Kakeya.Streamlined.MainLemmaTwo.PreterminalPhysicalBMDFMappedFullGridProvenance

open Lean Elab Command

run_cmd MyLeanRepo.Diagnostics.reportNumObjs #[
  `Kakeya.Streamlined.PreterminalPhysicalBMDFMappedFullGridProvenance.vnsProvenance,
  `Kakeya.Streamlined.preterminalPhysicalBMDFMappedVNSIntoFullGrid_scale,
  `Kakeya.Streamlined.preterminalPhysicalBMDFMappedFullGridProvenance
]
