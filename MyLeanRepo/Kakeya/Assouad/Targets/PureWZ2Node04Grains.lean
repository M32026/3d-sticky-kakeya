import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Strategy1Main
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Strategy2Main
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9Main

/-!
# Pure WZ2 Node 4: grains

This target proves `PureWZ2GrainsStatement`, the conjunction of:
1. `PureWZ2PaperADBridgeStatement` — proved in `ADBridge.lean`
2. `PureWZ2GrainsFromCriticalStatement` — via range-specific strategies

## Case split strategy

The second conjunct is proved by a case split on `outputLoss`:

- **outputLoss ≥ 2**: Strategy 1 — single-tube assembly
  (`pure_wz2_strategy1_main` in `Strategy1Main.lean`)
- **1 < outputLoss < 2**: Strategy 2 — direction bin pigeonholing
  (`pure_wz2_strategy2_main` in `Strategy2Main.lean`)
- **outputLoss ≤ 1**: Strategy 3 — paper-ordered robust multi-scale construction
  (`pure_wz2_strategy3_multiscale_main` in `Proposition63M9Main.lean`)
-/

namespace Kakeya.Assouad

theorem pure_wz2_node04_grains :
    PureWZ2GrainsStatement := by
  intro h_subunit h_extraction h_sticky
  constructor
  · -- First conjunct: AD bridge (proved)
    exact pure_wz2_paper_ad_bridge
  · -- Second conjunct: grains from critical via case split
    intro sigma hcrit outputLoss delta₀ hloss hdelta₀
    by_cases h1 : 2 ≤ outputLoss
    · -- Case 1: outputLoss ≥ 2 — Strategy 1 (single-tube)
      exact pure_wz2_strategy1_main
        h_subunit h_extraction h_sticky sigma hcrit outputLoss delta₀ hloss h1 hdelta₀
    · -- outputLoss < 2
      by_cases h2 : 1 < outputLoss
      · -- Case 2: 1 < outputLoss < 2 — Strategy 2 (direction binning)
        exact pure_wz2_strategy2_main
          h_subunit h_extraction h_sticky sigma hcrit outputLoss delta₀ hloss h2 hdelta₀
      · -- Case 3: outputLoss ≤ 1 — Strategy 3 Multi-Scale (base-family direct)
        have h3 : outputLoss ≤ 1 := by linarith
        exact pure_wz2_strategy3_multiscale_main
          h_subunit h_extraction h_sticky sigma hcrit outputLoss delta₀ hloss h3 hdelta₀

end Kakeya.Assouad
