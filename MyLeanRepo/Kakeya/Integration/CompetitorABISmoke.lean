import Kakeya.Sticky
import Kakeya.DimensionThree.KakeyaConjecture
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConcreteABI
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2Unconditional

/-!
# Competitor/WZ2 ABI smoke test

This module is the first integration boundary.  It intentionally proves no
mathematics: it checks that the competitor Sticky interface and the WZ2
producer interfaces coexist in one Lean environment under the repository's
pinned Mathlib checkout.
-/

#check StickyKakeya.StickyFrostmanEstimate
#check StickyKakeya.stickyFrostmanEstimate
#check Kakeya.Assouad.PureWZ2Theorem5_2Statement
#check Kakeya.Assouad.PureWZ2Theorem5_2Unconditional
#check Kakeya.Assouad.PureWZ2FixedSupportDilatedStickyContract
#check Kakeya.Assouad.PureWZ2GWZReanchoredConversionStatement
#check Kakeya.Assouad.PureWZ2GWZRemarkStatement
#check Kakeya.Assouad.PureWZ2ConcreteGWZABIStatement
#check Kakeya.Assouad.pure_wz2_concrete_gwz_abi
#check KakeyaDimensionThree
