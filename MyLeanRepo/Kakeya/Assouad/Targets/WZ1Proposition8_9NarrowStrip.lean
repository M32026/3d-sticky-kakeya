import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9NarrowUnion

/-!
Union-valued narrow common-strip branch used by the 3D Kakeya main line.

The arbitrary-three-class Proposition 8.9 display is stronger.  The two-set
Theorem 22 application repeats one endpoint set, and the same-endpoint theorem
below recovers exactly the Alternative (A) needed there.
-/

namespace Kakeya.Assouad

theorem wz1_proposition8_9_narrow_strip :
    WZ1Proposition8_9NarrowStripStatement :=
  wz1_proposition8_9_narrow_union

/-- The honest two-set Theorem 22 specialization used by Proposition 21. -/
theorem wz1_proposition8_9_narrow_strip_same_endpoint :
    WZ1Proposition8_9NarrowSameEndpointStatement :=
  wz1_proposition8_9_narrow_same_endpoint

end Kakeya.Assouad
