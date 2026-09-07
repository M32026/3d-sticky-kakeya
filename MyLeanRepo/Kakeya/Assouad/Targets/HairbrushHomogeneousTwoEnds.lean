import MyLeanRepo.Kakeya.Assouad.Hairbrush.HomogeneousTwoEnds

/-!
# Homogeneous per-hair two-ends refinement

This is equations (B.16)--(B.20) in the self-contained Appendix-B proof.

For every hair maximize `r^-zeta` times ball mass, restrict to the maximizing
ball, and pigeonhole a common dyadic radius.  The output two-ends coefficient
is absolute relative to the refined hair shading; it must not contain an
inverse power of `δ`.

Do not use the old lossy spatial-two-ends structure or select a stem.
-/

namespace Kakeya.Assouad

theorem hairbrush_homogeneous_two_ends :
    HairbrushHomogeneousTwoEndsStatement :=
  hairbrush_homogeneous_two_ends_main

end Kakeya.Assouad
