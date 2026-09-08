import MyLeanRepo.Kakeya.Integration.CompetitorModelBridge
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleVolume

/-!
# Audit of the repeated-leaf Sticky candidate

The proposed repeated-identical-tube counterexample does not satisfy the
current `C = 1` node-Frostman premise.  Already a singleton class fails at a
strictly larger parent radius: testing the Frostman inequality on the leaf
tube itself compares density `1` with the strict volume ratio
`|T_delta| / |T_rho| < 1`.

This file is an audit certificate only.  It does not change the public Sticky
contract.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Integration

/-- A tube shaded by its entire carrier. -/
def fullyShadedTube {delta : NNReal} (T : Tube delta Space3) :
    ShadedTube delta Space3 where
  toTube := T
  shade := T.carrier
  measurableSet_shade := T.isCompact.measurableSet
  shade_subset := subset_rfl

/-- One node at every grid scale, with every repeated leaf assigned to it. -/
noncomputable def repeatedCover {ι : Type*} {delta : NNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (s : Finset ι) (root : ι) (N : ℕ) (T : Tube delta Space3) :
    Tube.GridCoverSystem s (fun _ => T) N where
  indexSet := fun _ => {root}
  assign := fun _ _ => root
  tube := fun k _ => T.rescale (Tube.gridScale delta N k)
  assign_mem := by simp
  le_tube_assign := by
    intro k hk i hi
    refine T.le_rescale ?_
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have hk0 : k = 0 := Nat.le_zero.mp hk
      subst k
      simpa [Tube.gridScale] using hdeltaOne
    · calc
        delta = Tube.gridScale delta N N :=
          (Tube.gridScale_self delta hN).symm
        _ ≤ Tube.gridScale delta N k :=
          Tube.gridScale_antitone hdelta hdeltaOne N hk
  nested := by simp
  tube_nested := by
    intro k hk i hi
    exact Tube.rescale_le_rescale_of_radius_le T
      (Tube.gridScale_antitone hdelta hdeltaOne N (Nat.le_succ k))

/-- Repeated leaves support a one-node `UniformTubeSet`; node injectivity
does not impose leaf injectivity. -/
noncomputable def repeatedUniform {ι : Type*} {delta : NNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (s : Finset ι) (root : ι) (N : ℕ) (T : Tube delta Space3) :
    Tube.UniformTubeSet s (fun _ => T) N 1 where
  cover := repeatedCover hdelta hdeltaOne s root N T
  branchingN := fun _ => s.card
  tube_injOn := by
    intro k hk
    simp [repeatedCover]
  boundedOverlap := by
    intro k hk V
    refine le_trans ?_ (le_refl (1 : NNReal))
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  card_class_le := by
    intro k hk j hj
    simp [repeatedCover] at hj
    subst j
    simp [Tube.coverClass, repeatedCover]
  le_card_class := by
    intro k hk j hj
    simp [repeatedCover] at hj
    subst j
    simp [Tube.coverClass, repeatedCover]

/-- With full shading, the same one-node hierarchy is shaded-uniform with
constant `1`; its global and pointwise branching counts are both `s.card`. -/
noncomputable def repeatedShadedUniform {ι : Type*} {delta : NNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (s : Finset ι) (root : ι) (N : ℕ) (T : Tube delta Space3) :
    ShadedTube.ShadedUniformTubeSet s (fun _ => fullyShadedTube T) N 1 where
  tubeUniform := repeatedUniform hdelta hdeltaOne s root N T
  branchingN := fun _ => s.card
  localN := fun _ _ => s.card
  card_shadeClass_le := by
    intro x hx k hk i hi hxi
    have hxT : x ∈ T.carrier := hxi
    simp [ShadedTube.shadeClass, Tube.coverClass, repeatedUniform,
      repeatedCover, fullyShadedTube, hxT]
  le_card_shadeClass := by
    intro x hx k hk i hi hxi
    have hxT : x ∈ T.carrier := hxi
    simp [ShadedTube.shadeClass, Tube.coverClass, repeatedUniform,
      repeatedCover, fullyShadedTube, hxT]
  branchingN_le := by simp
  le_branchingN := by simp

private theorem deltaTubeVolume_eq_capsuleFormula {r : NNReal} (hr : 0 < r) :
    Kakeya.deltaTubeVolume (r : ℝ) =
      ENNReal.ofReal
        (Real.pi * (r : ℝ) ^ 2 +
          (4 / 3 : ℝ) * Real.pi * (r : ℝ) ^ 3) := by
  simpa [Kakeya.deltaTubeVolume,
    Kakeya.Streamlined.GeometricLemmas.capsule,
    Kakeya.Streamlined.GeometricLemmas.unitSegment0e0] using
      Kakeya.Streamlined.GeometricLemmas.capsule_volume_exact
        (r : ℝ) (by exact_mod_cast hr)

/-- In dimension three, the common volume of a positive-radius unit tube is
strictly increasing with its radius. -/
theorem deltaTubeVolume_strictMono_pos {delta rho : NNReal}
    (hdelta : 0 < delta) (hdr : delta < rho) :
    Kakeya.deltaTubeVolume (delta : ℝ) <
      Kakeya.deltaTubeVolume (rho : ℝ) := by
  have hdeltaR : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hdelta
  have hrhoR : (0 : ℝ) < (rho : ℝ) := by exact_mod_cast hdelta.trans hdr
  have hdrR : (delta : ℝ) < (rho : ℝ) := by exact_mod_cast hdr
  have hsq : (delta : ℝ) ^ 2 < (rho : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hdrR hdeltaR.le (by norm_num)
  have hcube : (delta : ℝ) ^ 3 < (rho : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hdrR hdeltaR.le (by norm_num)
  have hformula :
      Real.pi * (delta : ℝ) ^ 2 +
          (4 / 3 : ℝ) * Real.pi * (delta : ℝ) ^ 3 <
        Real.pi * (rho : ℝ) ^ 2 +
          (4 / 3 : ℝ) * Real.pi * (rho : ℝ) ^ 3 := by
    exact add_lt_add
      (mul_lt_mul_of_pos_left hsq Real.pi_pos)
      (mul_lt_mul_of_pos_left hcube (by positivity))
  rw [deltaTubeVolume_eq_capsuleFormula hdelta,
    deltaTubeVolume_eq_capsuleFormula (hdelta.trans hdr)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hformula

/-- Any nonempty class of identical leaves inside its same-axis larger-radius
parent is not `1`-Frostman.  The repeated index multiplicity cancels from both
densities, leaving the strict tube-volume ratio.  Therefore the proposed
repeated-leaf hierarchy cannot obtain node-Frostman constant `1`; the
obstruction precedes any leaf-separation question. -/
theorem not_repeated_isFrostmanIn_one_of_strict_radius
    {ι : Type*}
    {delta rho : NNReal} (hdelta : 0 < delta) (hdr : delta < rho)
    (s : Finset ι) (hs : s.Nonempty) (T : Tube delta Space3)
    (parent : Tube rho Space3)
    (hsub : T.toConvexSpaceBody ≤ parent.toConvexSpaceBody) :
    ¬ ConvexSpaceBody.IsFrostmanIn
        s
        (fun _ => T.toConvexSpaceBody)
        parent.toConvexSpaceBody 1 := by
  intro hFrostman
  have hineq := hFrostman T.toConvexSpaceBody hsub
  have hdeltaVolPos : 0 < volume T.carrier := by
    let n := Module.finrank ℝ Space3
    have hc0 : (Tube.le_volume.c n : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos n)).ne'
    have hd0 : (delta : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr hdelta).ne'
    have hp0 : (delta : ENNReal) ^ (n - 1) ≠ 0 :=
      pow_ne_zero (n - 1) hd0
    exact lt_of_lt_of_le
      (pos_iff_ne_zero.mpr (mul_ne_zero hc0 hp0))
      (Tube.le_volume T)
  have hdeltaVolTop : volume T.carrier ≠ ⊤ :=
    T.isCompact.measure_lt_top.ne
  have hrhoVolPos : 0 < volume parent.carrier := by
    let n := Module.finrank ℝ Space3
    have hc0 : (Tube.le_volume.c n : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos n)).ne'
    have hr0 : (rho : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (hdelta.trans hdr)).ne'
    have hp0 : (rho : ENNReal) ^ (n - 1) ≠ 0 :=
      pow_ne_zero (n - 1) hr0
    exact lt_of_lt_of_le
      (pos_iff_ne_zero.mpr (mul_ne_zero hc0 hp0))
      (Tube.le_volume parent)
  have hrhoVolTop : volume parent.carrier ≠ ⊤ :=
    parent.isCompact.measure_lt_top.ne
  have hdensitySelf :
      Kakeya.densityIn s
          (fun _ => T.toConvexSpaceBody) T.toConvexSpaceBody =
        (s.card : ENNReal) := by
    rw [Kakeya.densityIn_of_all_le]
    · rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc,
        ENNReal.div_self hdeltaVolPos.ne' hdeltaVolTop, mul_one]
    · intro i hi
      exact le_rfl
  have hdensityParent :
      Kakeya.densityIn s
          (fun _ => T.toConvexSpaceBody) parent.toConvexSpaceBody =
        (s.card : ENNReal) *
          (volume T.carrier / volume parent.carrier) := by
    rw [Kakeya.densityIn_of_all_le]
    · rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]
    · intro i hi
      simpa using hsub
  rw [hdensitySelf, hdensityParent, one_mul] at hineq
  have hcard0 : (s.card : ENNReal) ≠ 0 := by
    exact_mod_cast hs.card_pos.ne'
  have hcardTop : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top s.card
  have honeLeRatio :
      1 ≤ volume T.carrier / volume parent.carrier := by
    have hrewrite : (1 : ENNReal) * (s.card : ENNReal) ≤
        (volume T.carrier / volume parent.carrier) *
          (s.card : ENNReal) := by
      simpa [mul_comm] using hineq
    exact (ENNReal.mul_le_mul_iff_left hcard0 hcardTop).mp hrewrite
  have hparent_le_leaf :
      volume parent.carrier ≤ volume T.carrier := by
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hrhoVolPos.ne')
      (Or.inl hrhoVolTop), one_mul] at honeLeRatio
  have hstrict : volume T.carrier < volume parent.carrier := by
    calc
      volume T.carrier = (competitorTubeToDeltaTube T).volume :=
        (competitorTubeToDeltaTube_volume T).symm
      _ = Kakeya.deltaTubeVolume (delta : ℝ) :=
        Kakeya.Assouad.tube_volume_scaling.1 _ _
      _ < Kakeya.deltaTubeVolume (rho : ℝ) :=
        deltaTubeVolume_strictMono_pos hdelta hdr
      _ = (competitorTubeToDeltaTube parent).volume :=
        (Kakeya.Assouad.tube_volume_scaling.1 _ _).symm
      _ = volume parent.carrier :=
        competitorTubeToDeltaTube_volume parent
  exact (not_le_of_gt hstrict) hparent_le_leaf

/-- The explicit repeated-leaf shaded-uniform bundle fails the proposed
constant-`1` every-scale Frostman premise already at the top grid level. -/
theorem repeatedShadedUniform_not_isFrostmanAtEveryScale_one
    {ι : Type*} {delta : NNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (s : Finset ι) (hs : s.Nonempty) (root : ι) (N : ℕ)
    (T : Tube delta Space3) :
    ¬ Tube.UniformTubeSet.IsFrostmanAtEveryScale
        (repeatedShadedUniform hdelta hdeltaOne.le s root N T).tubeUniform 1 := by
  intro hFrostman
  have htop := hFrostman 0 (Nat.zero_le N) root (by
    simp [repeatedShadedUniform, repeatedUniform, repeatedCover])
  have hclass :
      Tube.coverClass s
          ((repeatedShadedUniform hdelta hdeltaOne.le s root N T).tubeUniform.cover.assign 0)
          root = s := by
    ext i
    simp [Tube.coverClass, repeatedShadedUniform, repeatedUniform, repeatedCover]
  rw [hclass] at htop
  change ConvexSpaceBody.IsFrostmanIn s
      (fun _ => T.toConvexSpaceBody)
      (T.rescale (Tube.gridScale delta N 0)).toConvexSpaceBody 1 at htop
  have htopRadius : delta < Tube.gridScale delta N 0 := by
    simpa [Tube.gridScale_zero] using hdeltaOne
  exact not_repeated_isFrostmanIn_one_of_strict_radius
    hdelta htopRadius s hs T (T.rescale (Tube.gridScale delta N 0))
      (T.le_rescale htopRadius.le) htop

end Kakeya.Integration

end
