import MyLeanRepo.Kakeya.Assouad.WZ1.CrossPerturbation
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Transfer coarse direction packing through a balanced cover

Projective parent alignment sends every fine close-direction partner to a
coarse close-direction partner.  The absolute coarse packing count and the
balanced fiber multiplicity cap then bound the original fine count.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

lemma wz1Cross_projective_upper
    (u1 u2 v1 v2 : Point3)
    (_hu1 : ‖u1‖ = 1) (hu2 : ‖u2‖ = 1)
    (hv1 : ‖v1‖ = 1)
    (s1 s2 : ℝ)
    (hs1 : s1 = 1 ∨ s1 = -1)
    (hs2 : s2 = 1 ∨ s2 = -1)
    {rho kappa : ℝ}
    (h1 : ‖v1 - s1 • u1‖ ≤ 4 * rho)
    (h2 : ‖v2 - s2 • u2‖ ≤ 4 * rho)
    (hcross : ‖wz1Cross u1 u2‖ < kappa) :
    ‖wz1Cross v1 v2‖ < kappa + 8 * rho := by
  let e1 := v1 - s1 • u1
  let e2 := v2 - s2 • u2
  have hv1_eq : v1 = s1 • u1 + e1 := by simp [e1]
  have hv2_eq : v2 = s2 • u2 + e2 := by simp [e2]
  have hdecomp :
      wz1Cross v1 v2 =
        wz1Cross v1 e2 +
          s2 • wz1Cross e1 u2 +
          (s1 * s2) • wz1Cross u1 u2 := by
    rw [hv2_eq, wz1Cross_add_right, wz1Cross_smul_right,
      hv1_eq, wz1Cross_add_left, wz1Cross_smul_left,
      smul_add, smul_smul]
    simp only [mul_comm s2 s1]
    abel
  have habs1 : |s1| = 1 := by
    rcases hs1 with (rfl | rfl) <;> norm_num
  have habs2 : |s2| = 1 := by
    rcases hs2 with (rfl | rfl) <;> norm_num
  have hterm1 : ‖wz1Cross v1 e2‖ ≤ 4 * rho := by
    calc
      ‖wz1Cross v1 e2‖ ≤ ‖v1‖ * ‖e2‖ :=
        wz1Cross_norm_le _ _
      _ = ‖e2‖ := by rw [hv1]; ring
      _ ≤ 4 * rho := by simpa [e2] using h2
  have hterm2 : ‖s2 • wz1Cross e1 u2‖ ≤ 4 * rho := by
    rw [norm_smul, Real.norm_eq_abs, habs2, one_mul]
    calc
      ‖wz1Cross e1 u2‖ ≤ ‖e1‖ * ‖u2‖ :=
        wz1Cross_norm_le _ _
      _ = ‖e1‖ := by rw [hu2]; ring
      _ ≤ 4 * rho := by simpa [e1] using h1
  have hterm3 :
      ‖(s1 * s2) • wz1Cross u1 u2‖ =
        ‖wz1Cross u1 u2‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, habs1, habs2]
    ring
  rw [hdecomp]
  calc
    ‖wz1Cross v1 e2 +
        s2 • wz1Cross e1 u2 +
        (s1 * s2) • wz1Cross u1 u2‖
        ≤ ‖wz1Cross v1 e2‖ +
          ‖s2 • wz1Cross e1 u2‖ +
          ‖(s1 * s2) • wz1Cross u1 u2‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ < kappa + 8 * rho := by
      rw [hterm3]
      linarith

theorem wz1_robust_close_count_from_balanced :
    WZ1RobustCloseCountFromBalancedStatement := by
  intro hPacking
  rcases hPacking with ⟨D, hD, hPack⟩
  refine ⟨D, hD, ?_⟩
  intro delta sigma epsilon F U Y rho hrhoSmall
    balanced p hp i hi
  have hdelta : 0 < delta := balanced.refined_extremal.1
  have hrho : 0 < rho.1 := hdelta.trans_le rho.2.1
  let closeFine : Finset (Fin F.card) :=
    Finset.univ.filter fun j =>
      p ∈ balanced.refined.carrier j ∧
        ‖wz1Cross
          (F.tube i).direction (F.tube j).direction‖ < rho.1
  let parentSet : Finset (Fin (U.coarse rho).card) :=
    closeFine.image (U.cover rho).parent
  have hcoarsePoint :
      p ∈ balanced.coarseShading.carrier
        ((U.cover rho).parent i) :=
    balanced.point_compatibility i p hi
  have hparentClose : ∀ q ∈ parentSet,
      ‖wz1Cross
        ((U.coarse rho).tube
          ((U.cover rho).parent i)).direction
        ((U.coarse rho).tube q).direction‖ < 10 * rho.1 := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
    rcases Finset.mem_filter.mp hj with ⟨_, _hjp, hjcross⟩
    rcases balanced.direction_alignment i with
      ⟨si, hsi, hali⟩
    rcases balanced.direction_alignment j with
      ⟨sj, hsj, halj⟩
    have hupper := wz1Cross_projective_upper
      (F.tube i).direction (F.tube j).direction
      ((U.coarse rho).tube
        ((U.cover rho).parent i)).direction
      ((U.coarse rho).tube
        ((U.cover rho).parent j)).direction
      (F.tube i).direction_unit (F.tube j).direction_unit
      ((U.coarse rho).tube
        ((U.cover rho).parent i)).direction_unit
      si sj hsi hsj hali halj hjcross
    linarith [hrho]
  have hparentPoint : ∀ q ∈ parentSet,
      p ∈ balanced.coarseShading.carrier q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
    exact balanced.point_compatibility j p
      (Finset.mem_filter.mp hj).2.1
  let coarseClose : Finset (Fin (U.coarse rho).card) :=
    Finset.univ.filter fun q =>
      p ∈ balanced.coarseShading.carrier q ∧
        ‖wz1Cross
          ((U.coarse rho).tube
            ((U.cover rho).parent i)).direction
          ((U.coarse rho).tube q).direction‖ < 10 * rho.1
  have hparentSubset : parentSet ⊆ coarseClose := by
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hparentPoint q hq, hparentClose q hq⟩
  have hcoarseCard : coarseClose.card ≤ D := by
    change
      wz1CloseDirectionCount balanced.coarseShading p
        ((U.cover rho).parent i) (10 * rho.1) ≤ D
    exact hPack rho.1 hrho hrhoSmall (U.coarse rho)
      (U.coarse_distinct rho) balanced.coarseShading p
      ((U.cover rho).parent i) hcoarsePoint
  have hparentCard : parentSet.card ≤ D :=
    (Finset.card_le_card hparentSubset).trans hcoarseCard
  let fiberCap :=
    Kakeya.realRpowENN
      (delta / rho.1) (-sigma - epsilon)
  have hfiber : ∀ q ∈ parentSet,
      ((closeFine.filter fun j =>
        (U.cover rho).parent j = q).card : ENNReal) ≤
        fiberCap := by
    intro q _
    have hsub :
        closeFine.filter
            (fun j => (U.cover rho).parent j = q) ⊆
          ((U.cover rho).toFactoring.fiberIndices q).filter
            (fun j => p ∈ balanced.refined.carrier j) := by
      intro j hj
      rcases Finset.mem_filter.mp hj with
        ⟨hjclose, hparent⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hparent⟩,
          (Finset.mem_filter.mp hjclose).2.1⟩
    have hcard := Finset.card_le_card hsub
    have hbound :=
      balanced.fiber_multiplicity_upper q p
    have hcardENN :
        ((closeFine.filter fun j =>
          (U.cover rho).parent j = q).card : ENNReal) ≤
          ((U.cover rho).toFactoring.fiberPointMultiplicity
            balanced.refined q p : ENNReal) := by
      exact_mod_cast hcard
    exact hcardENN.trans hbound
  have hmaps :
      Set.MapsTo (U.cover rho).parent
        (closeFine : Set (Fin F.card))
        (parentSet : Set (Fin (U.coarse rho).card)) := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hcloseSum :
      (closeFine.card : ENNReal) =
        ∑ q ∈ parentSet,
          ((closeFine.filter fun j =>
            (U.cover rho).parent j = q).card : ENNReal) := by
    have hnat := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hnat]
    norm_cast
  have hcloseENN :
      (closeFine.card : ENNReal) ≤
        fiberCap * (D : ENNReal) := by
    calc
      (closeFine.card : ENNReal) =
          ∑ q ∈ parentSet,
            ((closeFine.filter fun j =>
              (U.cover rho).parent j = q).card : ENNReal) :=
        hcloseSum
      _ ≤ ∑ _q ∈ parentSet, fiberCap :=
        Finset.sum_le_sum fun q hq => hfiber q hq
      _ = (parentSet.card : ENNReal) * fiberCap := by
        simp [Finset.sum_const]
      _ ≤ (D : ENNReal) * fiberCap := by
        exact mul_le_mul_left
          (by exact_mod_cast hparentCard) fiberCap
      _ = fiberCap * (D : ENNReal) := mul_comm _ _
  change
    (wz1CloseDirectionCount
      balanced.refined p i rho.1 : ENNReal) ≤
      (D : ENNReal) *
        Kakeya.realRpowENN
          (delta / rho.1) (-sigma - epsilon)
  change
    ((Finset.univ.filter fun j =>
      p ∈ balanced.refined.carrier j ∧
        ‖wz1Cross
          (F.tube i).direction (F.tube j).direction‖ < rho.1).card :
      ENNReal) ≤
      (D : ENNReal) *
        Kakeya.realRpowENN
          (delta / rho.1) (-sigma - epsilon)
  change
    (closeFine.card : ENNReal) ≤ (D : ENNReal) * fiberCap
  exact hcloseENN.trans_eq (mul_comm fiberCap (D : ENNReal))

end Kakeya.Assouad
