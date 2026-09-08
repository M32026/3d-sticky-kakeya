import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Halo volume from a rolling inner ball

The halo estimate used in Section 5 depends only on a local rolling-ball
property of the parent body.  This formulation separates that argument from
whether the parent is a strict tube or an actual fixed dilation of a tube.
-/

noncomputable section

open Metric MeasureTheory

namespace Kakeya.Streamlined

/--
If every point of a closed body admits a nearby radius-`rho / 2` ball inside
the body and its radius-`rho` neighborhood, then the `rho`-halo of any subset
has volume at most `1728` times the portion of that halo inside the body.
-/
lemma rolling_body_halo_volume_bound
    {rho : ℝ} (hrho : 0 < rho)
    (K S : Set Point3) (hK_closed : IsClosed K) (hS : S ⊆ K)
    (h_inner :
      ∀ x ∈ K, ∃ y : Point3, dist x y ≤ rho / 2 ∧
        Metric.closedBall y (rho / 2) ⊆
          K ∩ Metric.closedBall x rho) :
    volume (Metric.cthickening rho S) ≤
      1728 * volume (K ∩ Metric.cthickening rho S) := by
  by_cases hS_empty : S = ∅
  · rw [hS_empty]
    simp
  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
    set U := Metric.cthickening rho S with hU_def
    set Z := K ∩ U with hZ_def
    have h_closure_sub : closure S ⊆ K := closure_minimal hS hK_closed
    have hU_eq : U = ⋃ z ∈ closure S, Metric.closedBall z rho :=
      Metric.cthickening_eq_biUnion_closedBall S (by linarith)
    let Yset : Set Point3 := {y | Metric.closedBall y (rho / 2) ⊆ Z}
    have h_cover : U ⊆ ⋃ y ∈ Yset, Metric.closedBall y (3 * rho / 2) := by
      intro x hx
      have h_exists_z : ∃ z, z ∈ closure S ∧ dist x z ≤ rho := by
        rw [hU_eq] at hx
        simpa [Set.mem_iUnion] using hx
      rcases h_exists_z with ⟨z, hz_closure, h_dist_xz⟩
      have hz_in_K : z ∈ K := h_closure_sub hz_closure
      rcases h_inner z hz_in_K with
        ⟨y, h_dist_zy_le, h_ball_sub⟩
      have h_ball_in_Z : Metric.closedBall y (rho / 2) ⊆ Z := by
        intro w hw
        have h_w_in_K : w ∈ K := (h_ball_sub hw).1
        have h_dist_wz : dist w z ≤ rho :=
          Metric.mem_closedBall.mp (h_ball_sub hw).2
        have h6 : Metric.infDist w S = Metric.infDist w (closure S) := by
          rw [Metric.infDist_closure]
        have h7 : Metric.infDist w (closure S) ≤ dist w z :=
          Metric.infDist_le_dist_of_mem hz_closure
        have h_infDist : Metric.infDist w S ≤ rho := by
          rw [h6]
          exact h7.trans h_dist_wz
        have h8 : Metric.infEDist w S ≠ ⊤ :=
          Metric.infEDist_ne_top hS_nonempty
        have h9 : Metric.infEDist w S =
            ENNReal.ofReal (Metric.infDist w S) := by
          have h10 : Metric.infDist w S =
              ENNReal.toReal (Metric.infEDist w S) := by
            rfl
          rw [h10, ENNReal.ofReal_toReal h8]
        have h10 : Metric.infEDist w S ≤ ENNReal.ofReal rho := by
          rw [h9]
          exact ENNReal.ofReal_le_ofReal h_infDist
        exact ⟨h_w_in_K, Metric.mem_cthickening_iff.mpr h10⟩
      have h_dist_xy : dist x y ≤ 3 * rho / 2 := by
        calc
          dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
          _ ≤ rho + rho / 2 := by linarith
          _ = 3 * rho / 2 := by ring
      have hy_in_Yset : y ∈ Yset := h_ball_in_Z
      have h_x_in_ball : x ∈ Metric.closedBall y (3 * rho / 2) :=
        Metric.mem_closedBall.mpr h_dist_xy
      exact Set.subset_biUnion_of_mem hy_in_Yset h_x_in_ball
    let r : Point3 → ℝ := fun _ => 3 * rho / 2
    have h_vitali :
        ∃ u : Set Point3, u ⊆ Yset ∧
          u.PairwiseDisjoint (fun a : Point3 => Metric.closedBall a (r a)) ∧
          ∀ a ∈ Yset, ∃ b ∈ u,
            Metric.closedBall a (r a) ⊆ Metric.closedBall b (4 * r b) :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
        Yset (fun x : Point3 => x) r (3 * rho / 2)
          (fun _ _ => le_refl _) 4 (by norm_num)
    rcases h_vitali with ⟨u, hu_sub, hu_disjoint, hu_cover⟩
    have hU_sub : U ⊆ ⋃ b ∈ u, Metric.closedBall b (6 * rho) := by
      intro x hx
      have h1 : ∃ a ∈ Yset, x ∈ Metric.closedBall a (3 * rho / 2) := by
        simpa [Set.mem_iUnion] using h_cover hx
      rcases h1 with ⟨a, ha_Y, hxa⟩
      rcases hu_cover a ha_Y with ⟨b, hb_u, hball_sub⟩
      have h9 : 4 * r b = 6 * rho := by
        simp [r]
        ring
      rw [h9] at hball_sub
      exact Set.subset_biUnion_of_mem hb_u (hball_sub hxa)
    have h_ball_disjoint :
        Set.PairwiseDisjoint u (fun b : Point3 => Metric.ball b (rho / 2)) := by
      intro b1 hb1 b2 hb2 hne
      have h_disj :
          Disjoint (Metric.closedBall b1 (3 * rho / 2))
            (Metric.closedBall b2 (3 * rho / 2)) :=
        hu_disjoint hb1 hb2 hne
      have h_sub1 :
          Metric.ball b1 (rho / 2) ⊆ Metric.closedBall b1 (3 * rho / 2) :=
        Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall (by linarith))
      have h_sub2 :
          Metric.ball b2 (rho / 2) ⊆ Metric.closedBall b2 (3 * rho / 2) :=
        Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall (by linarith))
      exact h_disj.mono h_sub1 h_sub2
    let f : u → Set Point3 := fun y => Metric.ball (y : Point3) (rho / 2)
    have hd : Pairwise (Function.onFun Disjoint f) := by
      intro i j hne
      have hne' : (i : Point3) ≠ (j : Point3) := by
        intro h
        apply hne
        exact Subtype.ext h
      exact h_ball_disjoint i.property j.property hne'
    have ho : ∀ i : u, IsOpen (f i) := fun _ => Metric.isOpen_ball
    have hne : ∀ i : u, (f i).Nonempty := by
      intro i
      have h : (i : Point3) ∈ Metric.ball (i : Point3) (rho / 2) := by
        simp only [Metric.mem_ball, dist_self]
        exact half_pos hrho
      exact ⟨(i : Point3), h⟩
    haveI : Countable u := Pairwise.countable_of_isOpen_disjoint hd ho hne
    have h_inner_sub : ∀ b ∈ u, Metric.closedBall b (rho / 2) ⊆ Z := by
      intro b hb
      exact hu_sub hb
    have h_inner_disjoint :
        Set.PairwiseDisjoint u (fun b : Point3 =>
          Metric.closedBall b (rho / 2)) := by
      intro b1 hb1 b2 hb2 hne
      have h_disj :
          Disjoint (Metric.closedBall b1 (3 * rho / 2))
            (Metric.closedBall b2 (3 * rho / 2)) :=
        hu_disjoint hb1 hb2 hne
      exact h_disj.mono
        (Metric.closedBall_subset_closedBall (by linarith))
        (Metric.closedBall_subset_closedBall (by linarith))
    let A : u → Set Point3 := fun b =>
      Metric.closedBall (b : Point3) (6 * rho)
    let B : u → Set Point3 := fun b =>
      Metric.closedBall (b : Point3) (rho / 2)
    have h_meas : ∀ b : u, MeasurableSet (B b) := fun _ =>
      Metric.isClosed_closedBall.measurableSet
    have h_disj' : Pairwise (fun i j : u => Disjoint (B i) (B j)) := by
      intro i j hne
      have hne' : (i : Point3) ≠ (j : Point3) := by
        intro h
        apply hne
        exact Subtype.ext h
      exact h_inner_disjoint i.property j.property hne'
    have hU_sub' : U ⊆ ⋃ b : u, A b := by
      intro x hx
      rcases Set.mem_iUnion₂.mp (hU_sub hx) with ⟨b, hb, hxb⟩
      exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hxb⟩
    have h_inner_sub' : (⋃ b : u, B b) ⊆ Z := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨b, hxb⟩
      exact h_inner_sub b b.property hxb
    have h_vol_scale : ∀ y : Point3,
        volume (Metric.closedBall y (6 * rho)) =
          1728 * volume (Metric.closedBall y (rho / 2)) := by
      intro y
      have h_eq : 6 * rho = (12 : ℝ) * (rho / 2) := by ring
      rw [h_eq]
      have h := MeasureTheory.Measure.addHaar_closedBall_mul
        volume y (by norm_num : (0 : ℝ) ≤ 12) (by linarith : 0 ≤ rho / 2)
      have h12 : (12 : ENNReal) ^ 3 = 1728 := by norm_num
      simpa [show Module.finrank ℝ Point3 = 3 from by simp,
        h12, mul_assoc] using h
    calc
      volume U ≤ volume (⋃ b : u, A b) := measure_mono hU_sub'
      _ ≤ ∑' b : u, volume (A b) := measure_iUnion_le A
      _ = ∑' b : u, (1728 * volume (B b)) := by
        apply tsum_congr
        intro b
        exact h_vol_scale b
      _ = 1728 * ∑' b : u, volume (B b) := by
        rw [ENNReal.tsum_mul_left]
      _ = 1728 * volume (⋃ b : u, B b) := by
        rw [measure_iUnion h_disj' h_meas]
      _ ≤ 1728 * volume Z := by gcongr

end Kakeya.Streamlined
