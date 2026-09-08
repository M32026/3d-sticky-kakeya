import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleVolume
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Per-tube induced density estimate

For a δ-tube T contained in a ρ-tube S, and a measurable subset E ⊆ T:
`volume(S ∩ cthickening ρ E) ≥ c · volume(E) / volume(T) · volume(S)`

Proof: Fubini double-counting.
- Each y ∈ E sees at least 1/8 of B(y,ρ) inside S (midpoint ball argument).
- Each x sees at most 4·deltaTubeVol(δ)·ρ volume of T ∩ B(x,ρ).
- Equate integrals and simplify using tube volume bounds.

Whiteprint node: rho-tube-density.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Streamlined

/-! Re-export helpers from part 2 (inlined for standalone compilation) -/

lemma volume_coord_box (lo hi : Fin 3 → ℝ) (h : ∀ i, lo i ≤ hi i) :
    volume {z : Point3 | ∀ i, lo i ≤ z i ∧ z i ≤ hi i} =
    ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have h_mp : MeasurePreserving toLp := PiLp.volume_preserving_toLp (ι := Fin 3)
  let S_raw : Set (Fin 3 → ℝ) := Set.Icc lo hi
  have h_image : toLp '' S_raw = {z : Point3 | ∀ i, lo i ≤ z i ∧ z i ≤ hi i} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      intro i; exact ⟨hx.1 i, hx.2 i⟩
    · intro hz
      have h1 : lo ≤ z.ofLp := by intro i; exact (hz i).1
      have h2 : z.ofLp ≤ hi := by intro i; exact (hz i).2
      exact ⟨z.ofLp, ⟨h1, h2⟩, WithLp.toLp_ofLp (2 : ENNReal) z⟩
  have h_meas : MeasurableSet S_raw := measurableSet_Icc
  have h_cont_symm : Continuous (fun z : Point3 => z.ofLp) :=
    PiLp.continuous_ofLp (p := 2) (β := fun _ => ℝ)
  have h_img_meas : MeasurableSet (toLp '' S_raw) := by
    have h : toLp '' S_raw = (fun z : Point3 => z.ofLp) ⁻¹' S_raw := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy.1, hy.2⟩
      · intro hz
        exact ⟨z.ofLp, hz, WithLp.toLp_ofLp (2 : ENNReal) z⟩
    rw [h]
    exact h_meas.preimage h_cont_symm.measurable
  have h_pre : volume (toLp ⁻¹' (toLp '' S_raw)) = volume (toLp '' S_raw) :=
    h_mp.measure_preimage h_img_meas.nullMeasurableSet
  have h_eq : toLp ⁻¹' (toLp '' S_raw) = S_raw := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have h' : x = y := WithLp.toLp_injective (2 : ENNReal) hxy.symm
      rw [h']; exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have h_vol : volume (toLp '' S_raw) = volume S_raw := by
    have h : volume (toLp ⁻¹' (toLp '' S_raw)) = volume S_raw := by rw [h_eq]
    exact h_pre.symm.trans h
  rw [←h_image, h_vol, Real.volume_Icc_pi]
  have h_nonneg : ∀ i, 0 ≤ hi i - lo i := by intro i; linarith [h i]
  have h_prod : (∏ i : Fin 3, ENNReal.ofReal (hi i - lo i)) =
      ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
    have h5 : ∏ i : Fin 3, ENNReal.ofReal (hi i - lo i) =
        ENNReal.ofReal (hi 0 - lo 0) * ENNReal.ofReal (hi 1 - lo 1) * ENNReal.ofReal (hi 2 - lo 2) := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
      <;> simp [mul_assoc]
      <;> ring
    rw [h5]
    have h_mul : ENNReal.ofReal (hi 0 - lo 0) * ENNReal.ofReal (hi 1 - lo 1) * ENNReal.ofReal (hi 2 - lo 2) =
        ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
      rw [←ENNReal.ofReal_mul (h_nonneg 0), ←ENNReal.ofReal_mul (mul_nonneg (h_nonneg 0) (h_nonneg 1))]
      <;> ring
    exact h_mul
  exact h_prod

private lemma coord_abs_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h_inner : ∀ (j : Fin 3), inner ℝ (x j) (x j) = |x j| ^ 2 := by
    intro j
    simp [real_inner_self_eq_norm_sq] <;> ring
  have h2 : ‖x‖ ^ 2 = ∑ j : Fin 3, |x j| ^ 2 := by
    rw [←real_inner_self_eq_norm_sq, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact h_inner j
  have h1 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h2]
    let f : Fin 3 → ℝ := fun j => |x j| ^ 2
    have h3 : f i ≤ ∑ j ∈ Finset.univ, f j :=
      Finset.single_le_sum (fun j _ => sq_nonneg (|x j|)) (Finset.mem_univ i)
    exact h3
  have h4 : 0 ≤ |x i| := by positivity
  have h5 : 0 ≤ ‖x‖ := by positivity
  nlinarith

/-- Strong bound: volume(T ∩ B(x,ρ)) ≤ 4 · deltaTubeVolume(δ) · ρ. -/
lemma tube_ball_intersection_le4 {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hδρ : δ ≤ ρ)
    (T : Kakeya.DeltaTube δ) (x : Point3) :
    volume (T.carrier ∩ closedBall x ρ) ≤
      ENNReal.ofReal (4 : ℝ) * Kakeya.deltaTubeVolume δ * ENNReal.ofReal ρ := by
  let e0 : Point3 := EuclideanSpace.single 0 1
  let L : Point3 ≃ₗᵢ[ℝ] Point3 :=
    (Submodule.span ℝ {T.direction - e0})ᗮ.reflection
  have hL_dir : L T.direction = e0 := by
    apply Submodule.reflection_sub
    rw [T.direction_unit] <;> simp [e0, EuclideanSpace.norm_eq] <;> norm_num
  let e : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    AffineIsometryEquiv.mk' (fun z : Point3 => L (z - T.base)) L T.base (by
      intro z
      have h0 : L (T.base - T.base) = (0 : Point3) := by
        have h1 : T.base - T.base = (0 : Point3) := by simp
        rw [h1]
        exact L.map_zero
      simp [vsub_eq_sub, h0] <;> abel)
  have h_e_apply : ∀ z, e z = L (z - T.base) := by
    intro z
    rw [AffineIsometryEquiv.coe_mk'] <;> rfl
  have h_seg : e '' (unitSegment T.base T.direction) = unitSegment 0 e0 := by
    ext y
    simp only [unitSegment, Set.mem_image]
    constructor
    · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      have h_sub : T.base + t • T.direction - T.base = t • T.direction := by abel
      rw [h_e_apply, h_sub, L.map_smul, hL_dir] <;> abel
    · rintro ⟨t, ht, rfl⟩
      refine ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
      have h_sub : T.base + t • T.direction - T.base = t • T.direction := by abel
      rw [h_e_apply, h_sub, L.map_smul, hL_dir] <;> abel
  have h_carrier_img : e '' T.carrier = cthickening δ (unitSegment 0 e0) := by
    have h1 : e '' T.carrier = e '' (cthickening δ (unitSegment T.base T.direction)) := rfl
    rw [h1]
    have h2 : e '' cthickening δ (unitSegment T.base T.direction) =
        cthickening δ (e '' unitSegment T.base T.direction) := by
      ext y
      simp only [Set.mem_image, cthickening_eq_preimage_infEDist, Set.mem_preimage, Set.mem_Iic]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have h : infEDist (e z) (e '' unitSegment T.base T.direction) =
            infEDist z (unitSegment T.base T.direction) := Metric.infEDist_image e.isometry
        rw [h]; exact hz
      · intro hy
        let z := e.symm y
        have h1 : e z = y := e.apply_symm_apply y
        have h2 : infEDist z (unitSegment T.base T.direction) =
            infEDist (e z) (e '' unitSegment T.base T.direction) :=
          (Metric.infEDist_image e.isometry).symm
        refine ⟨z, ?_, h1⟩
        rw [h2, h1]; exact hy
    rw [h2, h_seg] <;> rfl
  have h_ball_img : e '' closedBall x ρ = closedBall (e x) ρ := by
    ext y
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h : dist (e z) (e x) = dist z x := e.isometry.dist_eq z x
      rw [h]; exact hz
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have h : dist (e.symm y) x = dist y (e x) := by
        calc dist (e.symm y) x
          = dist (e (e.symm y)) (e x) := (e.isometry.dist_eq _ _).symm
        _ = dist y (e x) := by rw [e.apply_symm_apply]
      rw [h]; exact hy
  have hT_meas : MeasurableSet T.carrier :=
    IsClosed.measurableSet (isClosed_Iic.preimage continuous_infEDist)
  have h_vol_pres : volume (e '' (T.carrier ∩ closedBall x ρ)) =
      volume (T.carrier ∩ closedBall x ρ) :=
    AffineIsometryEquiv.volume_image e (T.carrier ∩ closedBall x ρ)
      (hT_meas.inter isClosed_closedBall.measurableSet)
  have h_compact : IsCompact (unitSegment (0 : Point3) e0) := by
    apply IsCompact.image (isCompact_Icc)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have h_nonempty : (unitSegment (0 : Point3) e0).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, by norm_num, ?_⟩
    simp [e0, EuclideanSpace.single] <;> abel
  let x' := e x
  let lo0 := x' 0 - ρ
  let hi0 := x' 0 + ρ
  let box : Set Point3 := {z | lo0 ≤ z 0 ∧ z 0 ≤ hi0 ∧ -δ ≤ z 1 ∧ z 1 ≤ δ ∧ -δ ≤ z 2 ∧ z 2 ≤ δ}
  have h_box : e '' (T.carrier ∩ closedBall x ρ) ⊆ box := by
    intro z hz
    have h_exists : ∃ (w : Point3), w ∈ T.carrier ∩ closedBall x ρ ∧ e w = z := by
      simpa [Set.mem_image] using hz
    rcases h_exists with ⟨w, hw, rfl⟩
    have h1 : w ∈ T.carrier := hw.1
    have h2 : w ∈ closedBall x ρ := hw.2
    have h3 : e w ∈ cthickening δ (unitSegment 0 e0) := by
      rw [←h_carrier_img]; exact Set.mem_image_of_mem e h1
    have h4 : e w ∈ closedBall x' ρ := by
      rw [←h_ball_img]; exact Set.mem_image_of_mem e h2
    rcases h_compact.exists_infEDist_eq_edist h_nonempty (e w) with ⟨p, hp_in, hp_edist⟩
    have h_infEDist_le : infEDist (e w) (unitSegment (0 : Point3) e0) ≤ ENNReal.ofReal δ := h3
    rw [hp_edist] at h_infEDist_le
    have h_edist_le : edist (e w) p ≤ ENNReal.ofReal δ := h_infEDist_le
    have h_dist_le : dist (e w) p ≤ δ := by
      have h_eq : edist (e w) p = ENNReal.ofReal (dist (e w) p) := by exact edist_dist _ _
      rw [h_eq] at h_edist_le
      have h_iff : ENNReal.ofReal (dist (e w) p) ≤ ENNReal.ofReal δ ↔ dist (e w) p ≤ δ :=
        ENNReal.ofReal_le_ofReal_iff hδ.le
      exact h_iff.mp h_edist_le
    rcases hp_in with ⟨t, ht, rfl⟩
    have h_norm : ‖e w - t • e0‖ ≤ δ := by simpa [dist_eq_norm] using h_dist_le
    have h_ball_dist : dist (e w) x' ≤ ρ := h4
    have h_coord0 : |(e w) 0 - x' 0| ≤ ρ := by
      calc |(e w) 0 - x' 0|
        = |(e w - x') 0| := by simp
      _ ≤ ‖e w - x'‖ := coord_abs_le_norm (e w - x') 0
      _ = dist (e w) x' := by rfl
      _ ≤ ρ := h_ball_dist
    have h_perp1 : |(e w - t • e0) 1| ≤ δ := by
      calc |(e w - t • e0) 1| ≤ ‖e w - t • e0‖ := coord_abs_le_norm (e w - t • e0) 1
      _ ≤ δ := h_norm
    have h_perp2 : |(e w - t • e0) 2| ≤ δ := by
      calc |(e w - t • e0) 2| ≤ ‖e w - t • e0‖ := coord_abs_le_norm (e w - t • e0) 2
      _ ≤ δ := h_norm
    have h_e01 : (t • e0) 1 = 0 := by simp [e0, EuclideanSpace.single]
    have h_e02 : (t • e0) 2 = 0 := by simp [e0, EuclideanSpace.single]
    have h_z1 : |(e w) 1| ≤ δ := by
      have h : (e w) 1 = (e w - t • e0) 1 := by simp [h_e01] <;> ring
      rw [h]; exact h_perp1
    have h_z2 : |(e w) 2| ≤ δ := by
      have h : (e w) 2 = (e w - t • e0) 2 := by simp [h_e02] <;> ring
      rw [h]; exact h_perp2
    have h_lo0 : lo0 ≤ (e w) 0 := by
      dsimp only [lo0]; linarith [abs_le.mp h_coord0]
    have h_hi0 : (e w) 0 ≤ hi0 := by
      dsimp only [hi0]; linarith [abs_le.mp h_coord0]
    exact ⟨h_lo0, h_hi0,
      by linarith [abs_le.mp h_z1], by linarith [abs_le.mp h_z1],
      by linarith [abs_le.mp h_z2], by linarith [abs_le.mp h_z2]⟩
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => lo0
    | 1 => -δ
    | 2 => -δ
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => hi0
    | 1 => δ
    | 2 => δ
  have h_box_eq : box = {z : Point3 | ∀ i, lo i ≤ z i ∧ z i ≤ hi i} := by
    ext z
    simp only [box, lo, hi, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      intro i
      fin_cases i <;> tauto
    · intro h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2⟩
  have h_lo_hi : ∀ i, lo i ≤ hi i := by
    intro i; fin_cases i <;> dsimp only [lo, hi, lo0, hi0] <;> linarith
  have h_vol_box : volume box = ENNReal.ofReal ((hi0 - lo0) * (2 * δ) * (2 * δ)) := by
    rw [h_box_eq, volume_coord_box lo hi h_lo_hi]
    <;> dsimp only [lo, hi, lo0, hi0] <;> ring
  have h_len : hi0 - lo0 = 2 * ρ := by dsimp only [hi0, lo0] <;> ring
  rw [←h_vol_pres]
  have h_main : volume (e '' (T.carrier ∩ closedBall x ρ)) ≤ volume box := measure_mono h_box
  rw [h_vol_box, h_len] at h_main
  have h_8δ2ρ : ENNReal.ofReal ((2 * ρ) * (2 * δ) * (2 * δ)) =
      ENNReal.ofReal (8 * δ ^ 2 * ρ) := by congr 1 <;> ring
  rw [h_8δ2ρ] at h_main
  have h_tube_vol_ge : ENNReal.ofReal (2 * δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
    tube_volume_ge_two_delta_sq δ hδ
  have h_final : ENNReal.ofReal (8 * δ ^ 2 * ρ) ≤
      ENNReal.ofReal (4 : ℝ) * Kakeya.deltaTubeVolume δ * ENNReal.ofReal ρ := by
    have h1 : ENNReal.ofReal (8 * δ ^ 2 * ρ) =
        ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (2 * δ ^ 2) * ENNReal.ofReal ρ := by
      rw [←ENNReal.ofReal_mul (by positivity), ←ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h1]
    gcongr
  exact le_trans h_main h_final

/-! ### Lower bound: S ∩ B(y,ρ) has at least 1/8 of ball volume -/

/-- For y in a ρ-tube S, volume(S ∩ B(y,ρ)) ≥ (1/8) · volume(B(0,ρ)). -/
lemma ball_intersection_tube_lower {ρ : ℝ} (hρ : 0 < ρ)
    (S : Kakeya.DeltaTube ρ) {y : Point3} (hy : y ∈ S.carrier) :
    volume (S.carrier ∩ closedBall y ρ) ≥
      ENNReal.ofReal (1 / 8 : ℝ) * volume (closedBall (0 : Point3) ρ) := by
  let seg := unitSegment S.base S.direction
  have h_compact : IsCompact seg := by
    apply IsCompact.image (isCompact_Icc)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have h_nonempty : seg.Nonempty := by
    refine ⟨S.base, ?_⟩
    refine ⟨0, by norm_num, ?_⟩
    simp [unitSegment, zero_smul]
    <;> abel
  have h_y_in : infEDist y seg ≤ ENNReal.ofReal ρ := hy
  rcases h_compact.exists_infEDist_eq_edist h_nonempty y with ⟨p, hp_in, hp_edist⟩
  have h_edist_le : edist y p ≤ ENNReal.ofReal ρ := by
    rw [←hp_edist]; exact h_y_in
  have h_dist_le : dist y p ≤ ρ := by
    have h_eq : edist y p = ENNReal.ofReal (dist y p) := by exact edist_dist _ _
    rw [h_eq] at h_edist_le
    have h_iff : ENNReal.ofReal (dist y p) ≤ ENNReal.ofReal ρ ↔ dist y p ≤ ρ :=
      ENNReal.ofReal_le_ofReal_iff hρ.le
    exact h_iff.mp h_edist_le
  let m : Point3 := (1 / 2 : ℝ) • (y + p)
  have h2m : (2 : ℝ) • m = y + p := by
    have h1 : (2 : ℝ) • m = m + m := by
      simp [two_smul] <;> abel
    rw [h1]
    have h2 : m + m = (1 / 2 : ℝ) • (y + p) + (1 / 2 : ℝ) • (y + p) := by rfl
    rw [h2]
    have h3 : (1 / 2 : ℝ) • (y + p) + (1 / 2 : ℝ) • (y + p) = (1 : ℝ) • (y + p) := by
      rw [←add_smul] <;> norm_num
    rw [h3] <;> simp
  have h2p : (2 : ℝ) • p = p + p := by simp [two_smul] <;> abel
  have h2mp : (2 : ℝ) • (m - p) = y - p := by
    calc (2 : ℝ) • (m - p)
      = (2 : ℝ) • m - (2 : ℝ) • p := by rw [smul_sub]
    _ = (y + p) - (2 : ℝ) • p := by rw [h2m]
    _ = y - p := by rw [h2p] <;> abel
  have h_dist_mp : dist m p = dist y p / 2 := by
    have h1 : ‖(2 : ℝ) • (m - p)‖ = 2 * ‖m - p‖ := by
      have h11 : ‖(2 : ℝ) • (m - p)‖ = ‖(2 : ℝ)‖ * ‖m - p‖ := by
        exact norm_smul (2 : ℝ) (m - p)
      rw [h11]
      have h12 : ‖(2 : ℝ)‖ = 2 := by
        simp [Real.norm_eq_abs] <;> norm_num
      rw [h12] <;> ring
    have h2 : ‖(2 : ℝ) • (m - p)‖ = ‖y - p‖ := by rw [h2mp]
    have h3 : 2 * ‖m - p‖ = ‖y - p‖ := by linarith
    have h4 : ‖m - p‖ = ‖y - p‖ / 2 := by linarith
    have h5 : dist m p = ‖m - p‖ := by rw [dist_eq_norm]
    have h6 : dist y p = ‖y - p‖ := by rw [dist_eq_norm]
    rw [h5, h6, h4] <;> ring
  have h2y : (2 : ℝ) • y = y + y := by simp [two_smul] <;> abel
  have h2my : (2 : ℝ) • (m - y) = p - y := by
    calc (2 : ℝ) • (m - y)
      = (2 : ℝ) • m - (2 : ℝ) • y := by rw [smul_sub]
    _ = (y + p) - (2 : ℝ) • y := by rw [h2m]
    _ = p - y := by rw [h2y] <;> abel
  have h_dist_my : dist m y = dist y p / 2 := by
    have h1 : ‖(2 : ℝ) • (m - y)‖ = 2 * ‖m - y‖ := by
      have h11 : ‖(2 : ℝ) • (m - y)‖ = ‖(2 : ℝ)‖ * ‖m - y‖ := by
        exact norm_smul (2 : ℝ) (m - y)
      rw [h11]
      have h12 : ‖(2 : ℝ)‖ = 2 := by
        simp [Real.norm_eq_abs] <;> norm_num
      rw [h12] <;> ring
    have h2 : ‖(2 : ℝ) • (m - y)‖ = ‖p - y‖ := by rw [h2my]
    have h3 : 2 * ‖m - y‖ = ‖p - y‖ := by linarith
    have h4 : ‖m - y‖ = ‖p - y‖ / 2 := by linarith
    have h5 : ‖p - y‖ = ‖y - p‖ := by
      have h6 : p - y = -(y - p) := by abel
      rw [h6, norm_neg]
    have h7 : dist m y = ‖m - y‖ := by rw [dist_eq_norm]
    have h8 : dist y p = ‖y - p‖ := by rw [dist_eq_norm]
    rw [h7, h8, h4, h5] <;> ring
  have h1 : closedBall m (ρ / 2) ⊆ S.carrier := by
    intro z hz
    have h_dist_zp : dist z p ≤ ρ := by
      calc dist z p
        ≤ dist z m + dist m p := dist_triangle z m p
      _ ≤ ρ / 2 + dist y p / 2 := by
        rw [h_dist_mp]
        have h3 : dist z m ≤ ρ / 2 := hz
        linarith
      _ ≤ ρ := by linarith [h_dist_le]
    have h4 : infEDist z seg ≤ ENNReal.ofReal ρ := by
      have h5 : infEDist z seg ≤ edist z p := Metric.infEDist_le_edist_of_mem hp_in
      have h6 : edist z p = ENNReal.ofReal (dist z p) := by exact edist_dist _ _
      rw [h6] at h5
      have h7 : ENNReal.ofReal (dist z p) ≤ ENNReal.ofReal ρ := by
        exact ENNReal.ofReal_le_ofReal_iff hρ.le |>.mpr h_dist_zp
      exact le_trans h5 h7
    exact h4
  have h2 : closedBall m (ρ / 2) ⊆ closedBall y ρ := by
    intro z hz
    have h_dist_zy : dist z y ≤ ρ := by
      calc dist z y
        ≤ dist z m + dist m y := dist_triangle z m y
      _ ≤ ρ / 2 + dist y p / 2 := by
        rw [h_dist_my]
        have h3 : dist z m ≤ ρ / 2 := hz
        linarith
      _ ≤ ρ := by linarith [h_dist_le]
    exact h_dist_zy
  have h3 : closedBall m (ρ / 2) ⊆ S.carrier ∩ closedBall y ρ := by
    intro z hz
    exact ⟨h1 hz, h2 hz⟩
  have h4 : volume (S.carrier ∩ closedBall y ρ) ≥ volume (closedBall m (ρ / 2)) :=
    measure_mono h3
  have hρ2 : ρ / 2 = (1 / 2 : ℝ) * ρ := by ring
  have h5 : volume (closedBall m (ρ / 2)) =
      ENNReal.ofReal (1 / 8 : ℝ) * volume (closedBall (0 : Point3) ρ) := by
    rw [hρ2]
    have h_scale := MeasureTheory.Measure.addHaar_closedBall_mul_of_pos volume m
      (show (0 : ℝ) < 1 / 2 by norm_num) ρ
    have h_finrank : Module.finrank ℝ Point3 = 3 := by
      simp [Point3]
      <;> decide
    rw [h_scale, h_finrank]
    have h6 : ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) = ENNReal.ofReal (1 / 8 : ℝ) := by
      congr 1 <;> norm_num
    rw [h6] <;> ring
  rw [h5] at h4
  exact h4

/-! ### Main Fubini double-counting proof -/

/--
Per-tube induced density estimate.

Given a δ-tube T contained in a ρ-tube S, and a measurable subset E ⊆ T,
the ρ-thickening of E intersected with S has volume at least
`c · volume(E) / deltaTubeVolume(δ) · volume(S)`.
-/
lemma per_tube_density {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (T : Kakeya.DeltaTube δ) (S : Kakeya.DeltaTube ρ)
    (h_cont : T.carrier ⊆ S.carrier)
    (E : Set Point3) (hE_meas : MeasurableSet E) (hE_sub : E ⊆ T.carrier) :
    volume (S.carrier ∩ cthickening ρ E) ≥
      ENNReal.ofReal (1 / 100 : ℝ) * volume E / Kakeya.deltaTubeVolume δ * S.volume := by
  classical
  let A : Set Point3 := S.carrier ∩ cthickening ρ E
  let B : ENNReal := volume (closedBall (0 : Point3) ρ)
  let D : ENNReal := Kakeya.deltaTubeVolume δ
  let VS : ENNReal := S.volume
  let VE : ENNReal := volume E
  -- If volume E = 0, RHS is 0, trivial
  by_cases hVE : volume E = 0
  · rw [hVE]
    <;> simp
    <;> exact zero_le _
  -- If D = ⊤, RHS is 0, trivial
  by_cases hD : Kakeya.deltaTubeVolume δ = ⊤
  · rw [hD]
    <;> simp
    <;> exact zero_le _
  -- Define the Fubini relation set
  let R : Set (Point3 × Point3) :=
    {p | p.1 ∈ S.carrier ∧ p.2 ∈ E ∧ dist p.1 p.2 ≤ ρ}
  have hS_meas : MeasurableSet S.carrier :=
    IsClosed.measurableSet (isClosed_Iic.preimage continuous_infEDist)
  have hR_meas : MeasurableSet R := by
    have h1 : MeasurableSet {p : Point3 × Point3 | p.1 ∈ S.carrier} :=
      hS_meas.preimage measurable_fst
    have h2 : MeasurableSet {p : Point3 × Point3 | p.2 ∈ E} :=
      hE_meas.preimage measurable_snd
    have h_cont_dist : Continuous (fun p : Point3 × Point3 => dist p.1 p.2) :=
      continuous_dist
    have h3 : MeasurableSet {p : Point3 × Point3 | dist p.1 p.2 ≤ ρ} :=
      (isClosed_Iic.preimage h_cont_dist).measurableSet
    exact h1.inter (h2.inter h3)
  have h_slice_x : ∀ (x : Point3), (Prod.mk x ⁻¹' R) =
      if x ∈ S.carrier then E ∩ closedBall x ρ else ∅ := by
    intro x
    ext y
    simp only [R, Set.mem_preimage, Set.mem_setOf_eq]
    by_cases hx : x ∈ S.carrier
    · rw [if_pos hx]
      constructor
      · rintro ⟨hSx, hEy, hdist⟩
        refine' ⟨hEy, _⟩
        simpa [Metric.mem_closedBall, dist_comm] using hdist
      · rintro ⟨hEy, hball⟩
        have hdist : dist x y ≤ ρ := by
          simpa [Metric.mem_closedBall, dist_comm] using hball
        exact ⟨hx, hEy, hdist⟩
    · rw [if_neg hx]
      simp [hx]
  have h_slice_y : ∀ (y : Point3), ((fun x : Point3 => (x, y)) ⁻¹' R) =
      if y ∈ E then S.carrier ∩ closedBall y ρ else ∅ := by
    intro y
    ext x
    simp only [R, Set.mem_preimage, Set.mem_setOf_eq]
    by_cases hy : y ∈ E
    · rw [if_pos hy]
      constructor
      · rintro ⟨hSx, hEy, hdist⟩
        refine' ⟨hSx, _⟩
        simpa [Metric.mem_closedBall, dist_comm] using hdist
      · rintro ⟨hSx, hball⟩
        have hdist : dist x y ≤ ρ := by
          simpa [Metric.mem_closedBall, dist_comm] using hball
        exact ⟨hSx, hy, hdist⟩
    · rw [if_neg hy]
      simp [hy]
  -- Fubini: both orders of integration equal volume(R)
  have hvol_eq : MeasureTheory.volume = (MeasureTheory.volume : Measure Point3).prod
      (MeasureTheory.volume : Measure Point3) :=
    MeasureTheory.Measure.volume_eq_prod Point3 Point3
  have h_eq1 : (∫⁻ (x : Point3), volume (Prod.mk x ⁻¹' R)) =
      (∫⁻ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R)) := by
    have h1 : (volume.prod volume) R = ∫⁻ (x : Point3), volume (Prod.mk x ⁻¹' R) :=
      MeasureTheory.Measure.prod_apply hR_meas
    have h2 : (volume.prod volume) R = ∫⁻ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R) :=
      MeasureTheory.Measure.prod_apply_symm hR_meas
    have h3 : volume R = (volume.prod volume) R := by rw [hvol_eq]
    have h4 : ∫⁻ (x : Point3), volume (Prod.mk x ⁻¹' R) = volume R := by
      exact h1.symm
    have h5 : ∫⁻ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R) = volume R := by
      exact h2.symm
    rw [h4, h5]
  -- Lower bound on y-integral
  have h_lower : (∫⁻ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R)) ≥
      ENNReal.ofReal (1 / 8 : ℝ) * B * VE := by
    have h3 : ∀ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R) ≥
        if y ∈ E then ENNReal.ofReal (1 / 8 : ℝ) * B else 0 := by
      intro y
      by_cases hy : y ∈ E
      · have h_slice : ((fun x : Point3 => (x, y)) ⁻¹' R) = S.carrier ∩ closedBall y ρ := by
          rw [h_slice_y y, if_pos hy]
        rw [h_slice, if_pos hy]
        exact ball_intersection_tube_lower hρ S (h_cont (hE_sub hy))
      · have h_slice : ((fun x : Point3 => (x, y)) ⁻¹' R) = ∅ := by
          rw [h_slice_y y, if_neg hy]
        rw [h_slice, if_neg hy] <;> simp
    have h4 : (∫⁻ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R)) ≥
        ∫⁻ (y : Point3), (if y ∈ E then ENNReal.ofReal (1 / 8 : ℝ) * B else 0) :=
      lintegral_mono h3
    have h_ind1 : (fun y : Point3 => (if y ∈ E then ENNReal.ofReal (1 / 8 : ℝ) * B else 0)) =
        Set.indicator E (fun _ : Point3 => ENNReal.ofReal (1 / 8 : ℝ) * B) := by
      funext y
      simp [Set.indicator_apply]
      <;> split_ifs <;> tauto
    have h5 : (∫⁻ (y : Point3), (if y ∈ E then ENNReal.ofReal (1 / 8 : ℝ) * B else 0)) =
        ENNReal.ofReal (1 / 8 : ℝ) * B * VE := by
      rw [h_ind1]
      rw [MeasureTheory.lintegral_indicator_const hE_meas (ENNReal.ofReal (1 / 8 : ℝ) * B)]
      <;> ring
    have h6 : (∫⁻ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R)) ≥
        ENNReal.ofReal (1 / 8 : ℝ) * B * VE := by
      calc (∫⁻ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R))
        ≥ ∫⁻ (y : Point3), (if y ∈ E then ENNReal.ofReal (1 / 8 : ℝ) * B else 0) := h4
      _ = ENNReal.ofReal (1 / 8 : ℝ) * B * VE := h5
    exact h6
  -- Upper bound on x-integral
  have h_upper : (∫⁻ (x : Point3), volume (Prod.mk x ⁻¹' R)) ≤
      ENNReal.ofReal (4 : ℝ) * D * ENNReal.ofReal ρ * volume A := by
    let C : ENNReal := ENNReal.ofReal (4 : ℝ) * D * ENNReal.ofReal ρ
    have h5 : ∀ (x : Point3), volume (Prod.mk x ⁻¹' R) ≤ if x ∈ A then C else 0 := by
      intro x
      by_cases hxS : x ∈ S.carrier
      · have h_slice : (Prod.mk x ⁻¹' R) = E ∩ closedBall x ρ := by
          rw [h_slice_x x, if_pos hxS]
        rw [h_slice]
        by_cases hxA : x ∈ A
        · rw [if_pos hxA]
          have h6 : E ∩ closedBall x ρ ⊆ T.carrier ∩ closedBall x ρ := by
            intro z hz
            exact ⟨hE_sub hz.1, hz.2⟩
          have h7 : volume (E ∩ closedBall x ρ) ≤ volume (T.carrier ∩ closedBall x ρ) :=
            measure_mono h6
          have h8 : volume (T.carrier ∩ closedBall x ρ) ≤ C :=
            tube_ball_intersection_le4 hδ hρ hδρ T x
          exact le_trans h7 h8
        · rw [if_neg hxA]
          have h_not_thick : x ∉ cthickening ρ E := by
            intro h; exact hxA ⟨hxS, h⟩
          have h_empty : E ∩ closedBall x ρ = ∅ := by
            ext y
            simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
            intro ⟨h1, h2⟩
            have h3 : infEDist x E ≤ ENNReal.ofReal ρ := by
              have h4 : infEDist x E ≤ edist x y := Metric.infEDist_le_edist_of_mem h1
              have h5 : edist x y = ENNReal.ofReal (dist x y) := by exact edist_dist _ _
              rw [h5] at h4
              have hdist : dist x y ≤ ρ := by
                have hball : y ∈ closedBall x ρ := h2
                have h : dist y x ≤ ρ := (Metric.mem_closedBall).mp hball
                have h' : dist x y = dist y x := dist_comm x y
                rw [h']
                exact h
              have h6 : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal ρ := by
                exact (ENNReal.ofReal_le_ofReal_iff hρ.le).mpr hdist
              exact le_trans h4 h6
            have h6 : x ∈ cthickening ρ E := Metric.mem_cthickening_iff.mpr h3
            exact h_not_thick h6
          rw [h_empty]
          <;> simp
      · have h_slice : (Prod.mk x ⁻¹' R) = ∅ := by
          rw [h_slice_x x, if_neg hxS]
        rw [h_slice]
        have h_notA : x ∉ A := by
          intro h
          exact hxS h.1
        rw [if_neg h_notA] <;> simp
    have h9 : (∫⁻ (x : Point3), volume (Prod.mk x ⁻¹' R)) ≤
        ∫⁻ (x : Point3), (if x ∈ A then C else 0) := lintegral_mono h5
    have hA_meas : MeasurableSet A := hS_meas.inter (isClosed_cthickening.measurableSet)
    have h_ind2 : (fun x : Point3 => (if x ∈ A then C else 0)) =
        Set.indicator A (fun _ : Point3 => C) := by
      funext x
      simp [Set.indicator_apply]
      <;> split_ifs <;> tauto
    have h10 : (∫⁻ (x : Point3), (if x ∈ A then C else 0)) = C * volume A := by
      rw [h_ind2]
      rw [MeasureTheory.lintegral_indicator_const hA_meas C]
      <;> ring
    exact h9.trans_eq h10
  -- Combine
  have h_main : ENNReal.ofReal (1 / 8 : ℝ) * B * VE ≤
      ENNReal.ofReal (4 : ℝ) * D * ENNReal.ofReal ρ * volume A := by
    calc ENNReal.ofReal (1 / 8 : ℝ) * B * VE
      ≤ (∫⁻ (y : Point3), volume ((fun x : Point3 => (x, y)) ⁻¹' R)) := h_lower
    _ = (∫⁻ (x : Point3), volume (Prod.mk x ⁻¹' R)) := h_eq1.symm
    _ ≤ ENNReal.ofReal (4 : ℝ) * D * ENNReal.ofReal ρ * volume A := h_upper
  -- Now derive the final constant inequality
  have h_ball3 : B = ENNReal.ofReal (ρ ^ 3) * ENNReal.ofReal (Real.pi * 4 / 3) := by
    have h : volume (closedBall (0 : Point3) ρ) = ENNReal.ofReal ρ ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) :=
      EuclideanSpace.volume_closedBall_fin_three (0 : Point3) ρ
    have h_pow : ENNReal.ofReal ρ ^ 3 = ENNReal.ofReal (ρ ^ 3) := by
      rw [←ENNReal.ofReal_pow] <;> linarith
    have hB : B = volume (closedBall (0 : Point3) ρ) := by rfl
    rw [hB, h, h_pow]
  have h_tube_ρ_upper : VS ≤ ENNReal.ofReal (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := by
    have h_eq : VS = Kakeya.deltaTubeVolume ρ := by
      exact tube_volume_eq S (Kakeya.DeltaTube.mk 0 (EuclideanSpace.single 0 1) (by simp [EuclideanSpace.norm_eq] <;> norm_num))
    rw [h_eq]
    exact GeometricLemmas.capsule_volume_upper ρ hρ
  have h_ρ3_le_ρ2 : ρ ^ 3 ≤ ρ ^ 2 := by
    have h1 : 0 ≤ ρ := by linarith
    have h2 : ρ ≤ 1 := hρ1
    nlinarith
  have h_tube_ρ_better : VS ≤ ENNReal.ofReal ((11 / 3 : ℝ) * Real.pi * ρ ^ 2) := by
    have h_real : Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3 ≤ (11 / 3 : ℝ) * Real.pi * ρ ^ 2 := by
      have hρ32 : ρ ^ 3 ≤ ρ ^ 2 := by nlinarith
      have hπ : 0 < Real.pi := Real.pi_pos
      nlinarith
    calc VS
      ≤ ENNReal.ofReal (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := h_tube_ρ_upper
    _ ≤ ENNReal.ofReal ((11 / 3 : ℝ) * Real.pi * ρ ^ 2) := by
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h_real
  have hρ0 : 0 ≤ ρ := by linarith
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have h_key : B ≥ ENNReal.ofReal (8 / 25 : ℝ) * ENNReal.ofReal ρ * VS := by
    have h1 : B = ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * ρ ^ 3) := by
      rw [h_ball3]
      have hpos : 0 ≤ ρ ^ 3 := by positivity
      have h_mul : ENNReal.ofReal (ρ ^ 3) * ENNReal.ofReal (Real.pi * 4 / 3) =
          ENNReal.ofReal (ρ ^ 3 * (Real.pi * 4 / 3)) := by
        rw [ENNReal.ofReal_mul hpos]
      rw [h_mul]
      congr 1
      <;> ring
    rw [h1]
    have h_real1 : (4 / 3 : ℝ) * Real.pi * ρ ^ 3 ≥ (88 / 75 : ℝ) * Real.pi * ρ ^ 3 := by
      have h : (4 / 3 : ℝ) ≥ (88 / 75 : ℝ) := by norm_num
      have hpos : 0 ≤ Real.pi * ρ ^ 3 := by positivity
      nlinarith
    have h2 : ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * ρ ^ 3) ≥
        ENNReal.ofReal ((88 / 75 : ℝ) * Real.pi * ρ ^ 3) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h_real1
    have hpos3 : 0 ≤ (8 / 25 : ℝ) * ρ := by positivity
    have hpos4 : 0 ≤ (11 / 3 : ℝ) * Real.pi * ρ ^ 2 := by positivity
    have h3 : ENNReal.ofReal ((88 / 75 : ℝ) * Real.pi * ρ ^ 3) =
        ENNReal.ofReal ((8 / 25 : ℝ) * ρ) * ENNReal.ofReal ((11 / 3 : ℝ) * Real.pi * ρ ^ 2) := by
      have h_mul2 : (88 / 75 : ℝ) * Real.pi * ρ ^ 3 =
          ((8 / 25 : ℝ) * ρ) * ((11 / 3 : ℝ) * Real.pi * ρ ^ 2) := by ring
      rw [h_mul2]
      have hpos825 : 0 ≤ (8 / 25 : ℝ) * ρ := by positivity
      rw [ENNReal.ofReal_mul hpos825]
    have h4 : ENNReal.ofReal (8 / 25 : ℝ) * ENNReal.ofReal ρ * VS ≤
        ENNReal.ofReal ((8 / 25 : ℝ) * ρ) * ENNReal.ofReal ((11 / 3 : ℝ) * Real.pi * ρ ^ 2) := by
      have h5 : ENNReal.ofReal (8 / 25 : ℝ) * ENNReal.ofReal ρ = ENNReal.ofReal ((8 / 25 : ℝ) * ρ) := by
        have hpos8 : (0 : ℝ) ≤ (8 / 25 : ℝ) := by norm_num
        exact (ENNReal.ofReal_mul hpos8).symm
      have h6 : ENNReal.ofReal ((8 / 25 : ℝ) * ρ) * VS ≤
          ENNReal.ofReal ((8 / 25 : ℝ) * ρ) * ENNReal.ofReal ((11 / 3 : ℝ) * Real.pi * ρ ^ 2) := by
        gcongr
      calc
        ENNReal.ofReal (8 / 25 : ℝ) * ENNReal.ofReal ρ * VS
          = ENNReal.ofReal ((8 / 25 : ℝ) * ρ) * VS := by rw [h5]
        _ ≤ ENNReal.ofReal ((8 / 25 : ℝ) * ρ) * ENNReal.ofReal ((11 / 3 : ℝ) * Real.pi * ρ ^ 2) := h6
    calc ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * ρ ^ 3)
      ≥ ENNReal.ofReal ((88 / 75 : ℝ) * Real.pi * ρ ^ 3) := h2
    _ = ENNReal.ofReal ((8 / 25 : ℝ) * ρ) * ENNReal.ofReal ((11 / 3 : ℝ) * Real.pi * ρ ^ 2) := h3
    _ ≥ ENNReal.ofReal (8 / 25 : ℝ) * ENNReal.ofReal ρ * VS := h4
  -- From h_main and h_key, derive the goal
  have h_final : volume A ≥ ENNReal.ofReal (1 / 100 : ℝ) * VE / D * VS := by
    have h10 : ENNReal.ofReal (1 / 8 : ℝ) * B * VE ≤
        ENNReal.ofReal (4 : ℝ) * D * ENNReal.ofReal ρ * volume A := h_main
    have h11 : ENNReal.ofReal (1 / 8 : ℝ) * B ≥
        ENNReal.ofReal (1 / 25 : ℝ) * ENNReal.ofReal ρ * VS := by
      have h_mul1 : ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (8 / 25 : ℝ) =
          ENNReal.ofReal (1 / 25 : ℝ) := by
        have hpos18 : (0 : ℝ) ≤ (1 / 8 : ℝ) := by norm_num
        have h : ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (8 / 25 : ℝ) =
            ENNReal.ofReal ((1 / 8 : ℝ) * (8 / 25 : ℝ)) :=
          (ENNReal.ofReal_mul hpos18).symm
        rw [h]
        have h2 : (1 / 8 : ℝ) * (8 / 25 : ℝ) = (1 / 25 : ℝ) := by norm_num
        rw [h2]
      calc ENNReal.ofReal (1 / 8 : ℝ) * B
        ≥ ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal (8 / 25 : ℝ) * ENNReal.ofReal ρ * VS) := by gcongr
      _ = (ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (8 / 25 : ℝ)) * ENNReal.ofReal ρ * VS := by
        simp only [mul_assoc] <;> rfl
      _ = ENNReal.ofReal (1 / 25 : ℝ) * ENNReal.ofReal ρ * VS := by rw [h_mul1]
    have h12 : ENNReal.ofReal (1 / 25 : ℝ) * ENNReal.ofReal ρ * VS * VE ≤
        ENNReal.ofReal (4 : ℝ) * D * ENNReal.ofReal ρ * volume A := by
      have h121 : ENNReal.ofReal (1 / 25 : ℝ) * ENNReal.ofReal ρ * VS * VE ≤
          ENNReal.ofReal (1 / 8 : ℝ) * B * VE := by gcongr
      exact le_trans h121 h10
    have hρ_ne_zero : ENNReal.ofReal ρ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hρ).ne'
    have hρ_ne_top : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
    have h13 : ENNReal.ofReal (1 / 25 : ℝ) * VS * VE ≤
        ENNReal.ofReal (4 : ℝ) * D * volume A := by
      have h_rearr1 : ENNReal.ofReal (1 / 25 : ℝ) * ENNReal.ofReal ρ * VS * VE =
          (ENNReal.ofReal (1 / 25 : ℝ) * VS * VE) * ENNReal.ofReal ρ := by
        calc
          ENNReal.ofReal (1 / 25 : ℝ) * ENNReal.ofReal ρ * VS * VE
            = ENNReal.ofReal (1 / 25 : ℝ) * (ENNReal.ofReal ρ * (VS * VE)) := by simp only [mul_assoc]
          _ = ENNReal.ofReal (1 / 25 : ℝ) * ((VS * VE) * ENNReal.ofReal ρ) := by rw [mul_comm (ENNReal.ofReal ρ) (VS * VE)]
          _ = (ENNReal.ofReal (1 / 25 : ℝ) * (VS * VE)) * ENNReal.ofReal ρ := by simp only [mul_assoc]
          _ = (ENNReal.ofReal (1 / 25 : ℝ) * VS * VE) * ENNReal.ofReal ρ := by simp only [mul_assoc]
      have h_rearr2 : ENNReal.ofReal (4 : ℝ) * D * ENNReal.ofReal ρ * volume A =
          (ENNReal.ofReal (4 : ℝ) * D * volume A) * ENNReal.ofReal ρ := by
        calc
          ENNReal.ofReal (4 : ℝ) * D * ENNReal.ofReal ρ * volume A
            = ENNReal.ofReal (4 : ℝ) * D * (ENNReal.ofReal ρ * volume A) := by simp only [mul_assoc]
          _ = ENNReal.ofReal (4 : ℝ) * D * (volume A * ENNReal.ofReal ρ) := by
            have h_comm : ENNReal.ofReal ρ * volume A = volume A * ENNReal.ofReal ρ := mul_comm _ _
            rw [h_comm]
          _ = (ENNReal.ofReal (4 : ℝ) * D * volume A) * ENNReal.ofReal ρ := by simp only [mul_assoc]
      have h_div : ((ENNReal.ofReal (1 / 25 : ℝ) * VS * VE) * ENNReal.ofReal ρ) / ENNReal.ofReal ρ ≤
          ((ENNReal.ofReal (4 : ℝ) * D * volume A) * ENNReal.ofReal ρ) / ENNReal.ofReal ρ := by
        rw [←h_rearr1, ←h_rearr2]
        gcongr
      have h_left : ((ENNReal.ofReal (1 / 25 : ℝ) * VS * VE) * ENNReal.ofReal ρ) / ENNReal.ofReal ρ =
          ENNReal.ofReal (1 / 25 : ℝ) * VS * VE := by
        rw [ENNReal.mul_div_cancel_right hρ_ne_zero hρ_ne_top]
      have h_right : ((ENNReal.ofReal (4 : ℝ) * D * volume A) * ENNReal.ofReal ρ) / ENNReal.ofReal ρ =
          ENNReal.ofReal (4 : ℝ) * D * volume A := by
        rw [ENNReal.mul_div_cancel_right hρ_ne_zero hρ_ne_top]
      rw [h_left, h_right] at h_div
      exact h_div
    have hD_ne_zero : D ≠ 0 := by
      intro h
      have h_contra : ENNReal.ofReal (2 * δ ^ 2) ≤ D := tube_volume_ge_two_delta_sq δ hδ
      rw [h] at h_contra
      simpa [hδ.ne'] using h_contra
    have h4D_ne_zero : ENNReal.ofReal (4 : ℝ) * D ≠ 0 := by
      simp [hD_ne_zero]
    have h4D_ne_top : ENNReal.ofReal (4 : ℝ) * D ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD
    let X : ENNReal := ENNReal.ofReal (1 / 100 : ℝ) * VE / D * VS
    let c : ENNReal := ENNReal.ofReal (4 : ℝ) * D
    have h_D_cancel : D * (VE / D) = VE := ENNReal.mul_div_cancel hD_ne_zero hD
    have h4pos : (0 : ℝ) ≤ (4 : ℝ) := by norm_num
    have h4mul : ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (1 / 100 : ℝ) = ENNReal.ofReal (1 / 25 : ℝ) := by
      have h : ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (1 / 100 : ℝ) =
          ENNReal.ofReal ((4 : ℝ) * (1 / 100 : ℝ)) := (ENNReal.ofReal_mul h4pos).symm
      rw [h]
      have h2 : (4 : ℝ) * (1 / 100 : ℝ) = (1 / 25 : ℝ) := by norm_num
      rw [h2]
    have h_eq : c * X = ENNReal.ofReal (1 / 25 : ℝ) * VS * VE := by
      dsimp only [X, c]
      have h_step1 : (ENNReal.ofReal (4 : ℝ) * D) * (ENNReal.ofReal (1 / 100 : ℝ) * VE / D * VS) =
          ENNReal.ofReal (4 : ℝ) * (D * (VE / D)) * (ENNReal.ofReal (1 / 100 : ℝ) * VS) := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> rfl
      rw [h_step1, h_D_cancel]
      have h_step2 : ENNReal.ofReal (4 : ℝ) * VE * (ENNReal.ofReal (1 / 100 : ℝ) * VS) =
          (ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (1 / 100 : ℝ)) * VE * VS := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
      rw [h_step2, h4mul]
      have h_step3 : ENNReal.ofReal (1 / 25 : ℝ) * VE * VS =
          ENNReal.ofReal (1 / 25 : ℝ) * VS * VE := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
      exact h_step3
    have h : c * X ≤ c * volume A := by
      rw [h_eq]
      exact h13
    have h' : X * c ≤ volume A * c := by
      have h1 : c * X = X * c := mul_comm c X
      have h2 : c * volume A = volume A * c := mul_comm c (volume A)
      rw [h1, h2] at h
      exact h
    have h15 : X ≤ volume A := (ENNReal.mul_le_mul_iff_left h4D_ne_zero h4D_ne_top).mp h'
    exact h15
  exact h_final

end Kakeya.Streamlined
