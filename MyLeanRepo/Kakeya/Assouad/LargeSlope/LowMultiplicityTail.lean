import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.ExtremalInfrastructure
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.Targets.TubeVolumeScaling

/-!
# Low-multiplicity tail bound for the large-slope refinement

We prove a quadratic lower bound `deltaTubeVolume(δ) ≥ c · δ²` by inscribing
a rectangular box in the canonical tube, and deduce that the low-multiplicity
tail is at most a small power of `δ` times `F.mass`.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Local helper: product of real powers. -/
private lemma realRpowENN_mul
    {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
      Kakeya.realRpowENN delta (a + b) := by
  simp only [Kakeya.realRpowENN]
  have hreal : Real.rpow delta a * Real.rpow delta b = Real.rpow delta (a + b) :=
    (Real.rpow_add hdelta a b).symm
  have hnonneg : 0 ≤ Real.rpow delta a := Real.rpow_nonneg hdelta.le a
  have hmul : ENNReal.ofReal (Real.rpow delta a) * ENNReal.ofReal (Real.rpow delta b) =
      ENNReal.ofReal (Real.rpow delta a * Real.rpow delta b) :=
    (ENNReal.ofReal_mul hnonneg).symm
  rw [hmul, hreal]

/-- The canonical δ-tube contains a box of dimensions (1-δ) × δ × δ. -/
lemma canonical_box_subset_tube {delta : ℝ}
    (hdelta : 0 < delta) (hdelta_half : delta ≤ 1 / 2) :
    (WithLp.toLp 2) '' Set.Icc
        (fun i : Fin 3 =>
          match i with
          | 0 => delta / 2
          | 1 => -(delta / 2)
          | 2 => -(delta / 2))
        (fun i : Fin 3 =>
          match i with
          | 0 => 1 - delta / 2
          | 1 => delta / 2
          | 2 => delta / 2) ⊆
      Metric.cthickening delta
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  have hy01 : delta / 2 ≤ y 0 := (hy.1) 0
  have hy02 : y 0 ≤ 1 - delta / 2 := (hy.2) 0
  have hy1 : |y 1| ≤ delta / 2 := by
    have h1 : -(delta / 2) ≤ y 1 := (hy.1) 1
    have h2 : y 1 ≤ delta / 2 := (hy.2) 1
    exact abs_le.mpr ⟨h1, h2⟩
  have hy2 : |y 2| ≤ delta / 2 := by
    have h1 : -(delta / 2) ≤ y 2 := (hy.1) 2
    have h2 : y 2 ≤ delta / 2 := (hy.2) 2
    exact abs_le.mpr ⟨h1, h2⟩
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let p : Point3 := WithLp.toLp 2 y
  let q : Point3 := (y 0) • e0
  have hq_in : q ∈ Kakeya.unitSegment 0 e0 := by
    refine ⟨y 0, ⟨by linarith, by linarith⟩, ?_⟩
    simp [q, e0] <;> abel
  have h0 : (p - q) 0 = 0 := by simp [p, q, e0]
  have h1 : (p - q) 1 = y 1 := by simp [p, q, e0]
  have h2 : (p - q) 2 = y 2 := by simp [p, q, e0]
  have hcoord0 : (p - q).ofLp 0 = 0 := by simp [p, q, e0]
  have hcoord1 : (p - q).ofLp 1 = y 1 := by simp [p, q, e0]
  have hcoord2 : (p - q).ofLp 2 = y 2 := by simp [p, q, e0]
  have hnorm2 : ‖p - q‖ ^ 2 = ((p - q) 0)^2 + ((p - q) 1)^2 + ((p - q) 2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq (p - q)]
    simp [Fin.sum_univ_succ]
    <;> ring
  have h4 : (y 1)^2 ≤ (delta / 2)^2 := by nlinarith [abs_le.mp hy1]
  have h5 : (y 2)^2 ≤ (delta / 2)^2 := by nlinarith [abs_le.mp hy2]
  have hdist : ‖p - q‖ ≤ delta := by
    have h6 : ‖p - q‖ ^ 2 ≤ delta ^ 2 := by
      rw [hnorm2, hcoord0, hcoord1, hcoord2]
      nlinarith
    have h7 : 0 ≤ ‖p - q‖ := by positivity
    nlinarith
  exact Metric.mem_cthickening_of_dist_le p q delta _ hq_in hdist

/-- Volume of an axis-aligned box in Euclidean 3-space. -/
private lemma volume_box
    (lo hi : Fin 3 → ℝ) (hlohi : ∀ i, lo i ≤ hi i) :
    volume ((WithLp.toLp 2) '' Set.Icc lo hi) =
      ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hpreserving : MeasurePreserving toLp :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have hinjective : Function.Injective toLp := by
    intro x y hxy
    simpa [toLp, WithLp.toLp_injective] using hxy
  have hcontinuous : Continuous toLp :=
    PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
  have himage_measurable : MeasurableSet (toLp '' Set.Icc lo hi) := by
    have himage : toLp '' Set.Icc lo hi =
        (fun x : Point3 => x.ofLp) ⁻¹' Set.Icc lo hi := by
      ext y
      simp only [toLp, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [WithLp.ofLp_toLp] using hx
      · intro hy
        exact ⟨y.ofLp, hy, by simp [WithLp.ofLp_toLp]⟩
    rw [himage]
    exact (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable measurableSet_Icc
  have hvolume : volume (toLp '' Set.Icc lo hi) = volume (Set.Icc lo hi) := by
    calc
      volume (toLp '' Set.Icc lo hi)
          = Measure.map toLp volume (toLp '' Set.Icc lo hi) := by
            rw [hpreserving.map_eq]
      _ = volume (toLp ⁻¹' (toLp '' Set.Icc lo hi)) :=
        Measure.map_apply hcontinuous.measurable himage_measurable
      _ = volume (Set.Icc lo hi) := by
        rw [Set.preimage_image_eq _ hinjective]
  rw [hvolume, Real.volume_Icc_pi]
  simp [Fin.prod_univ_succ, ← ENNReal.ofReal_mul,
    sub_nonneg.mpr (hlohi 0), sub_nonneg.mpr (hlohi 1)]
  <;> ring_nf

/-- Quadratic lower bound: `deltaTubeVolume(δ) ≥ (1/2) · δ²` for `δ ≤ 1/2`. -/
lemma deltaTubeVolume_quadratic_lower {delta : ℝ}
    (hdelta : 0 < delta) (hdelta_half : delta ≤ 1 / 2) :
    Kakeya.deltaTubeVolume delta ≥
      ENNReal.ofReal ((1 / 2 : ℝ) * delta ^ 2) := by
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => delta / 2
    | 1 => -(delta / 2)
    | 2 => -(delta / 2)
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 1 - delta / 2
    | 1 => delta / 2
    | 2 => delta / 2
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i <;> dsimp [lo, hi] <;> linarith
  have hbox : (WithLp.toLp 2) '' Set.Icc lo hi ⊆
      Metric.cthickening delta
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) :=
    canonical_box_subset_tube hdelta hdelta_half
  have hvol : volume ((WithLp.toLp 2) '' Set.Icc lo hi) ≤
      Kakeya.deltaTubeVolume delta :=
    measure_mono hbox
  have hboxdim : (hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2) =
      (1 - delta) * delta ^ 2 := by
    dsimp [lo, hi]
    <;> ring
  have hboxineq : (1 / 2 : ℝ) * delta ^ 2 ≤ (hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2) := by
    rw [hboxdim]
    have h1 : 1 - delta ≥ 1 / 2 := by linarith
    nlinarith
  have hvol_eq : volume ((WithLp.toLp 2) '' Set.Icc lo hi) =
      ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) :=
    volume_box lo hi hlohi
  have hboxvol : ENNReal.ofReal ((1 / 2 : ℝ) * delta ^ 2) ≤
      volume ((WithLp.toLp 2) '' Set.Icc lo hi) := by
    rw [hvol_eq]
    exact ENNReal.ofReal_mono hboxineq
  exact hboxvol.trans hvol

/--
For sufficiently small `δ`, the low-multiplicity tail in slab `[a,b]` has
mass at most `δ^η · |𝕋|`.

The threshold is `δ^(2-σ+2η) #𝕋`, matching the lower bound of the retained
multiplicity band.
-/
lemma exists_delta_lowMultiplicityMass_le
    {sigma eta : ℝ} (heta : 0 < eta) (hsigma : 0 < sigma) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
        ∀ (F : Kakeya.Streamlined.TubeFamily delta)
          (Y : Kakeya.Streamlined.TubeShading F)
          (U : Kakeya.Streamlined.UniformTubeStructure F),
          IsExtremalPair sigma (eta / 100) F U Y →
          ∀ (a b : ℝ),
            lowMultiplicityMass Y a b
              (Kakeya.realRpowENN delta (2 - sigma + 2 * eta) * F.enncard) ≤
              Kakeya.realRpowENN delta eta * F.toBodyFamily.mass := by
  have hvol := tube_volume_scaling
  rcases hvol with ⟨h_eq, h_pos_finite, h_upper⟩

  -- We need: 2 * δ^(2η - η/100) ≤ δ^η
  -- i.e. 2 ≤ δ^(-η + η/100) = δ^(-99η/100)
  rcases exists_delta_realRpowENN_bound (2 : ENNReal)
      (by norm_num) (show 0 < (99 * eta / 100) by positivity)
    with ⟨delta₀, hdelta₀_pos, hdelta₀_one, hbound⟩

  have hmin_pos : 0 < min delta₀ (1 / 2) := by
    apply lt_min hdelta₀_pos <;> norm_num
  refine ⟨min delta₀ (1 / 2), hmin_pos, min_le_right _ _, ?_⟩
  intro delta hdelta hdelta_le
  have hdelta_le₀ : delta ≤ delta₀ :=
    hdelta_le.trans (min_le_left _ _)
  have hdelta_half : delta ≤ 1 / 2 :=
    hdelta_le.trans (min_le_right _ _)

  intro F Y U hExt a b
  set lower : ENNReal :=
    Kakeya.realRpowENN delta (2 - sigma + 2 * eta) * F.enncard with hlower_def

  -- lowTail ≤ lower * volume(Y.union)
  have h1 : lowMultiplicityMass Y a b lower ≤
      lower * MeasureTheory.volume Y.union :=
    (lowMultiplicityMass_le Y a b lower).trans
      (mul_le_mul_left' (measure_mono (Set.inter_subset_left)) lower)

  -- volume(Y.union) ≤ δ^(σ - η/100)
  have h2 : MeasureTheory.volume Y.union ≤
      Kakeya.realRpowENN delta (sigma - eta / 100) :=
    hExt.2.2.2.2.2.2.2.2.1

  let exp1 := 2 - sigma + 2 * eta
  let exp2 := sigma - eta / 100
  have hexp : exp1 + exp2 = 2 + 2 * eta - eta / 100 := by
    dsimp only [exp1, exp2] <;> ring
  have hmul : Kakeya.realRpowENN delta exp1 * Kakeya.realRpowENN delta exp2 =
      Kakeya.realRpowENN delta (exp1 + exp2) :=
    realRpowENN_mul hdelta
  have h_rearr : lower * Kakeya.realRpowENN delta exp2 =
      (Kakeya.realRpowENN delta exp1 * Kakeya.realRpowENN delta exp2) * F.enncard := by
    dsimp only [lower]
    rw [mul_assoc, mul_comm F.enncard, ←mul_assoc]
  have h3 : lower * MeasureTheory.volume Y.union ≤
      Kakeya.realRpowENN delta (2 + 2 * eta - eta / 100) * F.enncard := by
    have h : lower * MeasureTheory.volume Y.union ≤
        lower * Kakeya.realRpowENN delta exp2 := by gcongr
    rw [h_rearr] at h
    rw [hmul, hexp] at h
    exact h

  -- F.mass = F.enncard * deltaTubeVolume(delta)
  have hmass_eq : F.toBodyFamily.mass =
      F.enncard * Kakeya.deltaTubeVolume delta := by
    simp only [Kakeya.Streamlined.BodyFamily.mass,
      Kakeya.Streamlined.TubeFamily.toBodyFamily]
    have h : ∀ i : Fin F.card, (F.tube i).volume = Kakeya.deltaTubeVolume delta :=
      fun i => h_eq delta (F.tube i)
    calc
      (∑ i : Fin F.card, (F.tube i).volume)
        = ∑ i : Fin F.card, Kakeya.deltaTubeVolume delta := by
          apply Finset.sum_congr rfl
          intro i _
          exact h i
      _ = F.enncard * Kakeya.deltaTubeVolume delta := by
          simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
          <;> ring

  -- deltaTubeVolume(delta) ≥ (1/2) * delta^2
  have hVlower : Kakeya.deltaTubeVolume delta ≥
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta 2 := by
    have h : Kakeya.deltaTubeVolume delta ≥
        ENNReal.ofReal ((1 / 2 : ℝ) * delta ^ 2) :=
      deltaTubeVolume_quadratic_lower hdelta hdelta_half
    simpa [Kakeya.realRpowENN] using h

  have h4 : F.toBodyFamily.mass ≥
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta 2 * F.enncard := by
    rw [hmass_eq]
    have h : F.enncard * Kakeya.deltaTubeVolume delta ≥
        F.enncard * ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta 2) := by
      gcongr
    rw [mul_comm F.enncard ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta 2)] at h
    simpa [mul_assoc] using h

  -- 2 ≤ δ^(-99η/100)
  have h6 : (2 : ENNReal) ≤
      Kakeya.realRpowENN delta (-(99 * eta / 100)) :=
    hbound delta hdelta hdelta_le₀

  -- Key: δ^(η-η/100) ≤ 1/2, follows from 2 ≤ δ^(-99η/100)
  let expMid := eta - eta / 100
  have hexpMid : expMid = 99 * eta / 100 := by
    dsimp only [expMid] <;> ring
  have h_mul_one : Kakeya.realRpowENN delta expMid *
      Kakeya.realRpowENN delta (-expMid) = 1 := by
    rw [realRpowENN_mul hdelta]
    have h : expMid + (-expMid) = 0 := by ring
    rw [h]
    simp [Kakeya.realRpowENN]
  have h6_b : (2 : ENNReal) ≤ Kakeya.realRpowENN delta (-expMid) := by
    rw [show -expMid = -(99 * eta / 100) by { dsimp only [expMid] <;> ring }]
    exact h6
  have h_half_b : 1 ≤ Kakeya.realRpowENN delta (-expMid) * (1 / 2 : ENNReal) := by
    have h_two_half : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
      have h1 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
        simp [one_div]
      rw [h1]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      1 = (2 : ENNReal) * (1 / 2 : ENNReal) := h_two_half.symm
      _ ≤ Kakeya.realRpowENN delta (-expMid) * (1 / 2 : ENNReal) := by gcongr
  have h6' : Kakeya.realRpowENN delta expMid ≤ (1 / 2 : ENNReal) := by
    calc
      Kakeya.realRpowENN delta expMid
          = Kakeya.realRpowENN delta expMid * 1 := by simp
      _ ≤ Kakeya.realRpowENN delta expMid *
            (Kakeya.realRpowENN delta (-expMid) * (1 / 2 : ENNReal)) := by gcongr
      _ = (Kakeya.realRpowENN delta expMid * Kakeya.realRpowENN delta (-expMid)) *
            (1 / 2 : ENNReal) := by ring
      _ = (1 : ENNReal) * (1 / 2 : ENNReal) := by rw [h_mul_one] <;> ring
      _ = (1 / 2 : ENNReal) := by ring

  -- δ^(2+2η-η/100) * #T = δ^η * δ^(η-η/100) * δ² * #T
  let expTotal := 2 + 2 * eta - eta / 100
  have hexp_total : expTotal = eta + expMid + 2 := by
    dsimp only [expTotal, expMid] <;> ring
  have hpow_decomp : Kakeya.realRpowENN delta expTotal =
      Kakeya.realRpowENN delta eta * Kakeya.realRpowENN delta expMid *
      Kakeya.realRpowENN delta 2 := by
    have h1 : Kakeya.realRpowENN delta (eta + expMid) =
        Kakeya.realRpowENN delta eta * Kakeya.realRpowENN delta expMid :=
      (realRpowENN_mul hdelta).symm
    have h2 : Kakeya.realRpowENN delta ((eta + expMid) + 2) =
        Kakeya.realRpowENN delta (eta + expMid) * Kakeya.realRpowENN delta 2 :=
      (realRpowENN_mul hdelta).symm
    have h3 : expTotal = (eta + expMid) + 2 := by
      dsimp only [expTotal, expMid] <;> ring
    rw [h3, h2, h1] <;> ring

  -- δ^(2+2η-η/100) * #T ≤ δ^η * F.mass
  have h7 : Kakeya.realRpowENN delta expTotal * F.enncard ≤
      Kakeya.realRpowENN delta eta * F.toBodyFamily.mass := by
    calc
      Kakeya.realRpowENN delta expTotal * F.enncard
          = (Kakeya.realRpowENN delta eta * Kakeya.realRpowENN delta expMid *
              Kakeya.realRpowENN delta 2) * F.enncard := by rw [hpow_decomp]
      _ = Kakeya.realRpowENN delta eta *
            (Kakeya.realRpowENN delta expMid * Kakeya.realRpowENN delta 2 * F.enncard) := by ring
      _ ≤ Kakeya.realRpowENN delta eta *
            ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta 2 * F.enncard) := by
              gcongr
      _ ≤ Kakeya.realRpowENN delta eta * F.toBodyFamily.mass := by gcongr

  exact h1.trans (h3.trans h7)

end Kakeya.Assouad
