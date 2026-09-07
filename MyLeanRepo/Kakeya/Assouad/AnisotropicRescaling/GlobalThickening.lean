import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescalingGeometry


/-!
Global thickening containment: U ⊆ cthickening (20*rho) B
and slicewise containment.
-/

noncomputable section

open MeasureTheory Set Metric

namespace Kakeya.Assouad

/-- |f z| ≤ 2 for z ∈ [-1,1]. -/
private lemma f_bound_two {f : SlopeFunction}
    (hf_nonsing : f.IsNonsingular) (hf_zero : f 0 = 0)
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) : |f z| ≤ 2 := by
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |deriv f x| ≤ 2 :=
    fun x hx => (hf_nonsing x hx).2.1
  have hdiff : Differentiable ℝ f := f.contDiff.differentiable (by norm_num)
  have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have h : |f z - f 0| ≤ 2 * |z - 0| :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hdiff.differentiableAt)
      hderiv (convex_Icc (-1 : ℝ) 1) h0 hz
  have h' : |f z| ≤ 2 * |z| := by
    simpa [hf_zero] using h
  have hz' : |z| ≤ 1 := abs_le.mpr ⟨hz.1, hz.2⟩
  have h'' : 2 * |z| ≤ 2 := by
    calc 2 * |z| ≤ 2 * 1 := by gcongr
      _ = 2 := by norm_num
  linarith

/-- |f z - f w| ≤ 2 * |z - w| for z,w ∈ [-1,1]. -/
private lemma f'_bound_two {f : SlopeFunction}
    (hf_nonsing : f.IsNonsingular)
    {z w : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hw : w ∈ Set.Icc (-1 : ℝ) 1) :
    |f z - f w| ≤ 2 * |z - w| := by
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |deriv f x| ≤ 2 :=
    fun x hx => (hf_nonsing x hx).2.1
  have hdiff : Differentiable ℝ f := f.contDiff.differentiable (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hdiff.differentiableAt)
    hderiv (convex_Icc (-1 : ℝ) 1) hw hz

/-- Coordinate bound: |p i| ≤ ‖p‖ for EuclideanSpace. -/
private lemma coord_le_norm {n : ℕ} {p : EuclideanSpace ℝ (Fin n)} {i : Fin n} :
    |p i| ≤ ‖p‖ := by
  have h : (p i)^2 ≤ ∑ j : Fin n, (p j)^2 := by
    apply Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  have hsq : (|p i|)^2 ≤ ∑ j : Fin n, (p j)^2 := by
    simpa [sq_abs] using h
  have h2 : |p i| ≤ Real.sqrt (∑ j : Fin n, (p j)^2) := by
    have h3 : Real.sqrt ((|p i|)^2) ≤ Real.sqrt (∑ j : Fin n, (p j)^2) :=
      Real.sqrt_le_sqrt hsq
    have h4 : Real.sqrt ((|p i|)^2) = |p i| := by
      rw [Real.sqrt_sq] <;> exact abs_nonneg _
    rw [h4] at h3
    exact h3
  simpa [EuclideanSpace.norm_eq] using h2

/-- Triangle inequality for real absolute values. -/
private lemma abs_triangle {a b : ℝ} : |a + b| ≤ |a| + |b| := by
  have h1 : a ≤ |a| := le_abs_self a
  have h2 : b ≤ |b| := le_abs_self b
  have h3 : -a ≤ |a| := by
    by_cases h : 0 ≤ a
    · rw [abs_of_nonneg h] <;> linarith
    · rw [abs_of_neg (by linarith)] <;> linarith
  have h4 : -b ≤ |b| := by
    by_cases h : 0 ≤ b
    · rw [abs_of_nonneg h] <;> linarith
    · rw [abs_of_neg (by linarith)] <;> linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Horizontal displacement bound for twistedProjection. -/
lemma twistedProjection_horizontal_displacement
    {f : SlopeFunction} (hf_nonsing : f.IsNonsingular) (hf_zero : f 0 = 0)
    {p q : Point3} (hp1 : |p 1| ≤ 6) (hq1 : |q 1| ≤ 6)
    (hp2 : p 2 ∈ Set.Icc (-1 : ℝ) 1) (hq2 : q 2 ∈ Set.Icc (-1 : ℝ) 1) :
    |(p 0 + f (p 2) * p 1) - (q 0 + f (q 2) * q 1)| ≤ 15 * dist p q := by
  have hf2 : |f (p 2)| ≤ 2 := f_bound_two hf_nonsing hf_zero hp2
  have hfdiff : |f (p 2) - f (q 2)| ≤ 2 * |p 2 - q 2| :=
    f'_bound_two hf_nonsing hp2 hq2
  have h0 : |p 0 - q 0| ≤ dist p q := by
    simpa [dist_eq_norm] using @coord_le_norm 3 (p - q) 0
  have h1 : |p 1 - q 1| ≤ dist p q := by
    simpa [dist_eq_norm] using @coord_le_norm 3 (p - q) 1
  have h2 : |p 2 - q 2| ≤ dist p q := by
    simpa [dist_eq_norm] using @coord_le_norm 3 (p - q) 2
  have h3 : |f (p 2) * p 1 - f (q 2) * q 1| ≤
      |f (p 2)| * |p 1 - q 1| + |f (p 2) - f (q 2)| * |q 1| := by
    calc
      |f (p 2) * p 1 - f (q 2) * q 1|
        = |f (p 2) * (p 1 - q 1) + (f (p 2) - f (q 2)) * q 1| := by ring_nf
      _ ≤ |f (p 2)| * |p 1 - q 1| + |f (p 2) - f (q 2)| * |q 1| := by
          have h : |(f (p 2) * (p 1 - q 1) : ℝ) + ((f (p 2) - f (q 2)) * q 1 : ℝ)| ≤
              |(f (p 2) * (p 1 - q 1) : ℝ)| +
                |((f (p 2) - f (q 2)) * q 1 : ℝ)| :=
            abs_add_le _ _
          simpa [abs_mul] using h
  calc
    |(p 0 + f (p 2) * p 1) - (q 0 + f (q 2) * q 1)|
      ≤ |p 0 - q 0| + |f (p 2) * p 1 - f (q 2) * q 1| := by
        have h : (p 0 + f (p 2) * p 1) - (q 0 + f (q 2) * q 1) =
            (p 0 - q 0) + (f (p 2) * p 1 - f (q 2) * q 1) := by ring
        rw [h]
        exact abs_add_le _ _
    _ ≤ |p 0 - q 0| + (|f (p 2)| * |p 1 - q 1| + |f (p 2) - f (q 2)| * |q 1|) := by
        gcongr
    _ = |p 0 - q 0| + |f (p 2)| * |p 1 - q 1| + |f (p 2) - f (q 2)| * |q 1| := by ring
    _ ≤ dist p q + 2 * dist p q + 2 * dist p q * 6 := by
        have h4 : |p 0 - q 0| ≤ dist p q := h0
        have h5 : |f (p 2)| * |p 1 - q 1| ≤ 2 * dist p q := by
          calc |f (p 2)| * |p 1 - q 1| ≤ 2 * |p 1 - q 1| := by gcongr
            _ ≤ 2 * dist p q := by gcongr
        have h6 : |f (p 2) - f (q 2)| * |q 1| ≤ 2 * dist p q * 6 := by
          calc |f (p 2) - f (q 2)| * |q 1|
              ≤ 2 * |p 2 - q 2| * |q 1| := by gcongr
            _ ≤ 2 * dist p q * 6 := by gcongr <;> linarith
        linarith
    _ = 15 * dist p q := by ring

/-- A point in a target tube carrier has norm ≤ 5. -/
private lemma target_point_norm_le_five
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily rho}
    (hbb : HasBoundedBase F 3)
    {j : Fin F.card} {q : Point3}
    (hq : q ∈ (F.tube j).carrier) : ‖q‖ ≤ 5 := by
  have hbase : ‖(F.tube j).base‖ ≤ 3 := hbb j
  have hdir : ‖(F.tube j).direction‖ = 1 := (F.tube j).direction_unit
  have hcarrier : (F.tube j).carrier =
      Metric.cthickening rho (Kakeya.unitSegment (F.tube j).base (F.tube j).direction) := by
    rfl
  have hseg_compact : IsCompact (Kakeya.unitSegment (F.tube j).base (F.tube j).direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have h_eq : Metric.cthickening rho (Kakeya.unitSegment (F.tube j).base (F.tube j).direction) =
      ⋃ a ∈ (Kakeya.unitSegment (F.tube j).base (F.tube j).direction), Metric.closedBall a rho :=
    hseg_compact.cthickening_eq_biUnion_closedBall hrho.le
  rw [hcarrier, h_eq] at hq
  rcases Set.mem_iUnion₂.mp hq with ⟨a, ha, hqa⟩
  have hda : dist q a ≤ rho := by
    simpa [Metric.mem_closedBall] using hqa
  have h7 : ∃ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 ∧ (F.tube j).base + s • (F.tube j).direction = a := by
    simpa [Kakeya.unitSegment, Set.mem_image] using ha
  rcases h7 with ⟨s, hs, h_eq⟩
  have hnorm : ‖a‖ ≤ 4 := by
    rw [←h_eq]
    have h1 : ‖(F.tube j).base + s • (F.tube j).direction‖ ≤
        ‖(F.tube j).base‖ + ‖s • (F.tube j).direction‖ := norm_add_le _ _
    have h2 : ‖s • (F.tube j).direction‖ = |s| * ‖(F.tube j).direction‖ := by
      rw [norm_smul]
      <;> simp [Real.norm_eq_abs]
    rw [h2] at h1
    have h3 : |s| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    calc
      _ ≤ ‖(F.tube j).base‖ + |s| * ‖(F.tube j).direction‖ := h1
      _ ≤ 3 + 1 * 1 := by gcongr <;> linarith
      _ = 4 := by norm_num
  have hq1 : ‖q‖ ≤ ‖q - a‖ + ‖a‖ := by
    simpa [sub_add_cancel] using norm_add_le (q - a) a
  have hdist : ‖q - a‖ = dist q a := by rfl
  have h4 : ‖q‖ ≤ rho + 4 := by
    calc
      ‖q‖ ≤ ‖q - a‖ + ‖a‖ := hq1
      _ = dist q a + ‖a‖ := by rw [hdist]
      _ ≤ rho + 4 := by gcongr <;> linarith [hnorm]
  have h6 : rho + 4 ≤ 5 := by linarith [hrho_one]
  linarith

/--
Global containment: twistedUnion cleaned.shading f ⊆ cthickening (20*rho) B.
-/
lemma twisted_union_global_thickening
    {sigma delta rho c d m : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal} {G : C2GrainStructure Y sigma C}
    {cleaned : CleanedAnisotropicTarget (rho := rho) (c := c) (d := d) (m := m) F Y G.slope}
    {f : SlopeFunction}
    (hf_nonsing : f.IsNonsingular) (hf_zero : f 0 = 0)
    (hrho_one : rho ≤ 1) (hrho : 0 < rho)
    (hcd : c < d) (hm_pos : 0 < m)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1) :
    twistedUnion cleaned.shading f ⊆
      cthickening (20 * rho)
        (twistedProjection f ''
          (anisotropicRescalingMap G.slope c d m '' (Y.union ∩ horizontalSlab c d))) := by
  set Φ := anisotropicRescalingMap G.slope c d m with hΦ
  set S := Y.union ∩ horizontalSlab c d with hS
  set B := twistedProjection f '' (Φ '' S) with hB
  have h1 : cleaned.shading.union ⊆ cthickening rho (Φ '' S) := by
    intro x hx
    have h2 : ∃ j, x ∈ cleaned.shading.carrier j := by
      simpa [Kakeya.Streamlined.Shading.union] using hx
    rcases h2 with ⟨j, hj⟩
    let i := cleaned.sourceParent j
    have h3 : cleaned.shading.carrier j ⊆
        cthickening rho (Φ '' (Y.carrier i ∩ horizontalSlab c d)) :=
      cleaned.localCarrier j
    have h4 : Y.carrier i ∩ horizontalSlab c d ⊆ S := by
      intro p hp
      exact ⟨⟨i, hp.1⟩, hp.2⟩
    have h5 : Φ '' (Y.carrier i ∩ horizontalSlab c d) ⊆ Φ '' S := by
      intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      exact Set.mem_image_of_mem Φ (h4 ha)
    have h6 : cthickening rho (Φ '' (Y.carrier i ∩ horizontalSlab c d)) ⊆
        cthickening rho (Φ '' S) := by
      intro x hx
      have h7 : infEDist x (Φ '' (Y.carrier i ∩ horizontalSlab c d)) ≤ ENNReal.ofReal rho := hx
      have h8 : infEDist x (Φ '' S) ≤ infEDist x (Φ '' (Y.carrier i ∩ horizontalSlab c d)) :=
        Metric.infEDist_anti h5
      exact le_trans h8 h7
    exact h6 (h3 hj)
  have hslope : cleaned.shading.union ⊆ horizontalSlab (-1) 1 := cleaned.slopeWindow
  intro z hz
  rcases hz with ⟨q, hq, rfl⟩
  -- Bounds on q
  have hq2 : q 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have h : q ∈ horizontalSlab (-1) 1 := hslope hq
    simpa [horizontalSlab] using h
  have hq1 : |q 1| ≤ 6 := by
    have h2 : ∃ j, q ∈ cleaned.shading.carrier j := by
      simpa [Kakeya.Streamlined.Shading.union] using hq
    rcases h2 with ⟨j, hj⟩
    have htube : q ∈ (cleaned.family.tube j).carrier :=
      cleaned.shading.subset_body j hj
    have h : ‖q‖ ≤ 5 := target_point_norm_le_five hrho hrho_one cleaned.boundedBase htube
    have h' : |q 1| ≤ ‖q‖ := coord_le_norm
    linarith
  have hq_norm : ‖q‖ ≤ 5 := by
    have h2 : ∃ j, q ∈ cleaned.shading.carrier j := by
      simpa [Kakeya.Streamlined.Shading.union] using hq
    rcases h2 with ⟨j, hj⟩
    have htube : q ∈ (cleaned.family.tube j).carrier :=
      cleaned.shading.subset_body j hj
    exact target_point_norm_le_five hrho hrho_one cleaned.boundedBase htube
  -- q is in cthickening of Φ '' S
  have h_q_in : q ∈ cthickening rho (Φ '' S) := h1 hq
  have h_inf_le : infEDist q (Φ '' S) ≤ ENNReal.ofReal rho := h_q_in
  -- Helper: bounds on any y ∈ Φ '' S
  have h_y_bounds : ∀ (y : Point3), y ∈ Φ '' S →
      (y 2 ∈ Set.Icc (-1 : ℝ) 1) ∧ (‖y‖ ≤ ‖q‖ + dist q y) := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    have hps : p 2 ∈ Set.Icc c d := by
      have h : p ∈ horizontalSlab c d := hp.2
      simpa [horizontalSlab] using h
    have h_vert : (Φ p) 2 = 2 * (p 2 - c) / (d - c) - 1 := by
      simp [Φ, anisotropicRescalingMap, point3, EuclideanSpace.single_apply] <;> ring
    have h_y2 : (Φ p) 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [h_vert]
      have hcd_pos : 0 < d - c := by linarith
      have h1 : c ≤ p 2 := hps.1
      have h2 : p 2 ≤ d := hps.2
      have h3 : 0 ≤ 2 * (p 2 - c) / (d - c) := by
        apply div_nonneg
        · linarith
        · linarith
      have h4 : 2 * (p 2 - c) / (d - c) ≤ 2 := by
        calc
          2 * (p 2 - c) / (d - c) ≤ 2 * (d - c) / (d - c) := by gcongr
          _ = 2 := by
            field_simp [hcd_pos.ne'] <;> ring
      exact ⟨by linarith [h3], by linarith [h4]⟩
    have h_norm : ‖Φ p‖ ≤ ‖q‖ + dist q (Φ p) := by
      have h_eq : q + (Φ p - q) = Φ p := by
        simp [sub_eq_add_neg, add_assoc]
        <;> abel
      have h2 : ‖q + (Φ p - q)‖ ≤ ‖q‖ + ‖Φ p - q‖ := norm_add_le q (Φ p - q)
      have h3 : ‖Φ p - q‖ = dist q (Φ p) := by
        have h4 : dist q (Φ p) = ‖q - Φ p‖ := by rfl
        have h5 : ‖Φ p - q‖ = ‖q - Φ p‖ := norm_sub_rev (Φ p) q
        rw [h4, ←h5]
      rw [h3] at h2
      have h6 : ‖Φ p‖ = ‖q + (Φ p - q)‖ := by rw [h_eq]
      rw [h6]
      exact h2
    exact ⟨h_y2, h_norm⟩
  -- For any 0 < ε < 1, find approximate witness and bound displacement
  have h_eps : ∀ (ε : ℝ), 0 < ε → ε < 1 →
      infEDist (twistedProjection f q) B < ENNReal.ofReal (20 * (rho + ε)) := by
    intro ε hε hε1
    have h9 : ENNReal.ofReal rho < ENNReal.ofReal (rho + ε) := by
      have hpos : 0 < rho + ε := by linarith
      exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)
    have h10 : infEDist q (Φ '' S) < ENNReal.ofReal (rho + ε) :=
      lt_of_le_of_lt h_inf_le h9
    have hS_nonempty : (Φ '' S).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h] at h_q_in
      simpa [cthickening] using h_q_in
    have h11 : ∃ (y : Point3), y ∈ Φ '' S ∧ edist q y < ENNReal.ofReal (rho + ε) := by
      have h10' : infEDist q (Φ '' S) < ENNReal.ofReal (rho + ε) := h10
      have h_iff : ∃ (y : Point3), y ∈ Φ '' S ∧ edist q y < ENNReal.ofReal (rho + ε) :=
        Metric.infEDist_lt_iff.mp h10'
      exact h_iff
    rcases h11 with ⟨y, hy, h12⟩
    have h13 : dist q y < rho + ε := by
      have h_eq : edist q y = ENNReal.ofReal (dist q y) := edist_dist q y
      rw [h_eq] at h12
      have hpos : 0 ≤ dist q y := by positivity
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos).mp h12
    have h_y2 : y 2 ∈ Set.Icc (-1 : ℝ) 1 := (h_y_bounds y hy).1
    have h_y_norm : ‖y‖ ≤ ‖q‖ + dist q y := (h_y_bounds y hy).2
    have h_y1 : |y 1| ≤ 6 + ε := by
      have h1 : |y 1| ≤ ‖y‖ := coord_le_norm
      have h2 : ‖y‖ < 6 + ε := by linarith [hq_norm, h13]
      linarith
    -- Horizontal displacement bound with |y 1| ≤ 6 + ε
    have h_horiz : |(twistedProjection f q) 0 - (twistedProjection f y) 0| ≤
        (15 + 2 * ε) * dist q y := by
      have hf2 : |f (q 2)| ≤ 2 := f_bound_two hf_nonsing hf_zero hq2
      have hfdiff : |f (q 2) - f (y 2)| ≤ 2 * |q 2 - y 2| :=
        f'_bound_two hf_nonsing hq2 h_y2
      have h0 : |q 0 - y 0| ≤ dist q y := by
        simpa [dist_eq_norm] using @coord_le_norm 3 (q - y) 0
      have h1 : |q 1 - y 1| ≤ dist q y := by
        simpa [dist_eq_norm] using @coord_le_norm 3 (q - y) 1
      have h2 : |q 2 - y 2| ≤ dist q y := by
        simpa [dist_eq_norm] using @coord_le_norm 3 (q - y) 2
      have h3 : |f (q 2) * q 1 - f (y 2) * y 1| ≤
          |f (q 2)| * |q 1 - y 1| + |f (q 2) - f (y 2)| * |y 1| := by
        have h4 : f (q 2) * q 1 - f (y 2) * y 1 =
            f (q 2) * (q 1 - y 1) + (f (q 2) - f (y 2)) * y 1 := by ring
        rw [h4]
        have h5 : |(f (q 2) * (q 1 - y 1) : ℝ) + ((f (q 2) - f (y 2)) * y 1 : ℝ)| ≤
            |f (q 2) * (q 1 - y 1)| + |(f (q 2) - f (y 2)) * y 1| := by
          exact abs_triangle
        simpa [abs_mul] using h5
      calc
        |(twistedProjection f q) 0 - (twistedProjection f y) 0|
          = |(q 0 + f (q 2) * q 1) - (y 0 + f (y 2) * y 1)| := by
            simp [twistedProjection] <;> ring
        _ ≤ |q 0 - y 0| + |f (q 2) * q 1 - f (y 2) * y 1| := by
          have h : (q 0 + f (q 2) * q 1) - (y 0 + f (y 2) * y 1) =
              (q 0 - y 0) + (f (q 2) * q 1 - f (y 2) * y 1) := by ring
          rw [h]
          exact abs_triangle
        _ ≤ |q 0 - y 0| + |f (q 2)| * |q 1 - y 1| + |f (q 2) - f (y 2)| * |y 1| := by linarith
        _ ≤ dist q y + 2 * dist q y + 2 * dist q y * (6 + ε) := by
          gcongr <;> linarith
        _ = (15 + 2 * ε) * dist q y := by ring
    -- Vertical displacement
    have h_vert : |(twistedProjection f q) 1 - (twistedProjection f y) 1| ≤ dist q y := by
      have h21 : (twistedProjection f q) 1 = q 2 := by simp [twistedProjection]
      have h22 : (twistedProjection f y) 1 = y 2 := by simp [twistedProjection]
      rw [h21, h22]
      simpa [dist_eq_norm] using @coord_le_norm 3 (q - y) 2
    -- Total L2 bound
    set a := twistedProjection f q with ha
    set b := twistedProjection f y with hb
    have h_dist2 : dist a b ^ 2 = |a 0 - b 0| ^ 2 + |a 1 - b 1| ^ 2 := by
      have h : dist a b = ‖a - b‖ := by rfl
      rw [h]
      have h_nonneg : 0 ≤ ∑ i : Fin 2, (a - b) i ^ 2 := by positivity
      have h_norm_sq : ‖a - b‖ ^ 2 = ∑ i : Fin 2, (a - b) i ^ 2 := by
        rw [EuclideanSpace.norm_eq]
        have h2 : (Real.sqrt (∑ i : Fin 2, ‖(a - b) i‖ ^ 2)) ^ 2 = ∑ i : Fin 2, ‖(a - b) i‖ ^ 2 := by
          rw [Real.sq_sqrt] <;> positivity
        rw [h2]
        have h3 : ∑ i : Fin 2, ‖(a - b) i‖ ^ 2 = ∑ i : Fin 2, (a - b) i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          have h4 : ‖(a - b) i‖ = |(a - b) i| := by simp
          have h5 : ‖(a - b) i‖ ^ 2 = (a - b) i ^ 2 := by
            rw [h4, sq_abs]
          exact h5
        exact h3
      rw [h_norm_sq]
      have hsum : ∑ i : Fin 2, (a - b) i ^ 2 = (a - b) 0 ^ 2 + (a - b) 1 ^ 2 := by
        simp [Fin.sum_univ_two] <;> ring
      rw [hsum]
      have h0 : |a 0 - b 0| ^ 2 = (a - b) 0 ^ 2 := by simp [abs_pow]
      have h1 : |a 1 - b 1| ^ 2 = (a - b) 1 ^ 2 := by simp [abs_pow]
      rw [h0, h1] <;> ring
    have h_total : dist a b ≤ 20 * dist q y := by
      have h4 : dist a b ^ 2 ≤ (20 * dist q y) ^ 2 := by
        rw [h_dist2]
        have h5 : |a 0 - b 0| ≤ (15 + 2 * ε) * dist q y := h_horiz
        have h6 : |a 1 - b 1| ≤ dist q y := h_vert
        have h7 : |a 0 - b 0| ^ 2 ≤ ((15 + 2 * ε) * dist q y) ^ 2 := by
          gcongr <;> linarith
        have h8 : |a 1 - b 1| ^ 2 ≤ (dist q y) ^ 2 := by gcongr <;> linarith
        have h9 : ((15 + 2 * ε) * dist q y) ^ 2 + (dist q y) ^ 2 ≤ (20 * dist q y) ^ 2 := by
          have h10 : 0 ≤ dist q y := by positivity
          have h11 : (15 + 2 * ε) ^ 2 + 1 ≤ 20 ^ 2 := by
            have h12 : 15 + 2 * ε < 17 := by linarith
            have h13 : 0 ≤ 15 + 2 * ε := by linarith
            nlinarith
          have h14 : ((15 + 2 * ε) ^ 2 + 1) * (dist q y) ^ 2 ≤ (20 ^ 2) * (dist q y) ^ 2 := by
            gcongr <;> linarith
          have h15 : ((15 + 2 * ε) * dist q y) ^ 2 + (dist q y) ^ 2 =
              ((15 + 2 * ε) ^ 2 + 1) * (dist q y) ^ 2 := by ring
          have h16 : (20 * dist q y) ^ 2 = (20 ^ 2) * (dist q y) ^ 2 := by ring
          rw [h15, h16]
          exact h14
        linarith
      have h5 : 0 ≤ dist a b := by positivity
      have h6 : 0 ≤ 20 * dist q y := by positivity
      nlinarith
    have h14 : dist a b < 20 * (rho + ε) := by
      calc
        dist a b ≤ 20 * dist q y := h_total
        _ < 20 * (rho + ε) := by gcongr <;> linarith
    have h15 : b ∈ B := Set.mem_image_of_mem (twistedProjection f) hy
    have h16 : infEDist a B ≤ edist a b := Metric.infEDist_le_edist_of_mem h15
    have h17 : edist a b = ENNReal.ofReal (dist a b) := edist_dist a b
    rw [h17] at h16
    have h18 : ENNReal.ofReal (dist a b) < ENNReal.ofReal (20 * (rho + ε)) := by
      have hpos1 : 0 ≤ dist a b := by positivity
      have hpos2 : 0 ≤ 20 * (rho + ε) := by positivity
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith)
    exact lt_of_le_of_lt h16 h18
  -- Limiting argument: if infEDist < ENNReal.ofReal (20 * (rho + ε)) for all ε > 0,
  -- then infEDist ≤ ENNReal.ofReal (20 * rho)
  have h_final : infEDist (twistedProjection f q) B ≤ ENNReal.ofReal (20 * rho) := by
    by_contra h
    have h' : ENNReal.ofReal (20 * rho) < infEDist (twistedProjection f q) B := by
      exact lt_of_not_ge h
    rcases ENNReal.lt_iff_exists_real_btwn.mp h' with ⟨r, hr_nonneg, hr1, hr2⟩
    have hr_pos : 0 < r := by
      have h : 0 ≤ r := hr_nonneg
      have h' : 0 < 20 * rho := by positivity
      have h'' : 20 * rho < r := by
        have hlt : ENNReal.ofReal (20 * rho) < ENNReal.ofReal r := hr1
        have hpos : 0 ≤ 20 * rho := by positivity
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos).mp hlt
      linarith
    have h_rho_lt_r : 20 * rho < r := by
      have hlt : ENNReal.ofReal (20 * rho) < ENNReal.ofReal r := hr1
      have hpos : 0 ≤ 20 * rho := by positivity
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos).mp hlt
    set ε : ℝ := min ((r - 20 * rho) / 40) (1 / 2) with hε_def
    have hε_pos : 0 < ε := by
      apply lt_min
      · linarith
      · norm_num
    have hε_lt_one : ε < 1 := by
      have h : ε ≤ 1 / 2 := min_le_right _ _
      linarith
    have h_bound : 20 * (rho + ε) < r := by
      have h1 : ε ≤ (r - 20 * rho) / 40 := min_le_left _ _
      linarith
    have h_contra := h_eps ε hε_pos hε_lt_one
    have h19 : ENNReal.ofReal (20 * (rho + ε)) < ENNReal.ofReal r := by
      have hpos : 0 ≤ 20 * (rho + ε) := by positivity
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos).mpr h_bound
    have h20 : infEDist (twistedProjection f q) B < ENNReal.ofReal r :=
      lt_trans h_contra h19
    exact not_le.mpr h20 (le_of_lt hr2)
  exact h_final

end Kakeya.Assouad
