import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeReversal
import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Four-tube envelope geometry

The union of four consecutive unit tubes on the same axis is the closed
thickening of a length-4 segment, hence convex.  It is comparable to an
axis-aligned box of dimensions `rho × rho × 4` up to factor 3.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Four consecutive unit segments union to the length-4 segment. -/
lemma four_unit_segments_union (base direction : Point3) :
    Kakeya.unitSegment (base + (-2 : ℝ) • direction) direction ∪
    Kakeya.unitSegment (base + (-1 : ℝ) • direction) direction ∪
    Kakeya.unitSegment base direction ∪
    Kakeya.unitSegment (base + direction) direction =
    (fun t : ℝ => base + t • direction) '' Set.Icc (-2) 2 := by
  have h1 : ∀ (a : ℝ), Kakeya.unitSegment (base + a • direction) direction =
      (fun t : ℝ => base + t • direction) '' Set.Icc a (a + 1) := by
    intro a
    ext p
    simp only [Kakeya.unitSegment, Set.mem_image]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      refine ⟨a + t, ⟨by linarith, by linarith⟩, ?_⟩
      have h : (base + a • direction) + t • direction = base + (a + t) • direction := by
        rw [add_smul] <;> abel
      exact h.symm
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      refine ⟨t - a, ⟨by linarith, by linarith⟩, ?_⟩
      have h2 : a • direction + (t - a) • direction = t • direction := by
        rw [← add_smul] <;> abel
      have h : (base + a • direction) + (t - a) • direction = base + t • direction := by
        calc
          (base + a • direction) + (t - a) • direction
            = base + (a • direction + (t - a) • direction) := by abel
          _ = base + t • direction := by rw [h2]
      exact h
  let f : ℝ → Point3 := fun t => base + t • direction
  have h_sub1 : Set.Icc (-2 : ℝ) (-1) ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h_sub2 : Set.Icc (-1 : ℝ) 0 ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h_sub3 : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h_sub4 : Set.Icc (1 : ℝ) 2 ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h2 : Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc (-1 : ℝ) 0 ∪
           Set.Icc (0 : ℝ) 1 ∪ Set.Icc (1 : ℝ) 2 = Set.Icc (-2 : ℝ) 2 := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (Set.union_subset (Set.union_subset h_sub1 h_sub2) h_sub3) h_sub4
    · intro x hx
      have hlo : -2 ≤ x := hx.1
      have hhi : x ≤ 2 := hx.2
      by_cases h1 : x ≤ -1
      · exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ⟨by linarith, by linarith⟩))
      · by_cases h2 : x ≤ 0
        · exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨by linarith, by linarith⟩))
        · by_cases h3 : x ≤ 1
          · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨by linarith, by linarith⟩)
          · exact Set.mem_union_right _ ⟨by linarith, by linarith⟩
  have h10 : Kakeya.unitSegment (base + (-2 : ℝ) • direction) direction =
      f '' Set.Icc (-2) (-1) := by
    convert h1 (-2) using 2 <;> norm_num
  have h11 : Kakeya.unitSegment (base + (-1 : ℝ) • direction) direction =
      f '' Set.Icc (-1) 0 := by
    convert h1 (-1) using 2 <;> norm_num
  have h12 : Kakeya.unitSegment base direction =
      f '' Set.Icc 0 1 := by
    have h := h1 0
    have h_zero : base + (0 : ℝ) • direction = base := by simp
    rw [h_zero] at h
    convert h using 2 <;> norm_num
  have h13 : Kakeya.unitSegment (base + direction) direction =
      f '' Set.Icc 1 2 := by
    have h13_raw : Kakeya.unitSegment (base + (1 : ℝ) • direction) direction =
        f '' Set.Icc 1 (1 + 1) := h1 1
    have h_base : base + (1 : ℝ) • direction = base + direction := by simp
    rw [h_base] at h13_raw
    convert h13_raw using 2 <;> norm_num
  calc
    _ = f '' Set.Icc (-2) (-1) ∪ f '' Set.Icc (-1) 0 ∪
        f '' Set.Icc 0 1 ∪ f '' Set.Icc 1 2 := by
          rw [h10, h11, h12, h13]
    _ = f '' (Set.Icc (-2) (-1) ∪ Set.Icc (-1) 0 ∪
             Set.Icc 0 1 ∪ Set.Icc 1 2) := by
          rw [← Set.image_union, ← Set.image_union, ← Set.image_union]
    _ = f '' Set.Icc (-2) 2 := by rw [h2]

lemma four_tube_envelope_geometry
    (base direction : Point3) (hdir : ‖direction‖ = 1)
    (rho : ℝ) (hrho_pos : 0 < rho) (hrho_small : rho ≤ 1 / 8) :
    ∃ envelope : Kakeya.Streamlined.Body,
      envelope.carrier =
        (let T0 : Kakeya.DeltaTube rho :=
           ⟨base + (-2 : ℝ) • direction, direction, hdir⟩
         let C0 := reverseTube T0
         let P1 : Kakeya.DeltaTube rho :=
           ⟨base + (-1 : ℝ) • direction, direction, hdir⟩
         let P2 : Kakeya.DeltaTube rho :=
           ⟨base, direction, hdir⟩
         let P3 : Kakeya.DeltaTube rho :=
           ⟨base + direction, direction, hdir⟩
         C0.carrier ∪ P1.carrier ∪ P2.carrier ∪ P3.carrier) ∧
      envelope.IsMeasurable ∧
      envelope.IsConvex ∧
      envelope.HasDimensions rho rho 4 3 := by
  let fullSegment : Set Point3 :=
    (fun t : ℝ => base + t • direction) '' Set.Icc (-2) 2
  let seg0 := Kakeya.unitSegment (base + (-2 : ℝ) • direction) direction
  let seg1 := Kakeya.unitSegment (base + (-1 : ℝ) • direction) direction
  let seg2 := Kakeya.unitSegment base direction
  let seg3 := Kakeya.unitSegment (base + direction) direction
  have h_seg_union : seg0 ∪ seg1 ∪ seg2 ∪ seg3 = fullSegment :=
    four_unit_segments_union base direction
  let T0 : Kakeya.DeltaTube rho :=
    ⟨base + (-2 : ℝ) • direction, direction, hdir⟩
  let C0 := reverseTube T0
  let P1 : Kakeya.DeltaTube rho :=
    ⟨base + (-1 : ℝ) • direction, direction, hdir⟩
  let P2 : Kakeya.DeltaTube rho :=
    ⟨base, direction, hdir⟩
  let P3 : Kakeya.DeltaTube rho :=
    ⟨base + direction, direction, hdir⟩
  have hC0_seg : Kakeya.unitSegment C0.base C0.direction = seg0 := by
    have h_rev := unitSegment_reverse (base + (-2 : ℝ) • direction) direction
    have h_base : C0.base = (base + (-2 : ℝ) • direction) + direction := by
      simp [C0, reverseTube, T0] <;> abel
    have h_dir : C0.direction = -direction := by
      simp [C0, reverseTube, T0]
    rw [h_base, h_dir]
    exact h_rev
  have h_carrier_union :
      C0.carrier ∪ P1.carrier ∪ P2.carrier ∪ P3.carrier =
      Metric.cthickening rho fullSegment := by
    have h1 : C0.carrier = Metric.cthickening rho seg0 := by
      simp [Kakeya.DeltaTube.carrier, hC0_seg]
    have h2 : P1.carrier = Metric.cthickening rho seg1 := by rfl
    have h3 : P2.carrier = Metric.cthickening rho seg2 := by rfl
    have h4 : P3.carrier = Metric.cthickening rho seg3 := by rfl
    rw [h1, h2, h3, h4]
    rw [← Metric.cthickening_union, ← Metric.cthickening_union,
        ← Metric.cthickening_union]
    rw [h_seg_union]
  let envelope : Kakeya.Streamlined.Body :=
    ⟨Metric.cthickening rho fullSegment⟩
  have h_compact : IsCompact fullSegment := by
    apply IsCompact.image
    · exact isCompact_Icc
    · exact continuous_const.add (continuous_id.smul continuous_const)
  have h_measurable : envelope.IsMeasurable := by
    have h_closed : IsClosed (Metric.cthickening rho fullSegment) :=
      h_compact.cthickening.isClosed
    exact h_closed.measurableSet
  have h_seg_convex : Convex ℝ fullSegment := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rcases hy with ⟨s, ⟨hs0, hs1⟩, rfl⟩
    have h_at1 : a * t ≥ a * (-2) := mul_le_mul_of_nonneg_left ht0 ha
    have h_bs1 : b * s ≥ b * (-2) := mul_le_mul_of_nonneg_left hs0 hb
    have h_t : -2 ≤ a * t + b * s := by
      have h1 : a * t + b * s ≥ a * (-2) + b * (-2) := by linarith
      have h2 : a * (-2) + b * (-2) = -2 * (a + b) := by ring
      rw [h2] at h1
      rw [hab] at h1 <;> linarith
    have h_at2 : a * t ≤ a * (2 : ℝ) := mul_le_mul_of_nonneg_left ht1 ha
    have h_bs2 : b * s ≤ b * (2 : ℝ) := mul_le_mul_of_nonneg_left hs1 hb
    have h_s : a * t + b * s ≤ 2 := by
      have h1 : a * t + b * s ≤ a * (2 : ℝ) + b * (2 : ℝ) := by linarith
      have h2 : a * (2 : ℝ) + b * (2 : ℝ) = 2 * (a + b) := by ring
      rw [h2] at h1
      rw [hab] at h1 <;> linarith
    refine ⟨a * t + b * s, ⟨h_t, h_s⟩, ?_⟩
    have h_eq : a • (base + t • direction) + b • (base + s • direction) =
        base + (a * t + b * s) • direction := by
      have h1 : a • (base + t • direction) = a • base + (a * t) • direction := by
        rw [smul_add, smul_smul] <;> ring
      have h2 : b • (base + s • direction) = b • base + (b * s) • direction := by
        rw [smul_add, smul_smul] <;> ring
      rw [h1, h2]
      have h3 : a • base + (a * t) • direction + (b • base + (b * s) • direction) =
          (a • base + b • base) + ((a * t) • direction + (b * s) • direction) := by abel
      rw [h3]
      have h4 : a • base + b • base = (a + b) • base := by rw [← add_smul] <;> ring
      rw [h4, hab]
      have h5 : (a * t) • direction + (b * s) • direction = (a * t + b * s) • direction := by
        rw [← add_smul] <;> ring
      rw [h5] <;> simp
    exact h_eq.symm
  have h_convex : envelope.IsConvex :=
    h_seg_convex.cthickening rho
  let v : Fin 3 → Point3 := fun i =>
    match i with
    | 0 => 0
    | 1 => 0
    | 2 => direction
  let s : Set (Fin 3) := {2}
  have hv : Orthonormal ℝ (s.restrict v) := by
    constructor
    · intro i
      have hi2 : i.val = 2 := i.property
      have h : (s.restrict v) i = direction := by
        simp [Set.restrict, v, hi2] <;> fin_cases i.val <;> tauto
      rw [h] <;> exact hdir
    · intro i j hne
      have hi2 : i.val = 2 := i.property
      have hj2 : j.val = 2 := j.property
      have h_val_eq : i.val = j.val := by
        exact Eq.trans hi2 hj2.symm
      have h_eq : i = j := Subtype.ext h_val_eq
      exact False.elim (hne h_eq)
  have h_finrank : Module.finrank ℝ Point3 = Fintype.card (Fin 3) := by
    exact finrank_euclideanSpace_fin
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq h_finrank (hv := hv)
    with ⟨b, hb⟩
  have hb2 : b 2 = direction := hb 2 (by simp [s])
  let e' : Point3 ≃ₗᵢ[ℝ] Point3 :=
    OrthonormalBasis.equiv (EuclideanSpace.basisFun (Fin 3) ℝ) b (Equiv.refl (Fin 3))
  have he'_sum : ∀ (x : Point3), e' x = ∑ i : Fin 3, x i • b i :=
    OrthonormalBasis.equiv_apply_euclideanSpace b
  set frame : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    AffineIsometryEquiv.mk' (fun p : Point3 => e' p + base) e' 0 (by simp) with hframe_def
  have hframe_apply : ∀ (x : Point3), frame x = e' x + base := by
    intro x
    rw [hframe_def]
    <;> rfl
  have h_lower : frame '' Kakeya.Streamlined.axisBox rho rho 4 ⊆ envelope.carrier := by
    intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    have hx0 : |x 0| ≤ rho / 2 := hx.1
    have hx1 : |x 1| ≤ rho / 2 := hx.2.1
    have hx2 : |x 2| ≤ 2 := by linarith [hx.2.2]
    let y : Point3 := EuclideanSpace.single 2 (x 2)
    have h_ey : e' y = x 2 • direction := by
      rw [he'_sum y]
      simp [y, hb2, Fin.sum_univ_succ] <;> abel
    have hq : base + e' y ∈ fullSegment := by
      rw [h_ey]
      refine ⟨x 2, ⟨by linarith [abs_le.mp hx2], by linarith [abs_le.mp hx2]⟩, by simp⟩
    have h_norm : ‖e' x - e' y‖ = ‖x - y‖ := by
      have h_sub : e' (x - y) = e' x - e' y := map_sub e' x y
      rw [←h_sub]
      exact e'.norm_map (x - y)
    have h_dist : dist (frame x) (base + e' y) ≤ rho := by
      rw [hframe_apply x]
      have h2 : dist (e' x + base) (base + e' y) = ‖e' x - e' y‖ := by
        simp [dist_eq_norm] <;> abel
      rw [h2, h_norm]
      have h4 : ‖x - y‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
        have h5 : ‖x - y‖ ^ 2 = ∑ i : Fin 3, ((x - y) i) ^ 2 :=
          EuclideanSpace.real_norm_sq_eq (x - y)
        rw [h5]
        have h6 : (x - y) 0 = x 0 := by simp [y]
        have h7 : (x - y) 1 = x 1 := by simp [y]
        have h8 : (x - y) 2 = 0 := by simp [y]
        have h9 : ∑ i : Fin 3, ((x - y) i) ^ 2 = ((x - y) 0) ^ 2 + ((x - y) 1) ^ 2 + ((x - y) 2) ^ 2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h9, h6, h7, h8] <;> ring
      have h9 : (x 0) ^ 2 + (x 1) ^ 2 ≤ rho ^ 2 := by
        have hpos : 0 ≤ rho / 2 := by linarith
        have h10 : |x 0| ≤ |rho / 2| := by rw [abs_of_nonneg hpos] <;> exact hx0
        have h11 : |x 1| ≤ |rho / 2| := by rw [abs_of_nonneg hpos] <;> exact hx1
        have h12 : (x 0) ^ 2 ≤ (rho / 2) ^ 2 := sq_le_sq.mpr h10
        have h13 : (x 1) ^ 2 ≤ (rho / 2) ^ 2 := sq_le_sq.mpr h11
        nlinarith
      have h10 : ‖x - y‖ ^ 2 ≤ rho ^ 2 := by linarith
      have h11 : 0 ≤ ‖x - y‖ := by positivity
      nlinarith
    have h_goal : (frame x) ∈ Metric.cthickening rho fullSegment :=
      Metric.mem_cthickening_of_dist_le (frame x) (base + e' y) rho fullSegment hq h_dist
    exact h_goal
  have h_upper : envelope.carrier ⊆
      frame '' Kakeya.Streamlined.axisBox (3 * rho) (3 * rho) (3 * 4) := by
    intro p hp
    have hp' : p ∈ Metric.cthickening rho fullSegment := by
      simpa [envelope] using hp
    have h_eq2 : Metric.cthickening rho fullSegment =
        ⋃ x ∈ fullSegment, Metric.closedBall x rho :=
      h_compact.isClosed.cthickening_eq_biUnion_closedBall hrho_pos.le
    have h_exists : ∃ (q : Point3), q ∈ fullSegment ∧ p ∈ Metric.closedBall q rho := by
      rw [h_eq2] at hp'
      simpa [Set.mem_iUnion, Set.mem_iUnion₂] using hp'
    rcases h_exists with ⟨q, hq, hball⟩
    have hdist : dist p q ≤ rho := by
      simpa [Metric.mem_closedBall] using hball
    rcases hq with ⟨t, ht, hqt⟩
    set x : Point3 := e'.symm (p - base) with hx_def
    set y : Point3 := e'.symm (t • direction) with hy_def
    have hy : y = EuclideanSpace.single (2 : Fin 3) t := by
      have h2 : e'.symm (t • direction) = t • e'.symm direction := by
        exact map_smul e'.symm t direction
      have h_y_def : y = e'.symm (t • direction) := by simp [y]
      rw [h_y_def, h2]
      have h3 : e'.symm direction = EuclideanSpace.single (2 : Fin 3) 1 := by
        have h4 : e' (EuclideanSpace.single (2 : Fin 3) 1) = direction := by
          rw [he'_sum]
          simp [hb2, Fin.sum_univ_succ] <;> abel
        have h5 : e'.symm (e' (EuclideanSpace.single (2 : Fin 3) 1)) = EuclideanSpace.single (2 : Fin 3) 1 :=
          e'.symm_apply_apply (EuclideanSpace.single (2 : Fin 3) 1)
        rw [h4] at h5
        exact h5
      rw [h3]
      have h6 : t • EuclideanSpace.single (2 : Fin 3) 1 = EuclideanSpace.single (2 : Fin 3) t := by
        ext (i : Fin 3)
        fin_cases i <;> simp [EuclideanSpace.single] <;> ring
      exact h6
    have h_norm : ‖x - y‖ ≤ rho := by
      have hq' : q = base + t • direction := by simpa using hqt.symm
      have h5 : e' (x - y) = p - q := by
        have h6 : e' x = p - base := e'.apply_symm_apply (p - base)
        have h7 : e' y = t • direction := e'.apply_symm_apply (t • direction)
        calc
          e' (x - y) = e' x - e' y := map_sub e' x y
          _ = (p - base) - t • direction := by rw [h6, h7]
          _ = p - (base + t • direction) := by abel
          _ = p - q := by rw [hq'] <;> abel
      have h8 : ‖x - y‖ = ‖e' (x - y)‖ := (e'.norm_map _).symm
      rw [h8, h5]
      simpa [dist_eq_norm] using hdist
    have h_coord : ∀ (i : Fin 3), |(x - y) i| ≤ ‖x - y‖ := by
      intro i
      have h9 : ((x - y) i) ^ 2 ≤ ‖x - y‖ ^ 2 := by
        have h10 : ‖x - y‖ ^ 2 = ∑ j : Fin 3, ((x - y) j) ^ 2 :=
          EuclideanSpace.real_norm_sq_eq (x - y)
        rw [h10]
        exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have h10 : |(x - y) i| ≤ |‖x - y‖| := sq_le_sq.mp h9
      have h11 : 0 ≤ ‖x - y‖ := by positivity
      have h12 : |‖x - y‖| = ‖x - y‖ := abs_of_nonneg h11
      rw [h12] at h10
      exact h10
    have hx0 : |x 0| ≤ rho := by
      have h10 : y 0 = 0 := by rw [hy] <;> simp
      have h11 : |x 0 - y 0| ≤ ‖x - y‖ := h_coord 0
      have h12 : |x 0 - y 0| ≤ rho := by linarith [h_norm]
      rw [h10] at h12
      have h13 : |x 0 - 0| = |x 0| := by simp
      rw [h13] at h12
      exact h12
    have hx1 : |x 1| ≤ rho := by
      have h10 : y 1 = 0 := by rw [hy] <;> simp
      have h11 : |x 1 - y 1| ≤ ‖x - y‖ := h_coord 1
      have h12 : |x 1 - y 1| ≤ rho := by linarith [h_norm]
      rw [h10] at h12
      have h13 : |x 1 - 0| = |x 1| := by simp
      rw [h13] at h12
      exact h12
    have hx2 : |x 2| ≤ 2 + rho := by
      have h10 : y 2 = t := by rw [hy] <;> simp
      have h11 : |x 2 - y 2| ≤ ‖x - y‖ := h_coord 2
      have h12 : |x 2 - t| ≤ rho := by
        rw [h10] at h11
        exact h11.trans h_norm
      have h13 : |t| ≤ 2 := by
        exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h14 : |(x 2 - t) + t| ≤ |x 2 - t| + |t| :=
        abs_add_le (x 2 - t) t
      have h15 : (x 2 - t) + t = x 2 := by ring
      rw [h15] at h14
      have h16 : |x 2| ≤ |x 2 - t| + |t| := h14
      linarith
    have h_box : x ∈ Kakeya.Streamlined.axisBox (3 * rho) (3 * rho) (3 * 4) := by
      have h12 : |x 0| ≤ (3 * rho) / 2 := by linarith
      have h13 : |x 1| ≤ (3 * rho) / 2 := by linarith
      have h14 : |x 2| ≤ (3 * 4 : ℝ) / 2 := by linarith [hrho_small]
      exact ⟨h12, h13, h14⟩
    refine ⟨x, h_box, ?_⟩
    have h15 : frame x = p := by
      rw [hframe_apply x]
      have h16 : e' x = p - base := e'.apply_symm_apply (p - base)
      rw [h16] <;> abel
    exact h15
  have h_dim : envelope.HasDimensions rho rho 4 3 := by
    refine ⟨frame, by linarith, by linarith, by linarith, by norm_num, h_lower, h_upper⟩
  exact ⟨envelope, by rw [h_carrier_union], h_measurable, h_convex, h_dim⟩

end Kakeya.Assouad
