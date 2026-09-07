import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CinematicShearCorridorTransferStatement

/-!
# Transfer a cinematic corridor through the common shear

Undoing the Section 7 linear shear enlarges a graph corridor by at most the
explicit factor `2 + B` and adds at most `B` to its Lipschitz constant.
-/

namespace Kakeya.Assouad

theorem cinematic_shear_corridor_transfer :
    CinematicShearCorridorTransferStatement := by
  intro g c₀ B L hB hL r hr
  let h : Kakeya.Cinematic.C2Function :=
    unshearedCinematicCurve g c₀
  have h_ext_eval :
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        h.extension x = g.extension x + c₀ * x := by
    intro x hx
    let x' : Kakeya.Cinematic.UnitPoint := ⟨x, hx⟩
    have h1 : h.extension x = h x' := by
      have h2 := h.extension_eq_value x'
      simpa [x'] using h2
    rw [h1]
    have h3 :
        h x' = g x' + cinematicLinearDrift c₀ x' :=
      Kakeya.Cinematic.C2Function.add_apply
        g (cinematicLinearDrift c₀) x'
    rw [h3]
    have h4 : cinematicLinearDrift c₀ x' = c₀ * x := by
      simp [cinematicLinearDrift, slopeCurve_value,
        identitySlopeFunction, x']
    rw [h4]
    have h5 : g x' = g.extension x := by
      have h6 := g.extension_eq_value x'
      simpa [x'] using h6.symm
    rw [h5]
  constructor
  · intro q hq
    have h1 :
        ∃ p : ℝ × ℝ,
          p ∈ Kakeya.Cinematic.functionGraph g ∧
            dist (cinematicShear c₀ q) p < r := by
      simpa [Kakeya.Cinematic.graphNeighborhood,
        Metric.mem_thickening_iff] using hq
    rcases h1 with ⟨p, hp_graph, hp_dist⟩
    rcases hp_graph with ⟨hp1, hp2⟩
    have hp1' : p.1 ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Kakeya.Cinematic.unitInterval] using hp1
    have hprod :
        dist (cinematicShear c₀ q) p =
          max
            (dist (cinematicShear c₀ q).1 p.1)
            (dist (cinematicShear c₀ q).2 p.2) :=
      Prod.dist_eq
    have h_both :
        dist (cinematicShear c₀ q).1 p.1 < r ∧
          dist (cinematicShear c₀ q).2 p.2 < r := by
      rw [hprod] at hp_dist
      exact (max_lt_iff).mp hp_dist
    have h_horiz : |q 1 - p.1| < r := by
      have h' :
          dist (cinematicShear c₀ q).1 p.1 =
            |q 1 - p.1| := by
        rw [Real.dist_eq]
        rfl
      rw [h'] at h_both
      exact h_both.1
    have h_vert :
        |(q 0 - c₀ * q 1) - p.2| < r := by
      have h' :
          dist (cinematicShear c₀ q).2 p.2 =
            |(q 0 - c₀ * q 1) - p.2| := by
        rw [Real.dist_eq]
        rfl
      rw [h'] at h_both
      exact h_both.2
    have h_vert' :
        |q 0 - c₀ * q 1 - p.2| < r := by
      have h_eq :
          (q 0 - c₀ * q 1) - p.2 =
            q 0 - c₀ * q 1 - p.2 := by
        ring
      rw [h_eq] at h_vert
      exact h_vert
    have hp2' : p.2 = g.extension p.1 := by
      let x' : Kakeya.Cinematic.UnitPoint := ⟨p.1, hp1⟩
      have h_val : g.extension p.1 = g x' := by
        have h6 := g.extension_eq_value x'
        simpa [x'] using h6
      exact hp2.trans h_val.symm
    let z : Point2 :=
      h.extension p.1 •
          EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        p.1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
    have hz0 : z 0 = h.extension p.1 := by simp [z]
    have hz1 : z 1 = p.1 := by simp [z]
    have hz_in : z ∈ cinematicExtensionGraph h := by
      simp only [cinematicExtensionGraph, Set.mem_setOf_eq]
      have h_z1 : z 1 ∈ Set.Icc (0 : ℝ) 1 := by
        rw [hz1]
        exact hp1'
      exact ⟨h_z1, by rw [hz0, hz1]⟩
    have h_vert2 :
        |q 0 - z 0| ≤ (1 + (B : ℝ)) * r := by
      rw [hz0, h_ext_eval p.1 hp1']
      have h_eq :
          q 0 - (g.extension p.1 + c₀ * p.1) =
            (q 0 - c₀ * q 1 - p.2) +
              c₀ * (q 1 - p.1) := by
        rw [hp2']
        ring
      rw [h_eq]
      have h_ineq :
          |(q 0 - c₀ * q 1 - p.2) +
              c₀ * (q 1 - p.1)| ≤
            |q 0 - c₀ * q 1 - p.2| +
              |c₀ * (q 1 - p.1)| :=
        abs_add_le _ _
      have h_c :
          |c₀ * (q 1 - p.1)| =
            |c₀| * |q 1 - p.1| := by
        rw [abs_mul]
      rw [h_c] at h_ineq
      have h5 :
          |q 0 - c₀ * q 1 - p.2| +
              |c₀| * |q 1 - p.1| ≤
            r + (B : ℝ) * r := by
        have h6 : |q 0 - c₀ * q 1 - p.2| ≤ r := by
          linarith [h_vert']
        have h7 :
            |c₀| * |q 1 - p.1| ≤ (B : ℝ) * r := by
          calc
            |c₀| * |q 1 - p.1| ≤
                (B : ℝ) * |q 1 - p.1| := by
              gcongr
            _ ≤ (B : ℝ) * r := by
              have h8 : |q 1 - p.1| ≤ r := by
                linarith [h_horiz]
              gcongr
        linarith
      linarith
    have h_horiz2 : |q 1 - z 1| ≤ r := by
      rw [hz1]
      linarith [h_horiz]
    let v := q - z
    have h1 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      have h_sum := EuclideanSpace.real_norm_sq_eq v
      simpa [Fin.sum_univ_two] using h_sum
    have h2 :
        ‖v‖ ^ 2 ≤ (|v 0| + |v 1|) ^ 2 := by
      have h31 : |v 0| ^ 2 = (v 0) ^ 2 :=
        sq_abs (v 0)
      have h32 : |v 1| ^ 2 = (v 1) ^ 2 :=
        sq_abs (v 1)
      have h3 :
          (v 0) ^ 2 + (v 1) ^ 2 ≤
            (|v 0| + |v 1|) ^ 2 := by
        have h4 : 0 ≤ 2 * |v 0| * |v 1| := by positivity
        have h5 :
            (|v 0| + |v 1|) ^ 2 =
              |v 0| ^ 2 + |v 1| ^ 2 +
                2 * |v 0| * |v 1| := by
          ring
        rw [h5, h31, h32]
        linarith
      linarith
    have h4 : 0 ≤ ‖v‖ := by positivity
    have h5 : 0 ≤ |v 0| + |v 1| := by positivity
    have h6 : ‖v‖ ≤ |v 0| + |v 1| := by
      nlinarith
    have h_norm_bound :
        dist q z ≤ |q 0 - z 0| + |q 1 - z 1| := by
      have h7 : dist q z = ‖q - z‖ := by rfl
      rw [h7]
      have h8 : (q - z) 0 = q 0 - z 0 := by simp
      have h9 : (q - z) 1 = q 1 - z 1 := by simp
      rw [h8, h9] at h6
      exact h6
    have h_final :
        dist q z ≤ (2 + (B : ℝ)) * r := by
      calc
        dist q z ≤ |q 0 - z 0| + |q 1 - z 1| :=
          h_norm_bound
        _ ≤ (1 + (B : ℝ)) * r + r := by gcongr
        _ = (2 + (B : ℝ)) * r := by ring
    exact Metric.mem_cthickening_of_dist_le
      q z ((2 + (B : ℝ)) * r)
      (cinematicExtensionGraph h) hz_in h_final
  · have hL_dist :
        ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ∀ y ∈ Set.Icc (0 : ℝ) 1,
            dist (g.extension x) (g.extension y) ≤
              (L : ℝ) * dist x y :=
      lipschitzOnWith_iff_dist_le_mul.mp hL
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have h_ext_x :
        h.extension x = g.extension x + c₀ * x :=
      h_ext_eval x hx
    have h_ext_y :
        h.extension y = g.extension y + c₀ * y :=
      h_ext_eval y hy
    have h_Lip :
        |g.extension x - g.extension y| ≤
          (L : ℝ) * |x - y| := by
      have h := hL_dist x hx y hy
      simpa [Real.dist_eq] using h
    have h_main :
        dist (h.extension x) (h.extension y) ≤
          ((L : ℝ) + (B : ℝ)) * dist x y := by
      rw [Real.dist_eq, Real.dist_eq]
      rw [h_ext_x, h_ext_y]
      have h_eq :
          (g.extension x + c₀ * x) -
              (g.extension y + c₀ * y) =
            (g.extension x - g.extension y) +
              c₀ * (x - y) := by
        ring
      rw [h_eq]
      have h_ineq :
          |(g.extension x - g.extension y) +
              c₀ * (x - y)| ≤
            |g.extension x - g.extension y| +
              |c₀ * (x - y)| :=
        abs_add_le _ _
      have h_c :
          |c₀ * (x - y)| = |c₀| * |x - y| := by
        rw [abs_mul]
      rw [h_c] at h_ineq
      calc
        |(g.extension x - g.extension y) +
              c₀ * (x - y)| ≤
            |g.extension x - g.extension y| +
              |c₀| * |x - y| := h_ineq
        _ ≤ (L : ℝ) * |x - y| +
              (B : ℝ) * |x - y| := by
          gcongr
        _ = ((L : ℝ) + (B : ℝ)) * |x - y| := by
          ring
    simpa using h_main

end Kakeya.Assouad
