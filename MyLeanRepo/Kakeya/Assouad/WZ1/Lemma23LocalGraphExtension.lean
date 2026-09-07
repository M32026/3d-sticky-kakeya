import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalGraphExtensionStatements

/-!
# WZ1 Lemma 23 local graph extension

Construct a globally defined bounded Lipschitz function from sampled plane
normals using McShane extension and clamping.
-/

namespace Kakeya.Assouad

open Set Metric

private lemma wz1Lemma23ClampLocalGraph_lipschitz :
    LipschitzWith 1 wz1Lemma23ClampLocalGraph := by
  have h1 : LipschitzWith 1 (fun x : ℝ => min 2 x) :=
    LipschitzWith.const_min LipschitzWith.id 2
  have h2 : LipschitzWith 1 (fun x : ℝ => max (-2) x) :=
    LipschitzWith.const_max LipschitzWith.id (-2)
  have h3 : LipschitzWith (1 * 1) wz1Lemma23ClampLocalGraph :=
    h2.comp h1
  simpa [one_mul] using h3

private lemma wz1_lemma23_quotient_lipschitz
    (sample : Finset ℝ)
    (anchor : ℝ → Point3)
    (normal : Point3 → Point3)
    (hV_z :
      ∀ y ∈ sample,
        |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2)
    (hV_x :
      ∀ y ∈ sample,
        1 / 4 ≤ |normal (anchor y) (0 : Fin 3)|)
    (hnormal_dist :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
        dist (normal (anchor y₁)) (normal (anchor y₂)) ≤
          dist (anchor y₁) (anchor y₂))
    (hanchor_dist :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
        dist (anchor y₁) (anchor y₂) ≤
          4 * |y₁ - y₂|) :
    LipschitzOnWith 64
      (fun y : ℝ =>
        normal (anchor y) (2 : Fin 3) /
          normal (anchor y) (0 : Fin 3))
      (sample : Set ℝ) := by
  let f : ℝ → ℝ := fun y =>
    normal (anchor y) (2 : Fin 3) /
      normal (anchor y) (0 : Fin 3)
  have h_main :
      ∀ y₁ : ℝ, y₁ ∈ (sample : Set ℝ) →
        ∀ y₂ : ℝ, y₂ ∈ (sample : Set ℝ) →
          dist (f y₁) (f y₂) ≤
            (64 : ℝ) * dist y₁ y₂ := by
    intro y₁ hy₁ y₂ hy₂
    set n₁ := normal (anchor y₁) with hn₁
    set n₂ := normal (anchor y₂) with hn₂
    set a := n₁ (2 : Fin 3) with ha
    set b := n₁ (0 : Fin 3) with hb
    set c := n₂ (2 : Fin 3) with hc
    set d := n₂ (0 : Fin 3) with hd
    have hb_pos : 0 < |b| := by
      exact lt_of_lt_of_le (by norm_num) (hV_x y₁ hy₁)
    have hb_ne_zero : b ≠ 0 := by
      intro h
      rw [h] at hb_pos
      simp at hb_pos
    have hd_pos : 0 < |d| := by
      exact lt_of_lt_of_le (by norm_num) (hV_x y₂ hy₂)
    have hd_ne_zero : d ≠ 0 := by
      intro h
      rw [h] at hd_pos
      simp at hd_pos
    have h1 : 1 / 4 ≤ |b| := hV_x y₁ hy₁
    have h2 : 1 / 4 ≤ |d| := hV_x y₂ hy₂
    have h3 : |c| ≤ 1 / 2 := hV_z y₂ hy₂
    have h4 : |a - c| ≤ dist n₁ n₂ := by
      have h :
          |(n₁ - n₂) (2 : Fin 3)| ≤ ‖n₁ - n₂‖ :=
        PiLp.norm_apply_le (n₁ - n₂) (2 : Fin 3)
      simpa [dist_eq_norm] using h
    have h5 : |d - b| ≤ dist n₁ n₂ := by
      have h :
          |(n₁ - n₂) (0 : Fin 3)| ≤ ‖n₁ - n₂‖ :=
        PiLp.norm_apply_le (n₁ - n₂) (0 : Fin 3)
      have h' :
          |d - b| = |(n₁ - n₂) (0 : Fin 3)| := by
        simp [hd, hb]
        rw [show d - b =
          -(n₁ (0 : Fin 3) - n₂ (0 : Fin 3)) by ring]
        rw [abs_neg]
      rw [h']
      simpa [dist_eq_norm] using h
    have h6 :
        dist n₁ n₂ ≤ dist (anchor y₁) (anchor y₂) :=
      hnormal_dist y₁ hy₁ y₂ hy₂
    have h7 :
        dist (anchor y₁) (anchor y₂) ≤
          4 * |y₁ - y₂| :=
      hanchor_dist y₁ hy₁ y₂ hy₂
    have h_quot :
        |a / b - c / d| ≤ 12 * dist n₁ n₂ := by
      have h_eq :
          a / b - c / d =
            (a - c) / b + c * (d - b) / (b * d) := by
        field_simp [hb_ne_zero, hd_ne_zero]
        ring
      rw [h_eq]
      calc
        |(a - c) / b + c * (d - b) / (b * d)|
            ≤ |(a - c) / b| +
              |c * (d - b) / (b * d)| := by
          exact abs_add_le _ _
        _ =
            |a - c| / |b| +
              |c| * |d - b| / (|b| * |d|) := by
          simp [abs_div, abs_mul]
        _ ≤
            dist n₁ n₂ / (1 / 4 : ℝ) +
              (1 / 2 : ℝ) * dist n₁ n₂ /
                ((1 / 4 : ℝ) * (1 / 4 : ℝ)) := by
          gcongr
        _ = 12 * dist n₁ n₂ := by ring
    have h_dist :
        dist (f y₁) (f y₂) = |f y₁ - f y₂| := by
      simp [dist_eq_norm]
    rw [h_dist]
    have h_final :
        |f y₁ - f y₂| ≤ 48 * |y₁ - y₂| := by
      calc
        |f y₁ - f y₂| = |a / b - c / d| := by rfl
        _ ≤ 12 * dist n₁ n₂ := h_quot
        _ ≤ 12 * dist (anchor y₁) (anchor y₂) := by gcongr
        _ ≤ 12 * (4 * |y₁ - y₂|) := by gcongr
        _ = 48 * |y₁ - y₂| := by ring
    have h_ly : dist y₁ y₂ = |y₁ - y₂| := by
      simp [dist_eq_norm]
    rw [h_ly]
    have h_le :
        48 * |y₁ - y₂| ≤ 64 * |y₁ - y₂| := by
      nlinarith [abs_nonneg (y₁ - y₂)]
    exact h_final.trans h_le
  rw [lipschitzOnWith_iff_dist_le_mul]
  exact h_main

/--
Construct the bounded local graph from the quantitative hypotheses actually
used by the quotient-extension argument.  The anchor points need not lie
exactly on their indexing y-layers; the later measurable-shading application
only needs their mutual distortion relative to those layer coordinates.
-/
theorem wz1_lemma23_local_graph_extension_of_distortion
    (sample : Finset ℝ)
    (anchor : ℝ → Point3)
    (normal : Point3 → Point3)
    (hV_z :
      ∀ y ∈ sample,
        |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2)
    (hV_x :
      ∀ y ∈ sample,
        1 / 4 ≤ |normal (anchor y) (0 : Fin 3)|)
    (hnormal_dist :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
        dist (normal (anchor y₁)) (normal (anchor y₂)) ≤
          dist (anchor y₁) (anchor y₂))
    (hanchor_dist :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
        dist (anchor y₁) (anchor y₂) ≤
          4 * |y₁ - y₂|) :
    ∃ g : ℝ → ℝ,
      LipschitzOnWith 64 g Set.univ ∧
      (∀ y, |g y| ≤ 2) ∧
      ∀ y ∈ sample,
        g y =
          normal (anchor y) (2 : Fin 3) /
            normal (anchor y) (0 : Fin 3) := by
  let f : ℝ → ℝ := fun y =>
    normal (anchor y) (2 : Fin 3) /
      normal (anchor y) (0 : Fin 3)
  have h_lipschitz :
      LipschitzOnWith 64 f (sample : Set ℝ) :=
    wz1_lemma23_quotient_lipschitz
      sample anchor normal hV_z hV_x hnormal_dist hanchor_dist
  rcases h_lipschitz.extend_real with
    ⟨g₀, hg₀_lipschitz, hg₀_eqOn⟩
  let g : ℝ → ℝ := fun y =>
    wz1Lemma23ClampLocalGraph (g₀ y)
  have hg_lipschitz : LipschitzWith (1 * 64) g :=
    wz1Lemma23ClampLocalGraph_lipschitz.comp hg₀_lipschitz
  have hg_lipschitz64 : LipschitzWith 64 g := by
    simpa [one_mul] using hg_lipschitz
  have h1 : LipschitzOnWith 64 g Set.univ :=
    hg_lipschitz64.lipschitzOnWith
  have h2 : ∀ y, |g y| ≤ 2 := by
    intro y
    have h_left : -2 ≤ g y := by
      simp [g, wz1Lemma23ClampLocalGraph]
    have h_right : g y ≤ 2 := by
      simp [g, wz1Lemma23ClampLocalGraph]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h3 : ∀ y ∈ sample, g y = f y := by
    intro y hy
    have h4' : g₀ y = f y := (hg₀_eqOn hy).symm
    have hnx_pos :
        0 < |normal (anchor y) (0 : Fin 3)| := by
      exact lt_of_lt_of_le (by norm_num) (hV_x y hy)
    have h5 : |f y| ≤ 2 := by
      set n := normal (anchor y) with hn
      have hz : |n (2 : Fin 3)| ≤ 1 / 2 := hV_z y hy
      have hx : 1 / 4 ≤ |n (0 : Fin 3)| := hV_x y hy
      calc
        |f y| = |n (2 : Fin 3) / n (0 : Fin 3)| := by rfl
        _ = |n (2 : Fin 3)| / |n (0 : Fin 3)| := by
          rw [abs_div]
        _ ≤ (1 / 2 : ℝ) / |n (0 : Fin 3)| := by gcongr
        _ ≤ (1 / 2 : ℝ) / (1 / 4 : ℝ) := by gcongr
        _ = 2 := by norm_num
    have h6 : -2 ≤ f y := (abs_le.mp h5).1
    have h7 : f y ≤ 2 := (abs_le.mp h5).2
    have h8 : min 2 (f y) = f y := by
      rw [min_eq_right]
      linarith
    have h9 : max (-2) (min 2 (f y)) = f y := by
      rw [h8, max_eq_right]
      linarith
    change wz1Lemma23ClampLocalGraph (g₀ y) = f y
    rw [h4']
    exact h9
  exact ⟨g, h1, h2, h3⟩

theorem wz1_lemma23_local_graph_extension :
    WZ1Lemma23LocalGraphExtensionStatement := by
  intro sample anchor normal h_anchor_y h_normal_unit
    hV_z hV_x hnormal_dist hanchor_dist
  exact
    wz1_lemma23_local_graph_extension_of_distortion
      sample anchor normal hV_z hV_x hnormal_dist hanchor_dist

end Kakeya.Assouad
