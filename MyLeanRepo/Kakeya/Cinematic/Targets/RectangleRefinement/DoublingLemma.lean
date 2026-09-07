import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Doubling lemma: HasCinematicCurvature implies IsCinematicFamily

Proof via bi-Lipschitz embedding into ℝ³ using the jet at a fixed point.

We place a grid of spacing `2s` in each jet coordinate and pick one family
member per occupied cell.  Any two functions in the same cell have jet
coordinates within `2s` of each other, so `c2Distance ≤ K · 6s = r/2`.
The interval `[c-r, c+r]` has length `2r`; with rounding to the nearest
grid point, `N > r/s = 12K` cells suffice per coordinate.
-/

noncomputable section

namespace Kakeya.Cinematic

lemma cinematic_curvature_to_isCinematicFamily
    {family : Set C2Function} {K : ℝ} (hK : 1 ≤ K)
    (hcurv : HasCinematicCurvature family K) :
    IsCinematicFamily family K ((12 * K + 2)^3) := by
  let x0 : UnitPoint := ⟨1 / 2, by
    simp only [Kakeya.Cinematic.unitInterval, Set.mem_Icc] <;> norm_num⟩
  let Φ : C2Function → ℝ × ℝ × ℝ := fun g =>
    (g x0, g.firstDeriv x0, g.secondDeriv x0)
  have hK_pos : 0 < K := by linarith

  have h_lower : ∀ (g h : C2Function), g ∈ family → h ∈ family →
      c2Distance g h ≤ K * (|g x0 - h x0| + |g.firstDeriv x0 - h.firstDeriv x0| +
        |g.secondDeriv x0 - h.secondDeriv x0|) := by
    intro g h hg hh
    have hcurv' : K⁻¹ * c2Distance g h ≤ jetGap g h x0 :=
      hcurv.2 hg hh x0
    calc
      c2Distance g h
        = K * (K⁻¹ * c2Distance g h) := by
          field_simp [hK_pos.ne'] <;> ring
      _ ≤ K * jetGap g h x0 := by gcongr
      _ = K * (|g x0 - h x0| + |g.firstDeriv x0 - h.firstDeriv x0| +
            |g.secondDeriv x0 - h.secondDeriv x0|) := by
          simp [jetGap]

  let N : ℕ := (⌈12 * K⌉).toNat + 1
  let D : ℝ := (12 * K + 2)^3
  have hD1 : 1 ≤ D := by
    have h1 : 1 ≤ 12 * K + 2 := by linarith
    have h2 : (1 : ℝ)^3 ≤ (12 * K + 2)^3 := by gcongr
    simpa using h2

  have h_ceil_nonneg : 0 ≤ ⌈12 * K⌉ := by positivity
  have h_toNat_eq : ((⌈12 * K⌉).toNat : ℝ) = (⌈12 * K⌉ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h_ceil_nonneg

  have hN_ge : (N : ℝ) > 12 * K + 1 / 2 := by
    dsimp only [N]
    have h1 : ((⌈12 * K⌉).toNat : ℝ) ≥ 12 * K := by
      rw [h_toNat_eq]
      exact Int.le_ceil _
    have h2 : ((N : ℝ)) = ((⌈12 * K⌉).toNat : ℝ) + 1 := by
      simp [N] <;> norm_cast
    rw [h2]
    linarith

  have hN_le : (N : ℝ) ≤ 12 * K + 2 := by
    dsimp only [N]
    have h1 : (⌈12 * K⌉ : ℝ) ≤ 12 * K + 1 := Int.ceil_lt_add_one _ |>.le
    have h2 : ((N : ℝ)) = ((⌈12 * K⌉).toNat : ℝ) + 1 := by
      simp [N] <;> norm_cast
    rw [h2, h_toNat_eq]
    linarith

  have h_doubling : ∀ (f : C2Function), f ∈ family → ∀ (r : ℝ), 0 < r →
      ∃ centers : Set C2Function,
        centers.Finite ∧ centers ⊆ family ∧
        (centers.ncard : ℝ) ≤ D ∧
        ∀ (g : C2Function), g ∈ family → c2Distance f g ≤ r →
          ∃ h ∈ centers, c2Distance h g ≤ r / 2 := by
    intro f hf r hr
    let c1 := f x0
    let c2 := f.firstDeriv x0
    let c3 := f.secondDeriv x0
    let s : ℝ := r / (12 * K)
    have hs_pos : 0 < s := by positivity
    let spacing : ℝ := 2 * s
    have h_spacing_pos : 0 < spacing := by positivity

    have h_cover1D : ∀ (c : ℝ), ∀ (x : ℝ), c - r ≤ x → x ≤ c + r →
        ∃ n : Fin N, |x - (c - r + (n : ℝ) * spacing)| ≤ s := by
      intro c x hx1 hx2
      let y := x - (c - r)
      have hy0 : 0 ≤ y := by linarith
      have hy2r : y ≤ 2 * r := by linarith
      -- Round to nearest grid point: n = floor((y + s) / spacing)
      let n_int : ℤ := ⌊(y + s) / spacing⌋
      have h_nint_nonneg : 0 ≤ n_int := by
        dsimp only [n_int]
        apply Int.floor_nonneg.mpr
        have h : (0 : ℝ) ≤ (y + s) / spacing := by positivity
        exact h
      let n : ℕ := n_int.toNat
      have hn_eq : (n : ℝ) = (n_int : ℝ) := by
        have h1 : (n : ℤ) = n_int := Int.toNat_of_nonneg h_nint_nonneg
        exact_mod_cast h1
      have h_n_lt : n < N := by
        have h1 : (y + s) / spacing < (N : ℝ) := by
          have h2 : (y + s) / spacing ≤ (2 * r + s) / spacing := by gcongr
          have h3 : (2 * r + s) / spacing = 12 * K + 1 / 2 := by
            dsimp only [spacing, s]
            field_simp [hK_pos.ne'] <;> ring
          rw [h3] at h2
          have h4 : (12 * K + 1 / 2 : ℝ) < (N : ℝ) := hN_ge
          linarith
        have h4 : (n_int : ℝ) ≤ (y + s) / spacing := Int.floor_le _
        have h5 : (n : ℝ) < (N : ℝ) := by
          rw [hn_eq]
          exact h4.trans_lt h1
        exact_mod_cast h5
      let fn : Fin N := ⟨n, h_n_lt⟩
      have h_b1 : -s ≤ y - (n : ℝ) * spacing := by
        have h : (n_int : ℝ) * spacing ≤ y + s := by
          have h' : (n_int : ℝ) ≤ (y + s) / spacing := Int.floor_le _
          have h'' : (n_int : ℝ) * spacing ≤ ((y + s) / spacing) * spacing := by gcongr
          have h3 : ((y + s) / spacing) * spacing = y + s := by
            field_simp [h_spacing_pos.ne'] <;> ring
          linarith
        have h' : (n : ℝ) = (n_int : ℝ) := hn_eq
        rw [h']
        linarith
      have h_b2 : y - (n : ℝ) * spacing ≤ s := by
        have h : y + s < ((n_int : ℝ) + 1) * spacing := by
          have h' : (y + s) / spacing < (n_int : ℝ) + 1 := Int.lt_floor_add_one _
          have h9 : y + s = ((y + s) / spacing) * spacing := by
            field_simp [h_spacing_pos.ne'] <;> ring
          rw [h9]
          gcongr <;> linarith
        have h' : (n : ℝ) = (n_int : ℝ) := hn_eq
        rw [h']
        linarith
      have h_abs : |x - (c - r + (n : ℝ) * spacing)| ≤ s := by
        have h_eq : x - (c - r + (n : ℝ) * spacing) = y - (n : ℝ) * spacing := by ring
        rw [h_eq]
        rw [abs_sub_le_iff] <;> constructor <;> linarith
      exact ⟨fn, h_abs⟩

    classical
    let Idx := Fin N × Fin N × Fin N
    let gridPoint (idx : Idx) : ℝ × ℝ × ℝ :=
      (c1 - r + (idx.1 : ℝ) * spacing,
       c2 - r + (idx.2.1 : ℝ) * spacing,
       c3 - r + (idx.2.2 : ℝ) * spacing)
    let inCube (p : ℝ × ℝ × ℝ) (idx : Idx) : Prop :=
      |p.1 - (gridPoint idx).1| ≤ s ∧
      |p.2.1 - (gridPoint idx).2.1| ≤ s ∧
      |p.2.2 - (gridPoint idx).2.2| ≤ s
    let P : Idx → Prop := fun idx =>
      ∃ h : C2Function, h ∈ family ∧ inCube (Φ h) idx
    let pick : Idx → C2Function := fun idx =>
      if h : P idx then Classical.choose h else f
    let IdxFinset : Finset Idx := Finset.univ
    let centers_finset : Finset C2Function :=
      (IdxFinset.filter P).image pick
    let centers : Set C2Function := (centers_finset : Set C2Function)

    have hcenters_finite : centers.Finite := centers_finset.finite_toSet

    have hcenters_subset : centers ⊆ family := by
      intro g hg
      rcases Finset.mem_image.mp hg with ⟨idx, hidx, rfl⟩
      have hP : P idx := (Finset.mem_filter.mp hidx).2
      have hpick : pick idx = Classical.choose hP := by
        simp [pick, hP]
      rw [hpick]
      exact (Classical.choose_spec hP).1

    have hcard : centers.ncard ≤ D := by
      have h1 : centers_finset.card ≤ (IdxFinset.filter P).card :=
        Finset.card_image_le
      have h2 : (IdxFinset.filter P).card ≤ IdxFinset.card :=
        Finset.card_filter_le _ _
      have h3 : IdxFinset.card = N^3 := by
        have h_univ : IdxFinset = Finset.univ := by simp [IdxFinset]
        rw [h_univ, Finset.card_univ]
        have h4 : Fintype.card Idx = N * N * N := by
          simp [Idx, Fintype.card_prod, Fintype.card_fin]
          <;> ring
        rw [h4]
        <;> ring
      have h4 : (N^3 : ℝ) ≤ D := by
        dsimp only [D]
        have h5 : (N : ℝ) ≤ 12 * K + 2 := hN_le
        have h6 : (N^3 : ℝ) ≤ (12 * K + 2)^3 := by
          gcongr <;> linarith
        exact h6
      rw [Set.ncard_coe_finset]
      have h7 : (centers_finset.card : ℝ) ≤ (N^3 : ℝ) := by
        exact_mod_cast (h1.trans (h2.trans (by rw [h3])))
      linarith

    have hcover : ∀ (g : C2Function), g ∈ family → c2Distance f g ≤ r →
        ∃ h ∈ centers, c2Distance h g ≤ r / 2 := by
      intro g hg hdist
      have h4 : |g x0 - f x0| ≤ r := by
        have h_comm : c2Distance g f = c2Distance f g := dist_comm g f
        calc |g x0 - f x0| ≤ c2Distance g f := abs_value_sub_le_c2Distance g f x0
             _ = c2Distance f g := h_comm
             _ ≤ r := hdist
      have h5 : |g.firstDeriv x0 - f.firstDeriv x0| ≤ r := by
        have h_comm : c2Distance g f = c2Distance f g := dist_comm g f
        calc |g.firstDeriv x0 - f.firstDeriv x0| ≤ c2Distance g f :=
               abs_firstDeriv_sub_le_c2Distance g f x0
             _ = c2Distance f g := h_comm
             _ ≤ r := hdist
      have h6 : |g.secondDeriv x0 - f.secondDeriv x0| ≤ r := by
        have h_comm : c2Distance g f = c2Distance f g := dist_comm g f
        calc |g.secondDeriv x0 - f.secondDeriv x0| ≤ c2Distance g f :=
               abs_secondDeriv_sub_le_c2Distance g f x0
             _ = c2Distance f g := h_comm
             _ ≤ r := hdist

      have h_x1 : c1 - r ≤ g x0 := by
        have h : |g x0 - c1| ≤ r := by simpa [c1] using h4
        have h' : -r ≤ g x0 - c1 := (abs_le.mp h).1
        linarith
      have h_x2 : g x0 ≤ c1 + r := by
        have h : |g x0 - c1| ≤ r := by simpa [c1] using h4
        have h' : g x0 - c1 ≤ r := (abs_le.mp h).2
        linarith
      have h_y1 : c2 - r ≤ g.firstDeriv x0 := by
        have h : |g.firstDeriv x0 - c2| ≤ r := by simpa [c2] using h5
        have h' : -r ≤ g.firstDeriv x0 - c2 := (abs_le.mp h).1
        linarith
      have h_y2 : g.firstDeriv x0 ≤ c2 + r := by
        have h : |g.firstDeriv x0 - c2| ≤ r := by simpa [c2] using h5
        have h' : g.firstDeriv x0 - c2 ≤ r := (abs_le.mp h).2
        linarith
      have h_z1 : c3 - r ≤ g.secondDeriv x0 := by
        have h : |g.secondDeriv x0 - c3| ≤ r := by simpa [c3] using h6
        have h' : -r ≤ g.secondDeriv x0 - c3 := (abs_le.mp h).1
        linarith
      have h_z2 : g.secondDeriv x0 ≤ c3 + r := by
        have h : |g.secondDeriv x0 - c3| ≤ r := by simpa [c3] using h6
        have h' : g.secondDeriv x0 - c3 ≤ r := (abs_le.mp h).2
        linarith

      rcases h_cover1D c1 (g x0) h_x1 h_x2 with ⟨n1, hn1⟩
      rcases h_cover1D c2 (g.firstDeriv x0) h_y1 h_y2 with ⟨n2, hn2⟩
      rcases h_cover1D c3 (g.secondDeriv x0) h_z1 h_z2 with ⟨n3, hn3⟩

      let idx : Idx := (n1, n2, n3)

      have h_inCube : inCube (Φ g) idx := by
        simp only [inCube, gridPoint]
        exact ⟨hn1, hn2, hn3⟩

      have hP : P idx := ⟨g, hg, h_inCube⟩
      have hidx : idx ∈ IdxFinset.filter P := by
        simp only [IdxFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hP

      have hpick_in : pick idx ∈ centers_finset := by
        apply Finset.mem_image.mpr
        exact ⟨idx, hidx, rfl⟩

      have hP_spec : (pick idx) ∈ family ∧ inCube (Φ (pick idx)) idx := by
        have hpick_eq : pick idx = Classical.choose hP := by
          simp [pick, hP]
        rw [hpick_eq]
        exact Classical.choose_spec hP

      have hpick_in_family : pick idx ∈ family := hP_spec.1
      have hpick_cube : inCube (Φ (pick idx)) idx := hP_spec.2

      have h1 : |g x0 - (pick idx) x0| ≤ 2 * s := by
        have ha : |g x0 - (gridPoint idx).1| ≤ s := h_inCube.1
        have hb : |(gridPoint idx).1 - (pick idx) x0| ≤ s := by
          have h : |(pick idx) x0 - (gridPoint idx).1| ≤ s := by simpa [Φ] using hpick_cube.1
          rwa [abs_sub_comm] at h
        have h : |g x0 - (pick idx) x0| ≤ |g x0 - (gridPoint idx).1| + |(gridPoint idx).1 - (pick idx) x0| := by
          exact abs_sub_le (g x0) (gridPoint idx).1 ((pick idx) x0)
        linarith

      have h2 : |g.firstDeriv x0 - (pick idx).firstDeriv x0| ≤ 2 * s := by
        have ha : |g.firstDeriv x0 - (gridPoint idx).2.1| ≤ s := h_inCube.2.1
        have hb : |(gridPoint idx).2.1 - (pick idx).firstDeriv x0| ≤ s := by
          have h : |(pick idx).firstDeriv x0 - (gridPoint idx).2.1| ≤ s := by simpa [Φ] using hpick_cube.2.1
          rwa [abs_sub_comm] at h
        have h : |g.firstDeriv x0 - (pick idx).firstDeriv x0| ≤
            |g.firstDeriv x0 - (gridPoint idx).2.1| + |(gridPoint idx).2.1 - (pick idx).firstDeriv x0| := by
          exact abs_sub_le (g.firstDeriv x0) (gridPoint idx).2.1
            ((pick idx).firstDeriv x0)
        linarith

      have h3 : |g.secondDeriv x0 - (pick idx).secondDeriv x0| ≤ 2 * s := by
        have ha : |g.secondDeriv x0 - (gridPoint idx).2.2| ≤ s := h_inCube.2.2
        have hb : |(gridPoint idx).2.2 - (pick idx).secondDeriv x0| ≤ s := by
          have h : |(pick idx).secondDeriv x0 - (gridPoint idx).2.2| ≤ s := by simpa [Φ] using hpick_cube.2.2
          rwa [abs_sub_comm] at h
        have h : |g.secondDeriv x0 - (pick idx).secondDeriv x0| ≤
            |g.secondDeriv x0 - (gridPoint idx).2.2| + |(gridPoint idx).2.2 - (pick idx).secondDeriv x0| := by
          exact abs_sub_le (g.secondDeriv x0) (gridPoint idx).2.2
            ((pick idx).secondDeriv x0)
        linarith

      have h_sum : |g x0 - (pick idx) x0| +
          |g.firstDeriv x0 - (pick idx).firstDeriv x0| +
          |g.secondDeriv x0 - (pick idx).secondDeriv x0| ≤ 6 * s := by
        linarith

      have h_final : c2Distance (pick idx) g ≤ r / 2 := by
        have h_bound_raw : c2Distance g (pick idx) ≤
            K * (|g x0 - (pick idx) x0| +
              |g.firstDeriv x0 - (pick idx).firstDeriv x0| +
              |g.secondDeriv x0 - (pick idx).secondDeriv x0|) :=
          h_lower g (pick idx) hg hpick_in_family
        have h_comm : c2Distance g (pick idx) = c2Distance (pick idx) g :=
          dist_comm g (pick idx)
        have h_bound : c2Distance (pick idx) g ≤
            K * (|g x0 - (pick idx) x0| +
              |g.firstDeriv x0 - (pick idx).firstDeriv x0| +
              |g.secondDeriv x0 - (pick idx).secondDeriv x0|) := by
          rw [h_comm] at h_bound_raw
          exact h_bound_raw
        have h9 : K * (|g x0 - (pick idx) x0| +
            |g.firstDeriv x0 - (pick idx).firstDeriv x0| +
            |g.secondDeriv x0 - (pick idx).secondDeriv x0|) ≤ K * (6 * s) := by
          gcongr
        have h10 : K * (6 * s) = r / 2 := by
          dsimp only [s]
          field_simp [hK_pos.ne'] <;> ring
        linarith

      exact ⟨pick idx, hpick_in, h_final⟩

    exact ⟨centers, hcenters_finite, hcenters_subset, by exact_mod_cast hcard, hcover⟩

  have h_main : IsCinematicFamily family K D :=
    ⟨hcurv.1, h_doubling, hcurv.2⟩
  exact h_main

/-- Existential version for backward compatibility. -/
lemma hasCinematicCurvature_implies_isCinematicFamily
    {family : Set C2Function} {K : ℝ} (hK : 1 ≤ K)
    (hcurv : HasCinematicCurvature family K) :
    ∃ (D : ℝ), 1 ≤ D ∧ IsCinematicFamily family K D := by
  let D : ℝ := (12 * K + 2)^3
  have hD1 : 1 ≤ D := by
    have h1 : 1 ≤ 12 * K + 2 := by linarith
    have h2 : (1 : ℝ)^3 ≤ (12 * K + 2)^3 := by gcongr
    simpa using h2
  exact ⟨D, hD1, cinematic_curvature_to_isCinematicFamily hK hcurv⟩

/-- Uniform version: D depends only on K, not on the family. -/
lemma uniform_doubling (K : ℝ) (hK : 1 ≤ K) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (family : Set C2Function), HasCinematicCurvature family K →
        IsCinematicFamily family K D := by
  let D : ℝ := (12 * K + 2)^3
  have hD1 : 1 ≤ D := by
    have h1 : 1 ≤ 12 * K + 2 := by linarith
    have h2 : (1 : ℝ)^3 ≤ (12 * K + 2)^3 := by gcongr
    simpa using h2
  refine' ⟨D, hD1, _⟩
  intro family hcurv
  exact cinematic_curvature_to_isCinematicFamily hK hcurv

end Kakeya.Cinematic
