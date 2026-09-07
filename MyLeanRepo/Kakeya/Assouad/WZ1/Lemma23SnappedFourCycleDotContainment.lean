import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleStatements

/-!
WZ1 Lemma 23, Steps 3--5: interpret a snapped local-pair signature collision
as an exact local--global--local four-cycle, perform the faithful skew
centering, and invoke the closed dot-difference telescope.
-/

namespace Kakeya.Assouad

theorem wz1_lemma23_snapped_four_cycle_dot_containment :
    WZ1Lemma23SnappedFourCycleDotContainmentStatement := by
  intro rho w f g cells path h_rho h_path h_base
  dsimp only
  set Q₁ := path.1 with hQ₁
  set Q₂ := path.2.1 with hQ₂
  set Q₃ := path.2.2.1 with hQ₃
  set Q₄ := path.2.2.2 with hQ₄
  set q₁ := wz1Lemma23SnappedPoint rho Q₁ with hq₁
  set q₂ := wz1Lemma23SnappedPoint rho Q₂ with hq₂
  set q₃ := wz1Lemma23SnappedPoint rho Q₃ with hq₃
  set q₄ := wz1Lemma23SnappedPoint rho Q₄ with hq₄
  set baseHeight := q₁ 2 with hbaseHeight
  set p₁ := wz1Lemma23SkewPoint baseHeight f g q₁ with hp₁
  set p₂ := wz1Lemma23SkewPoint baseHeight f g q₂ with hp₂
  set p₃ := wz1Lemma23SkewPoint baseHeight f g q₃ with hp₃
  set p₄ := wz1Lemma23SkewPoint baseHeight f g q₄ with hp₄
  set centeredSlope := wz1Lemma23CenteredSlope baseHeight f with hcs
  set centeredLocal := wz1Lemma23CenteredLocal g with hcl
  have h_all : (Q₁ ∈ cells ∧ Q₂ ∈ cells ∧ Q₃ ∈ cells ∧ Q₄ ∈ cells) ∧
      wz1Lemma23SameSnappedLocalGrain rho g Q₁ Q₂ ∧
      wz1Lemma23SameSnappedLocalGrain rho g Q₄ Q₃ ∧
      wz1Lemma23SnappedHeight Q₁ = wz1Lemma23SnappedHeight Q₄ ∧
      wz1Lemma23SnappedHeight Q₂ = wz1Lemma23SnappedHeight Q₃ ∧
      wz1Lemma23SnappedGlobalBin rho f Q₂ = wz1Lemma23SnappedGlobalBin rho f Q₃ := by
    simpa [wz1Lemma23SnappedFourCycles, wz1Lemma23FourCycles] using h_path
  rcases h_all with
    ⟨_, h_localGrain12, h_localGrain43, h_height14, h_height23, h_globalBin23⟩
  have h_y12 : Q₁.2.1 = Q₂.2.1 := (Prod.ext_iff.mp h_localGrain12).1
  have h_floor12 : Int.floor (wz1Lemma23LocalCoordinate g q₁ / rho) =
        Int.floor (wz1Lemma23LocalCoordinate g q₂ / rho) :=
    (Prod.ext_iff.mp h_localGrain12).2
  have h_y43 : Q₄.2.1 = Q₃.2.1 := (Prod.ext_iff.mp h_localGrain43).1
  have h_floor43 : Int.floor (wz1Lemma23LocalCoordinate g q₄ / rho) =
        Int.floor (wz1Lemma23LocalCoordinate g q₃ / rho) :=
    (Prod.ext_iff.mp h_localGrain43).2
  have h_local12 :
      |wz1Lemma23LocalCoordinate g q₁ - wz1Lemma23LocalCoordinate g q₂| ≤ rho :=
    le_of_lt (wz1Lemma23_abs_sub_lt_of_floor_div_eq h_rho h_floor12)
  have h_local34 :
      |wz1Lemma23LocalCoordinate g q₃ - wz1Lemma23LocalCoordinate g q₄| ≤ rho := by
    have h : |wz1Lemma23LocalCoordinate g q₄ - wz1Lemma23LocalCoordinate g q₃| < rho :=
      wz1Lemma23_abs_sub_lt_of_floor_div_eq h_rho h_floor43
    have h' : |wz1Lemma23LocalCoordinate g q₃ - wz1Lemma23LocalCoordinate g q₄| =
        |wz1Lemma23LocalCoordinate g q₄ - wz1Lemma23LocalCoordinate g q₃| := by
      rw [show wz1Lemma23LocalCoordinate g q₃ - wz1Lemma23LocalCoordinate g q₄ =
        -(wz1Lemma23LocalCoordinate g q₄ - wz1Lemma23LocalCoordinate g q₃) by ring]
      rw [abs_neg]
    rw [h']
    exact le_of_lt h
  have h_global23 :
      |wz1Lemma23GlobalCoordinate f q₂ - wz1Lemma23GlobalCoordinate f q₃| ≤ rho :=
    le_of_lt (wz1Lemma23_abs_sub_lt_of_floor_div_eq h_rho h_globalBin23)
  have h_z14 : Q₁.2.2 = Q₄.2.2 := by
    simpa [wz1Lemma23SnappedHeight] using h_height14
  have h_z23 : Q₂.2.2 = Q₃.2.2 := by
    simpa [wz1Lemma23SnappedHeight] using h_height23
  have h_q12_y : q₁ 1 = q₂ 1 := by
    simp [hq₁, hq₂, wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3, h_y12]
  have h_q43_y : q₄ 1 = q₃ 1 := by
    simp [hq₄, hq₃, wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3, h_y43]
  have h_q14_z : q₁ 2 = q₄ 2 := by
    simp [hq₁, hq₄, wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3, h_z14]
  have h_q23_z : q₂ 2 = q₃ 2 := by
    simp [hq₂, hq₃, wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3, h_z23]
  have h_p1_z : p₁ 2 = 0 := by
    simp [hp₁, wz1Lemma23SkewPoint, point3, hbaseHeight]
  have h_p4_z : p₄ 2 = 0 := by
    simp [hp₄, wz1Lemma23SkewPoint, point3, hbaseHeight, h_q14_z]
  have h_p2_y : p₂ 1 = p₁ 1 := by
    simp [hp₁, hp₂, wz1Lemma23SkewPoint, point3, h_q12_y]
  have h_p4_y : p₄ 1 = p₃ 1 := by
    simp [hp₃, hp₄, wz1Lemma23SkewPoint, point3, h_q43_y]
  have h_p3_z : p₃ 2 = p₂ 2 := by
    simp [hp₂, hp₃, wz1Lemma23SkewPoint, point3, h_q23_z]
  have h_p1_x : p₁ 0 = wz1Lemma23GlobalCoordinate f q₁ := by
    simp [hp₁, wz1Lemma23SkewPoint, point3, wz1Lemma23GlobalCoordinate, hbaseHeight]
  have h_base' : |p₁ 0 - w| ≤ rho := by
    rw [h_p1_x]
    exact h_base
  have h_local_pres12 :
      wz1Lemma23LocalCoordinate centeredLocal p₁ -
          wz1Lemma23LocalCoordinate centeredLocal p₂ =
        wz1Lemma23LocalCoordinate g q₁ - wz1Lemma23LocalCoordinate g q₂ := by
    simpa [hp₁, hp₂, wz1Lemma23SkewPoint, point3, wz1Lemma23LocalCoordinate,
      centeredLocal, wz1Lemma23CenteredLocal, h_q12_y] using by ring
  have h_global_pres23 :
      wz1Lemma23GlobalCoordinate centeredSlope p₂ -
          wz1Lemma23GlobalCoordinate centeredSlope p₃ =
        wz1Lemma23GlobalCoordinate f q₂ - wz1Lemma23GlobalCoordinate f q₃ := by
    simpa [hp₂, hp₃, wz1Lemma23SkewPoint, point3, wz1Lemma23GlobalCoordinate,
      centeredSlope, wz1Lemma23CenteredSlope, h_q23_z, hbaseHeight] using by ring
  have h_local_pres34 :
      wz1Lemma23LocalCoordinate centeredLocal p₃ -
          wz1Lemma23LocalCoordinate centeredLocal p₄ =
        wz1Lemma23LocalCoordinate g q₃ - wz1Lemma23LocalCoordinate g q₄ := by
    simpa [hp₃, hp₄, wz1Lemma23SkewPoint, point3, wz1Lemma23LocalCoordinate,
      centeredLocal, wz1Lemma23CenteredLocal, h_q43_y] using by ring
  have h_local12' :
      |wz1Lemma23LocalCoordinate centeredLocal p₁ -
        wz1Lemma23LocalCoordinate centeredLocal p₂| ≤ rho := by
    rw [h_local_pres12]
    exact h_local12
  have h_global23' :
      |wz1Lemma23GlobalCoordinate centeredSlope p₂ -
        wz1Lemma23GlobalCoordinate centeredSlope p₃| ≤ rho := by
    rw [h_global_pres23]
    exact h_global23
  have h_local34' :
      |wz1Lemma23LocalCoordinate centeredLocal p₃ -
        wz1Lemma23LocalCoordinate centeredLocal p₄| ≤ rho := by
    rw [h_local_pres34]
    exact h_local34
  exact
    wz1_lemma23_four_cycle_dot_difference
      rho w centeredSlope centeredLocal p₁ p₂ p₃ p₄
      (le_of_lt h_rho) h_p1_z h_p4_z h_p2_y h_p4_y h_p3_z h_base'
      h_local12' h_global23' h_local34'

end Kakeya.Assouad
