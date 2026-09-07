import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SpatialGrid
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23DotDifferenceStatements

/-!
# Coordinate labels for the WZ1 Lemma 23 cell graph

The four-cycle argument groups active spatial cells by three discretized
quantities:

* height at mesh `rho`;
* the local-grain `y` coordinate at mesh `sqrt rho`;
* the global-grain scalar coordinate at mesh `rho`.

The labels below are defined from the genuine shaded representative selected
in `Lemma23SpatialGrid`.  Equality of labels therefore gives the precise
coordinate-closeness estimates used to define local and global grain
relations.
-/

namespace Kakeya.Assouad

noncomputable section

/--
If two real numbers have the same floor after division by a positive mesh,
then they differ by less than that mesh.
-/
lemma wz1Lemma23_abs_sub_lt_of_floor_div_eq
    {a b mesh : ℝ} (hmesh : 0 < mesh)
    (hfloor : Int.floor (a / mesh) = Int.floor (b / mesh)) :
    |a - b| < mesh := by
  have ha_lower :
      (Int.floor (a / mesh) : ℝ) ≤ a / mesh :=
    Int.floor_le _
  have ha_upper :
      a / mesh < (Int.floor (a / mesh) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hb_lower :
      (Int.floor (b / mesh) : ℝ) ≤ b / mesh :=
    Int.floor_le _
  have hb_upper :
      b / mesh < (Int.floor (b / mesh) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hratio : |a / mesh - b / mesh| < 1 := by
    rw [abs_lt]
    constructor
    · rw [hfloor] at ha_lower ha_upper
      linarith
    · rw [← hfloor] at hb_lower hb_upper
      linarith
  have hdiv : |(a - b) / mesh| < 1 := by
    rw [sub_div]
    exact hratio
  rw [abs_div, abs_of_pos hmesh] at hdiv
  have hmul : |a - b| / mesh * mesh < 1 * mesh := by
    gcongr
  simpa [hmesh.ne'] using hmul

/-- The selected shaded point attached to one active spatial cell. -/
abbrev wz1Lemma23Representative
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (cell : WZ1Lemma23ActiveCell Y rho hrho) : Point3 :=
  wz1Lemma23CellRepresentative Y hrho cell

/-- Height label at the fine `rho` mesh. -/
def wz1Lemma23HeightLabel
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (cell : WZ1Lemma23ActiveCell Y rho hrho) : ℤ :=
  Int.floor ((wz1Lemma23Representative Y hrho cell) 2 / rho)

/-- Local-grain `y` label at mesh `sqrt rho`. -/
def wz1Lemma23LocalYLabel
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (cell : WZ1Lemma23ActiveCell Y rho hrho) : ℤ :=
  Int.floor
    ((wz1Lemma23Representative Y hrho cell) 1 / Real.sqrt rho)

/-- Global-grain scalar-coordinate label at the fine `rho` mesh. -/
def wz1Lemma23GlobalBin
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (slope : ℝ → ℝ)
    (cell : WZ1Lemma23ActiveCell Y rho hrho) : ℤ :=
  Int.floor
    (wz1Lemma23GlobalCoordinate slope
        (wz1Lemma23Representative Y hrho cell) / rho)

/-- Equal height labels place the representatives within one `rho` interval. -/
lemma wz1Lemma23_height_close_of_label_eq
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    {first second : WZ1Lemma23ActiveCell Y rho hrho}
    (h :
      wz1Lemma23HeightLabel Y hrho first =
        wz1Lemma23HeightLabel Y hrho second) :
    |(wz1Lemma23Representative Y hrho first) 2 -
        (wz1Lemma23Representative Y hrho second) 2| < rho := by
  exact wz1Lemma23_abs_sub_lt_of_floor_div_eq hrho h

/--
Equal local `y` labels place the representatives within one `sqrt rho`
interval.
-/
lemma wz1Lemma23_localY_close_of_label_eq
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    {first second : WZ1Lemma23ActiveCell Y rho hrho}
    (h :
      wz1Lemma23LocalYLabel Y hrho first =
        wz1Lemma23LocalYLabel Y hrho second) :
    |(wz1Lemma23Representative Y hrho first) 1 -
        (wz1Lemma23Representative Y hrho second) 1| <
      Real.sqrt rho := by
  exact
    wz1Lemma23_abs_sub_lt_of_floor_div_eq
      (Real.sqrt_pos.mpr hrho) h

/--
Equal global-grain labels place the scalar coordinates within one `rho`
interval.
-/
lemma wz1Lemma23_globalCoordinate_close_of_label_eq
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (slope : ℝ → ℝ)
    {first second : WZ1Lemma23ActiveCell Y rho hrho}
    (h :
      wz1Lemma23GlobalBin Y hrho slope first =
        wz1Lemma23GlobalBin Y hrho slope second) :
    |wz1Lemma23GlobalCoordinate slope
          (wz1Lemma23Representative Y hrho first) -
        wz1Lemma23GlobalCoordinate slope
          (wz1Lemma23Representative Y hrho second)| < rho := by
  exact wz1Lemma23_abs_sub_lt_of_floor_div_eq hrho h

end

end Kakeya.Assouad
