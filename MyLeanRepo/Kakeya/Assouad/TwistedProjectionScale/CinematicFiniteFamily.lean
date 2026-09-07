import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters
import MyLeanRepo.Kakeya.Assouad.Targets.CinematicFamilyFromSlope
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Construction
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.LowerBound
import MyLeanRepo.Kakeya.Cinematic.Definitions

/-!
# Cinematic finite family from a tube family

Maps selected tubes in a c-window to cinematic slope curves, with parameter
rescaling to fit the standard `[-1,1]^3` cinematic parameter cube.

Whiteprint node: `cinematic_finite_family`.
-/

noncomputable section

open Kakeya.Cinematic Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Rescale tube parameters to fit the standard cinematic parameter cube. -/
def scaledParams (p : TubeParams) : ℝ × ℝ × ℝ :=
  (p.a / 12, p.b / 12, p.d / 2)

/-- A canonical point in the unit interval. -/
def midpoint : UnitPoint := ⟨1 / 2, by norm_num [Kakeya.Cinematic.unitInterval]⟩

/--
Construct a finite cinematic family by mapping each selected tube to its
rescaled cinematic slope curve.
-/
def cinematicFiniteFamily {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (f : SlopeFunction) (selected : Finset (Fin F.card)) :
    FiniteFunctionFamily :=
  let img : Finset C2Function :=
    selected.image (fun i =>
      let p := scaledParams (tubeParams i)
      slopeCurve f p.1 p.2.1 p.2.2)
  ⟨(img : Set C2Function), Finset.finite_toSet img⟩

/-- The standard cinematic family for a given slope, with its constants. -/
lemma standard_cinematic_family
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    ∃ (family : Set C2Function) (K D : ℝ),
      1 ≤ K ∧ 1 ≤ D ∧
      IsSlopeCurveFamily family f ∧
      IsCinematicFamily family K D := by
  rcases cinematic_family_from_slope with ⟨K, D, hK1, hD1, h_main⟩
  rcases h_main f h_ns h0 with ⟨family, h_family_def, h_cinematic⟩
  exact ⟨family, K, D, hK1, hD1, h_family_def, h_cinematic⟩

/-- Every function in the finite family belongs to the standard cinematic family. -/
lemma cinematicFiniteFamily_mem
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (f : SlopeFunction)
    (selected : Finset (Fin F.card))
    (hbase : HasBoundedBase F 4) (hvert : IsInVerticalChart F)
    (family : Set C2Function)
    (h_family : IsSlopeCurveFamily family f) :
    ∀ g ∈ (cinematicFiniteFamily f selected).carrier, g ∈ family := by
  intro g hg
  have h_img : ∃ (i : Fin F.card), i ∈ selected ∧
      (let p := scaledParams (tubeParams i)
       slopeCurve f p.1 p.2.1 p.2.2) = g := by
    have h2 : g ∈ (cinematicFiniteFamily f selected).carrier := hg
    simpa [cinematicFiniteFamily, Finset.mem_image, eq_comm] using h2
  rcases h_img with ⟨i, _, rfl⟩
  let p := scaledParams (tubeParams i)
  have ha : p.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    dsimp only [p, scaledParams]
    have h_bounds := tubeParams_ab_bounds hbase hvert i
    have h_abs : |(tubeParams i).a| ≤ 12 := h_bounds.1
    have h11 : -12 ≤ (tubeParams i).a := (abs_le.mp h_abs).1
    have h12 : (tubeParams i).a ≤ 12 := (abs_le.mp h_abs).2
    exact ⟨by linarith, by linarith⟩
  have hb : p.2.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    dsimp only [p, scaledParams]
    have h_bounds := tubeParams_ab_bounds hbase hvert i
    have h_abs : |(tubeParams i).b| ≤ 12 := h_bounds.2
    have h11 : -12 ≤ (tubeParams i).b := (abs_le.mp h_abs).1
    have h12 : (tubeParams i).b ≤ 12 := (abs_le.mp h_abs).2
    exact ⟨by linarith, by linarith⟩
  have hd : p.2.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    dsimp only [p, scaledParams]
    have h_bounds := tubeParams_cd_bounds hvert i
    have h_abs : |(tubeParams i).d| ≤ 2 := h_bounds.2
    have h11 : -2 ≤ (tubeParams i).d := (abs_le.mp h_abs).1
    have h12 : (tubeParams i).d ≤ 2 := (abs_le.mp h_abs).2
    exact ⟨by linarith, by linarith⟩
  have hrep : RepresentsSlopeCurve (slopeCurve f p.1 p.2.1 p.2.2) f p.1 p.2.1 p.2.2 :=
    slopeCurve_represents f p.1 p.2.1 p.2.2
  exact (h_family (slopeCurve f p.1 p.2.1 p.2.2)).mpr
    ⟨p.1, ha, p.2.1, hb, p.2.2, hd, hrep⟩

/--
Conditional cinematic separation: if the rescaled L1 parameter distance between
two tubes is at least `c * δ`, then their cinematic C² distance is at least
`(11 / 30000) * c * δ`.
-/
lemma cinematicFiniteFamily_conditional_separation
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (i j : Fin F.card) (c : ℝ) (_hc : 0 ≤ c) (_hδ : 0 < δ)
    (h_sep : |(tubeParams i).a - (tubeParams j).a| / 12 +
             |(tubeParams i).b - (tubeParams j).b| / 12 +
             |(tubeParams i).d - (tubeParams j).d| / 2 ≥ c * δ) :
    c * (δ * (11 / 30000 : ℝ)) ≤
      c2Distance
        (slopeCurve f ((tubeParams i).a / 12) ((tubeParams i).b / 12) ((tubeParams i).d / 2))
        (slopeCurve f ((tubeParams j).a / 12) ((tubeParams j).b / 12) ((tubeParams j).d / 2)) := by
  set a1 := (tubeParams i).a / 12 with ha1
  set b1 := (tubeParams i).b / 12 with hb1
  set d1 := (tubeParams i).d / 2 with hd1
  set a2 := (tubeParams j).a / 12 with ha2
  set b2 := (tubeParams j).b / 12 with hb2
  set d2 := (tubeParams j).d / 2 with hd2
  set P : ℝ := |a1 - a2| + |b1 - b2| + |d1 - d2| with hP
  have h_abs_div_a : |a1 - a2| = |(tubeParams i).a - (tubeParams j).a| / 12 := by
    rw [ha1, ha2]
    have h : |(tubeParams i).a / 12 - (tubeParams j).a / 12| = |(tubeParams i).a - (tubeParams j).a| / 12 := by
      rw [show (tubeParams i).a / 12 - (tubeParams j).a / 12 = ((tubeParams i).a - (tubeParams j).a) / 12 by ring]
      rw [abs_div]
      norm_num
    exact h
  have h_abs_div_b : |b1 - b2| = |(tubeParams i).b - (tubeParams j).b| / 12 := by
    rw [hb1, hb2]
    have h : |(tubeParams i).b / 12 - (tubeParams j).b / 12| = |(tubeParams i).b - (tubeParams j).b| / 12 := by
      rw [show (tubeParams i).b / 12 - (tubeParams j).b / 12 = ((tubeParams i).b - (tubeParams j).b) / 12 by ring]
      rw [abs_div]
      norm_num
    exact h
  have h_abs_div_d : |d1 - d2| = |(tubeParams i).d - (tubeParams j).d| / 2 := by
    rw [hd1, hd2]
    have h : |(tubeParams i).d / 2 - (tubeParams j).d / 2| = |(tubeParams i).d - (tubeParams j).d| / 2 := by
      rw [show (tubeParams i).d / 2 - (tubeParams j).d / 2 = ((tubeParams i).d - (tubeParams j).d) / 2 by ring]
      rw [abs_div]
      norm_num
    exact h
  have hP_eq : P = |(tubeParams i).a - (tubeParams j).a| / 12 +
      |(tubeParams i).b - (tubeParams j).b| / 12 +
      |(tubeParams i).d - (tubeParams j).d| / 2 := by
    rw [hP, h_abs_div_a, h_abs_div_b, h_abs_div_d]
  have hP_ge : P ≥ c * δ := by
    rw [hP_eq]; exact h_sep
  let g1 := slopeCurve f a1 b1 d1
  let g2 := slopeCurve f a2 b2 d2
  have hrep1 : RepresentsSlopeCurve g1 f a1 b1 d1 := slopeCurve_represents f a1 b1 d1
  have hrep2 : RepresentsSlopeCurve g2 f a2 b2 d2 := slopeCurve_represents f a2 b2 d2
  have h_lower : (99 / 7500 : ℝ) * P ≤ jetGap g1 g2 midpoint :=
    slopeCurve_jetGap_ge f h_ns h0 g1 g2 a1 b1 d1 a2 b2 d2 hrep1 hrep2 midpoint
  have h_upper : jetGap g1 g2 midpoint ≤ 3 * c2Distance g1 g2 :=
    jetGap_le_three_mul_c2Distance g1 g2 midpoint
  have h_main : (99 / 7500 : ℝ) * P ≤ 3 * c2Distance g1 g2 := by
    linarith
  have h_coeff : (11 / 30000 : ℝ) ≤ (99 / 7500 : ℝ) / 3 := by norm_num
  have h_final : (11 / 30000 : ℝ) * P ≤ c2Distance g1 g2 := by
    calc (11 / 30000 : ℝ) * P
      ≤ ((99 / 7500 : ℝ) / 3) * P := by gcongr
    _ = (99 / 7500 : ℝ) * P / 3 := by ring
    _ ≤ c2Distance g1 g2 := by linarith
  have h_goal : (11 / 30000 : ℝ) * (c * δ) ≤ c2Distance g1 g2 := by
    have h_mult : (11 / 30000 : ℝ) * (c * δ) ≤ (11 / 30000 : ℝ) * P :=
      mul_le_mul_of_nonneg_left hP_ge (by norm_num)
    calc (11 / 30000 : ℝ) * (c * δ)
      ≤ (11 / 30000 : ℝ) * P := h_mult
    _ ≤ c2Distance g1 g2 := h_final
  have h_eq : c * (δ * (11 / 30000 : ℝ)) = (11 / 30000 : ℝ) * (c * δ) := by ring
  rw [h_eq]
  exact h_goal

/-- Cardinality of the cinematic finite family. -/
lemma cinematicFiniteFamily_card
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (f : SlopeFunction) (selected : Finset (Fin F.card)) :
    (cinematicFiniteFamily f selected).carrier.ncard =
      (selected.image (fun i : Fin F.card =>
        let p := scaledParams (tubeParams i)
        slopeCurve f p.1 p.2.1 p.2.2)).card := by
  have h : (cinematicFiniteFamily f selected).carrier =
      (selected.image (fun i : Fin F.card =>
        let p := scaledParams (tubeParams i)
        slopeCurve f p.1 p.2.1 p.2.2) : Set C2Function) := by
    rfl
  rw [h]
  exact ncard_coe_finset (selected.image (fun i : Fin F.card =>
    let p := scaledParams (tubeParams i)
    slopeCurve f p.1 p.2.1 p.2.2))

end Kakeya.Assouad
