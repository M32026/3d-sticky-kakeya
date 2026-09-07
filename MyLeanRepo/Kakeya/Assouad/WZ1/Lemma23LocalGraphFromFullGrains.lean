import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FullGrainNormalBound
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalGraphExtension

/-!
# Local graph from full local grains in WZ1 Lemma 23

For each selected y-anchor, the faithful full-grain argument supplies the
large first component of the plane normal.  The already closed McShane/clamp
extension then produces the bounded global local-graph function.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Source data for a finite family of selected local-grain anchors. -/
structure WZ1Lemma23FullGrainAnchorFamily
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) where
  sample : Finset ℝ
  anchor : ℝ → Point3
  normal : Point3 → Point3
  normal_vertical :
    ∀ y ∈ sample,
      |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2
  normal_dist :
    ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
      dist (normal (anchor y₁)) (normal (anchor y₂)) ≤
        dist (anchor y₁) (anchor y₂)
  anchor_dist :
    ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
      dist (anchor y₁) (anchor y₂) ≤
        4 * |y₁ - y₂|
  grainInput :
    ∀ y ∈ sample,
      WZ1Lemma23FullLocalGrainInput
        rho sigma eta C slope
  grain_normal :
    ∀ (y : ℝ) (hy : y ∈ sample),
      (grainInput y hy).normal =
        normal (anchor y)

/-- Source anchors carrying generalized full local-grain inputs. -/
structure WZ1Lemma23FullGrainAnchorFamilyGeneralized
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ) where
  sample : Finset ℝ
  anchor : ℝ → Point3
  normal : Point3 → Point3
  normal_vertical :
    ∀ y ∈ sample,
      |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2
  normal_dist :
    ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
      dist (normal (anchor y₁)) (normal (anchor y₂)) ≤
        dist (anchor y₁) (anchor y₂)
  anchor_dist :
    ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
      dist (anchor y₁) (anchor y₂) ≤
        4 * |y₁ - y₂|
  grainInput :
    ∀ y ∈ sample,
      WZ1Lemma23FullLocalGrainInputGeneralized
        rho sigma eta C slope
  grain_normal :
    ∀ (y : ℝ) (hy : y ∈ sample),
      (grainInput y hy).normal =
        normal (anchor y)

/--
Construct the local graph from a family of actual full local grains.
-/
theorem wz1_lemma23_local_graph_from_full_grains
    (hPlanar : WZ1Lemma23PlanarProjectionFullnessStatement)
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall : 12 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 10)
    (family :
      WZ1Lemma23FullGrainAnchorFamily
        rho sigma eta C slope) :
    ∃ g : ℝ → ℝ,
      LipschitzOnWith 64 g Set.univ ∧
      (∀ y, |g y| ≤ 2) ∧
      ∀ y ∈ family.sample,
        g y =
          family.normal (family.anchor y) (2 : Fin 3) /
            family.normal (family.anchor y) (0 : Fin 3) := by
  have hfirst :
      ∀ y ∈ family.sample,
        1 / 4 ≤
          |family.normal (family.anchor y) (0 : Fin 3)| := by
    intro y hy
    have hgrain :=
      wz1_lemma23_full_grain_normal_first_component
        hPlanar rho sigma eta C slope
        hrho hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall habsorb
        (family.grainInput y hy)
    rw [family.grain_normal y hy] at hgrain
    exact hgrain
  exact
    wz1_lemma23_local_graph_extension_of_distortion
      family.sample family.anchor family.normal
      family.normal_vertical hfirst
      family.normal_dist family.anchor_dist

/-- Construct the local graph from generalized full local grains. -/
theorem wz1_lemma23_local_graph_from_full_grains_generalized
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (family :
      WZ1Lemma23FullGrainAnchorFamilyGeneralized
        rho sigma eta C slope) :
    ∃ g : ℝ → ℝ,
      LipschitzOnWith 64 g Set.univ ∧
      (∀ y, |g y| ≤ 2) ∧
      ∀ y ∈ family.sample,
        g y =
          family.normal (family.anchor y) (2 : Fin 3) /
            family.normal (family.anchor y) (0 : Fin 3) := by
  have hfirst :
      ∀ y ∈ family.sample,
        1 / 4 ≤
          |family.normal (family.anchor y) (0 : Fin 3)| := by
    intro y hy
    have hgrain :=
      wz1_lemma23_full_grain_normal_first_component_generalized
        rho sigma eta C slope
        hrho hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall20 habsorb
        (family.grainInput y hy)
    rw [family.grain_normal y hy] at hgrain
    exact hgrain
  exact
    wz1_lemma23_local_graph_extension_of_distortion
      family.sample family.anchor family.normal
      family.normal_vertical hfirst
      family.normal_dist family.anchor_dist

end

end Kakeya.Assouad
