import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49RadialProjectionStatements

/-!
# Endpoint construction for WZ1 Lemma 8.13

Recover endpoint witnesses from the radial direction image used in the
normalized Kaufman package.
-/

namespace Kakeya.Assouad

/-- Choose one source point mapping to a supplied radial direction. -/
noncomputable def wz1Lemma49_firstEndpoint
    (viewpoint : Point2) (source : DiscreteSet 2)
    (direction : Point2) : Point2 :=
  if h :
      direction ∈
        source.image (wz1Lemma49RadialDirection viewpoint) then
    Classical.choose (Finset.mem_image.mp h)
  else
    direction

/-- The chosen first endpoint lies in the source set. -/
lemma wz1Lemma49_firstEndpoint_mem
    (viewpoint : Point2) (source : DiscreteSet 2)
    (direction : Point2)
    (hdirection :
      direction ∈
        source.image (wz1Lemma49RadialDirection viewpoint)) :
    wz1Lemma49_firstEndpoint viewpoint source direction ∈ source := by
  have heq :
      wz1Lemma49_firstEndpoint viewpoint source direction =
        Classical.choose (Finset.mem_image.mp hdirection) := by
    rw [wz1Lemma49_firstEndpoint, dif_pos hdirection]
  rw [heq]
  exact
    (Classical.choose_spec
      (Finset.mem_image.mp hdirection)).1

/-- The chosen first endpoint maps back to the supplied radial direction. -/
lemma wz1Lemma49_firstEndpoint_map
    (viewpoint : Point2) (source : DiscreteSet 2)
    (direction : Point2)
    (hdirection :
      direction ∈
        source.image (wz1Lemma49RadialDirection viewpoint)) :
    wz1Lemma49RadialDirection viewpoint
        (wz1Lemma49_firstEndpoint viewpoint source direction) =
      direction := by
  have heq :
      wz1Lemma49_firstEndpoint viewpoint source direction =
        Classical.choose (Finset.mem_image.mp hdirection) := by
    rw [wz1Lemma49_firstEndpoint, dif_pos hdirection]
  rw [heq]
  exact
    (Classical.choose_spec
      (Finset.mem_image.mp hdirection)).2

/-- The second endpoint is the fixed radial viewpoint. -/
def wz1Lemma49_secondEndpoint
    (viewpoint : Point2) (_direction : Point2) : Point2 :=
  viewpoint

/-- The direction is the normalized difference of the two endpoints. -/
lemma wz1Lemma49_direction_eq
    (viewpoint : Point2) (source : DiscreteSet 2)
    (direction : Point2)
    (hdirection :
      direction ∈
        source.image (wz1Lemma49RadialDirection viewpoint)) :
    direction =
      (‖wz1Lemma49_firstEndpoint viewpoint source direction -
          wz1Lemma49_secondEndpoint viewpoint direction‖⁻¹ : ℝ) •
        (wz1Lemma49_firstEndpoint viewpoint source direction -
          wz1Lemma49_secondEndpoint viewpoint direction) := by
  have hmap :=
    wz1Lemma49_firstEndpoint_map
      viewpoint source direction hdirection
  have hdefinition :
      wz1Lemma49RadialDirection viewpoint
          (wz1Lemma49_firstEndpoint viewpoint source direction) =
        (‖wz1Lemma49_firstEndpoint viewpoint source direction -
            viewpoint‖⁻¹ : ℝ) •
          (wz1Lemma49_firstEndpoint viewpoint source direction -
            viewpoint) := by
    rfl
  rw [hdefinition] at hmap
  simpa [wz1Lemma49_secondEndpoint] using hmap.symm

/-- A fixed viewpoint in `G₂` gives a valid second endpoint for every direction. -/
lemma wz1Lemma49_secondEndpoint_mem
    (viewpoint : Point2) (G₂ : DiscreteSet 2)
    (hviewpoint : viewpoint ∈ G₂) (direction : Point2) :
    wz1Lemma49_secondEndpoint viewpoint direction ∈ G₂ := by
  simpa [wz1Lemma49_secondEndpoint] using hviewpoint

end Kakeya.Assouad
