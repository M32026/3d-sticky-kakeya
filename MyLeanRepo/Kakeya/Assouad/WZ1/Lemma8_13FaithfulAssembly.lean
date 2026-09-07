import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements

/-!
# Assemble the faithful PDF Lemma 8.13 leaves

This module contains only threshold bookkeeping and dependent witness
threading.  All mathematical work is isolated in the three faithful leaves.
-/

namespace Kakeya.Assouad

theorem wz1_lemma8_13_faithful_assembly :
    WZ1Lemma8_13FaithfulAssemblyStatement := by
  intro hAffine hKaufman hClosing
  intro epsilon hepsilon hepsilonOne
  rcases hAffine epsilon hepsilon hepsilonOne with
    ⟨deltaAffine, hdeltaAffine, hdeltaAffineOne, hAffineAt⟩
  rcases hKaufman epsilon hepsilon hepsilonOne with
    ⟨deltaKaufman, hdeltaKaufman, hdeltaKaufmanOne, hKaufmanAt⟩
  rcases hClosing epsilon hepsilon hepsilonOne with
    ⟨deltaClosing, hdeltaClosing, hdeltaClosingOne, hClosingAt⟩
  let delta₀ := min deltaAffine (min deltaKaufman deltaClosing)
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hdeltaAffine, hdeltaKaufman, hdeltaClosing]
  have hdelta₀One : delta₀ ≤ 1 := by
    exact (min_le_left _ _).trans hdeltaAffineOne
  let eta := wz1Lemma8_13FaithfulEta epsilon
  have heta : 0 < eta := by
    dsimp only [eta, wz1Lemma8_13FaithfulEta]
    positivity
  refine ⟨eta, delta₀, heta, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaLe
  have hdeltaAffineLe : delta ≤ deltaAffine :=
    hdeltaLe.trans (min_le_left _ _)
  have hdeltaKaufmanLe : delta ≤ deltaKaufman :=
    hdeltaLe.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaClosingLe : delta ≤ deltaClosing :=
    hdeltaLe.trans
      ((min_le_right _ _).trans (min_le_right _ _))
  intro F G₁ G₂ hF hG₁ hG₂
    hFball hG₁ball hG₂ball
    hFseparated hG₁separated hG₂separated
    hFfrostman hG₁frostman hG₂frostman
    hstandard H hDensity
    base direction hdirection
    width hwidth hdeltaWidth hG₁strip
    activeWidth hFstrip hlarge
  let input :
      WZ1Lemma8_13ResidualInput delta epsilon eta :=
    { F := F
      G₁ := G₁
      G₂ := G₂
      H := H
      F_nonempty := hF
      G₁_nonempty := hG₁
      G₂_nonempty := hG₂
      F_ball := hFball
      G₁_ball := hG₁ball
      G₂_ball := hG₂ball
      F_separated := hFseparated
      G₁_separated := hG₁separated
      G₂_separated := hG₂separated
      F_frostman := hFfrostman
      G₁_frostman := hG₁frostman
      G₂_frostman := hG₂frostman
      standardSeparation := hstandard
      density := hDensity
      base := base
      direction := direction
      direction_unit := hdirection
      width := width
      width_pos := hwidth
      delta_le_width := hdeltaWidth
      G₁_strip := hG₁strip
      F_strip := by
        simpa only [activeWidth] using hFstrip
      active_width_large := by
        simpa only [activeWidth] using hlarge }
  have hetaEq :
      eta = wz1Lemma8_13FaithfulEta epsilon := rfl
  rcases
      hAffineAt delta hdelta hdeltaAffineLe
        (hetaEq ▸ input) with
    ⟨affine⟩
  rcases
      hKaufmanAt delta hdelta hdeltaKaufmanLe
        (hetaEq ▸ input) affine with
    ⟨kaufman⟩
  rcases
      hClosingAt delta hdelta hdeltaClosingLe
        (hetaEq ▸ input) affine kaufman with
    ⟨closing⟩
  exact
    ⟨closing.rho, 0, closing.transportedRadius,
      closing.rho_lower, closing.rho_upper,
      closing.transportedRadius_pos,
      closing.long_radius, closing.covering⟩

end Kakeya.Assouad
