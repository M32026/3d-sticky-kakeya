import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridData
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridData.RealPowerGrid
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridData.TailSchedule
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.MultiscaleShiftData
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.GridLabelMaps

/-!
# Assembly of fixed-depth power-grid data

Construct the `FixedDepthPowerGrid`, `MultiscaleShiftData`, and
`GridLabelMaps` for `s_k = δ^(k/N)`.
-/

noncomputable section

open BigOperators Finset
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridTail

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- The literal power grid and tail-radius schedule used by the fixed-depth
construction. -/
def canonicalFixedDepthPowerGrid
    (N : ℕ) (hN : 0 < N)
    (delta : ℝ) (hδ_pos : 0 < delta) (hδ_lt_one : delta < 1) :
    FixedDepthPowerGrid delta N where
  scale := fun k =>
    ⟨realScale delta N k.val,
      realScaleGrid_range delta N hN hδ_pos hδ_lt_one
        k.val (by omega)⟩
  radius := fun k =>
    FixedDepthPowerGridTail.radius delta N k
  hpower := fun k =>
    realScaleGrid_ennreal delta N k.val
  hfirst :=
    realScaleGrid_zero delta N
  hlast :=
    realScaleGrid_N delta N hN
  hstrict := fun k =>
    realScaleGrid_strict_desc
      delta N hN hδ_pos hδ_lt_one k.val k.is_lt
  hratio := fun k =>
    realScaleGrid_ratio delta N hN hδ_pos k.val
  hradius_pos := fun k =>
    radius_pos hδ_pos hδ_lt_one hN k
  htail := fun k =>
    tail_suffix_bound hδ_pos hδ_lt_one hN k
  htotal :=
    total_radius_le_one hδ_pos hδ_lt_one hN
  hbracket := fun rho => by
    rcases realScaleGrid_bracket delta N hN hδ_pos hδ_lt_one
        rho.1 rho.2.1 rho.2.2 with
      ⟨k, hk, h1, h2⟩
    exact ⟨⟨k, hk⟩, h1, h2⟩

@[simp]
lemma canonicalFixedDepthPowerGrid_scale
    (N : ℕ) (hN : 0 < N)
    (delta : ℝ) (hδ_pos : 0 < delta) (hδ_lt_one : delta < 1)
    (k : Fin (N + 1)) :
    ((canonicalFixedDepthPowerGrid
      N hN delta hδ_pos hδ_lt_one).scale k).1 =
      realScale delta N k.val :=
  rfl

@[simp]
lemma canonicalFixedDepthPowerGrid_radius
    (N : ℕ) (hN : 0 < N)
    (delta : ℝ) (hδ_pos : 0 < delta) (hδ_lt_one : delta < 1)
    (k : Fin N) :
    (canonicalFixedDepthPowerGrid
      N hN delta hδ_pos hδ_lt_one).radius k =
      FixedDepthPowerGridTail.radius delta N k :=
  rfl

@[simp]
lemma canonicalFixedDepthPowerGrid_fineScale
    (N : ℕ) (hN : 0 < N)
    (delta : ℝ) (hδ_pos : 0 < delta) (hδ_lt_one : delta < 1)
    (k : Fin N) :
    ((canonicalFixedDepthPowerGrid
      N hN delta hδ_pos hδ_lt_one).fineScale k).1 =
      realScale delta N (k.val + 1) :=
  rfl

@[simp]
lemma canonicalFixedDepthPowerGrid_coarseScale
    (N : ℕ) (hN : 0 < N)
    (delta : ℝ) (hδ_pos : 0 < delta) (hδ_lt_one : delta < 1)
    (k : Fin N) :
    (canonicalFixedDepthPowerGrid
      N hN delta hδ_pos hδ_lt_one).coarseScale k =
      realScale delta N k.val :=
  rfl

/-- Construct the grid and all deterministic shift data for fixed `N, δ`. -/
lemma fixed_depth_power_grid_aux (N : ℕ) (hN : 0 < N)
    (delta : ℝ) (hδ_pos : 0 < delta) (hδ_lt_one : delta < 1) :
    ∃ grid : FixedDepthPowerGrid delta N,
      ∀ {F : TubeFamily delta} {U : UniformTubeStructure F}
        {Y : TubeShading F}
        (J : Fin N → ℕ) (hJ_pos : ∀ k, 0 < J k)
        (shiftAt : (k : Fin N) → Fin (J k) → Point3)
        (hshift : ∀ k j, ‖shiftAt k j‖ ≤ grid.radius k),
        ∃ (data : MultiscaleShiftData delta N)
          (gm : GridLabelMaps U Y data),
          data.sigma = grid.fineScale ∧
          data.J = J ∧
          HEq data.shiftAt shiftAt ∧
          data.radius = grid.radius ∧
          gm.fineScale = grid.fineScale ∧
          gm.coarseScale = grid.coarseScale := by
  let grid :=
    canonicalFixedDepthPowerGrid
      N hN delta hδ_pos hδ_lt_one
  refine ⟨grid, ?_⟩
  intro F U Y J hJ_pos shiftAt hshift
  let data : MultiscaleShiftData delta N := {
    sigma := grid.fineScale
    J := J
    hJ_pos := hJ_pos
    shiftAt := shiftAt
    radius := grid.radius
    hradius_nonneg := fun k => (grid.hradius_pos k).le
    hshift_norm := hshift
    h_total_radius := grid.htotal.trans (by norm_num)
  }
  have hscale :
      ∀ k : Fin N,
        (grid.fineScale k).1 ≤ grid.coarseScale k := fun k =>
    (grid.hstrict k).le
  have htail' :
      ∀ k : Fin N,
        (∑ j ∈ Finset.univ.filter
          (fun j : Fin N => k.val ≤ j.val), data.radius j) ≤
            grid.coarseScale k - (grid.fineScale k).1 := by
    intro k
    exact grid.htail k
  refine ⟨data,
    GridLabelMaps.exists_gridLabelMaps
      grid.fineScale grid.coarseScale hscale htail', ?_⟩
  exact ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩

end Kakeya.Streamlined.RandomTranslation.WithShading

end
