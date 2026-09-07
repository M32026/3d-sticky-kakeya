import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectionArea
import MyLeanRepo.Kakeya.Assouad.Targets.CompactTubeTwistedProjectionArea.CoordEquiv
import MyLeanRepo.Kakeya.Assouad.Targets.CompactTubeTwistedProjectionArea.TubeYDiameter

/-!
WZ2 Section 7: bound one compact shaded tube's mass by its twisted-projection
area times the explicit tube-width factor.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

theorem compact_tube_twisted_projection_area :
    CompactTubeTwistedProjectionAreaStatement := by
  intro delta hdelta F hF Z hZcompact f i
  have h_twisted_cont : Continuous (twistedProjection f) :=
    continuous_twistedProjection f
  have h_img_compact :
      IsCompact (twistedProjection f '' Z.carrier i) :=
    (hZcompact i).image h_twisted_cont
  have h_meas :
      MeasurableSet (twistedProjection f '' Z.carrier i) :=
    h_img_compact.measurableSet
  let A : Set (ℝ × (ℝ × ℝ)) := coordEquiv3 '' Z.carrier i
  let D : ℝ := 10 * delta
  have hD : 0 < D := by
    positivity
  have hA_compact : IsCompact A :=
    (hZcompact i).image continuous_coordEquiv3
  have hA_meas : MeasurableSet A := hA_compact.measurableSet
  have h_y_diam :
      ∀ z y1 y2,
        (∃ x1 x2, (z, (x1, y1)) ∈ A ∧ (z, (x2, y2)) ∈ A) →
          |y1 - y2| ≤ D := by
    intro z y1 y2 h
    have h6 : |y1 - y2| ≤ 6 * delta :=
      tube_y_diameter_bound hdelta (hF i)
        (Z.subset_body i) z y1 y2 h
    dsimp only [D]
    linarith
  let π_f : ℝ × (ℝ × ℝ) → ℝ × ℝ :=
    fun p => (p.2.1 + f p.1 * p.2.2, p.1)
  have h_main :
      volume (π_f '' A) ≥
        volume A / ENNReal.ofReal (2 * D) :=
    projection3d_volume_lower hD hA_meas
      f.contDiff.continuous h_y_diam
  have h_vol_A : volume A = volume (Z.carrier i) :=
    volume_image_of_injective_measurePreserving
      continuous_coordEquiv3 measurePreserving_coordEquiv3
        injective_coordEquiv3 (hZcompact i)
  have h_comm :
      π_f '' A =
        coordEquiv2 '' (twistedProjection f '' Z.carrier i) := by
    ext ⟨u, z⟩
    simp only [Set.mem_image, A, π_f]
    constructor
    · rintro ⟨_, ⟨p3, hp3, rfl⟩, h_eq⟩
      refine ⟨twistedProjection f p3, ⟨p3, hp3, rfl⟩, ?_⟩
      exact (twistedProjection_coordEquiv_diagram f p3).trans h_eq
    · rintro ⟨_, ⟨p3, hp3, rfl⟩, h_eq⟩
      refine ⟨coordEquiv3 p3, ⟨p3, hp3, rfl⟩, ?_⟩
      exact
        (twistedProjection_coordEquiv_diagram f p3).symm.trans h_eq
  have h_vol_img :
      volume (π_f '' A) =
        volume (twistedProjection f '' Z.carrier i) := by
    rw [h_comm]
    exact volume_image_of_injective_measurePreserving
      continuous_coordEquiv2 measurePreserving_coordEquiv2
        injective_coordEquiv2 h_img_compact
  rw [h_vol_A, h_vol_img] at h_main
  set c : ENNReal := ENNReal.ofReal (2 * D) with hc
  have h_pos : 0 < c := by
    rw [hc]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have h_ne_top : c ≠ ⊤ := by
    rw [hc]
    exact ENNReal.ofReal_ne_top
  have h_final :
      volume (Z.carrier i) ≤
        c * volume (twistedProjection f '' Z.carrier i) := by
    have h2 :
        volume (Z.carrier i) / c * c =
          volume (Z.carrier i) :=
      ENNReal.div_mul_cancel (a := c)
        (b := volume (Z.carrier i)) h_pos.ne' h_ne_top
    calc
      volume (Z.carrier i)
          = volume (Z.carrier i) / c * c := h2.symm
      _ ≤ volume (twistedProjection f '' Z.carrier i) * c := by
            gcongr
      _ = c * volume (twistedProjection f '' Z.carrier i) := by
            ring
  have h_D_eq : c = ENNReal.ofReal (20 * delta) := by
    rw [hc]
    congr 1
    dsimp only [D]
    ring
  rw [h_D_eq] at h_final
  exact ⟨h_meas, h_final⟩

end Kakeya.Assouad
