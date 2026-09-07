import MyLeanRepo.Kakeya.Cinematic.Section5.ProductScalePairIncidenceInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.PerPair

/-!
# Product-scale fixed-pair incidence
-/

namespace Kakeya.Cinematic

theorem product_scale_fixed_pair_incidence :
    ProductScaleFixedPairIncidenceStatement := by
  intro hTangency K D hK hD
  obtain ⟨C_geometry, hC_geometry_pos, hgeometry⟩ :=
    hTangency K D hK hD
  let C_pair : ℝ := 20 * C_geometry
  have hC_pair_pos : 0 < C_pair := by positivity
  refine' ⟨C_pair, hC_pair_pos, _⟩
  intro delta t metricLower tangencyLower Cc
    hdelta ht hmetricLower htangencyLower hgeom_small hCc hadm
    family hfamily I hI w b hw hb hwb hmetric htangency
    R hRquarter hRincomp hcounts
  exact product_scale_fixed_pair_tangent_bound_core
    (hK := hK) (hD := hD) (hfamily := hfamily) (hI := hI)
    (hdelta := hdelta) (ht := ht)
    (hmetricLower := hmetricLower) (htangencyLower := htangencyLower)
    (hgeom_small := hgeom_small) (hCc := hCc) (hadm := hadm)
    (w := w) (b := b) (hw := hw) (hb := hb) (hwb := hwb)
    (hmetric := hmetric) (htangency := htangency)
    (hC_geometry := hC_geometry_pos) (hgeometry := hgeometry)
    (hRquarter := hRquarter) (hRincomp := hRincomp)
    (hcounts := hcounts)

end Kakeya.Cinematic
