import MyLeanRepo.Kakeya.Assouad.WZ1.WideBranchProjectionHelpers

/-!
# Line nonconcentration and Frostman subset transfer

Restrict line-nonconcentration and Frostman estimates from an ambient
vertex class to a selected subset, absorbing a retention/cardinality factor
into the exponent or constant.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Local copy of the power identity matching `WZ1LineNonConcentration`. -/
private lemma local_line_power_identity
    {tau radius lambda zeta : ℝ}
    (htau : 0 < tau) (hradius : 0 < radius) :
    Kakeya.realRpowENN (Real.rpow tau (-lambda) * radius) zeta =
      Kakeya.realRpowENN tau (-lambda * zeta) *
        Kakeya.realRpowENN radius zeta := by
  have hbase : 0 < Real.rpow tau (-lambda) :=
    Real.rpow_pos_of_pos htau _
  have hiterated :
      Kakeya.realRpowENN tau (-lambda * zeta) =
        Kakeya.realRpowENN (Real.rpow tau (-lambda)) zeta := by
    simp only [Kakeya.realRpowENN]
    congr 1
    exact Real.rpow_mul htau.le (-lambda) zeta
  rw [hiterated]
  exact realRpowENN_mul hbase hradius zeta

/--
Transfer line nonconcentration from an ambient set to a selected subset,
absorbing a retention factor into the exponent.

Given ambient nonconcentration with exponent `lambda` and a retention factor
`retentionInv` such that `|ambient| ≤ retentionInv * |selected|`, produce
nonconcentration on `selected` with exponent `lambda'` provided the retention
factor is absorbed by the exponent gap.
-/
lemma WZ1LineNonConcentration.transfer_subset
    {tau lambda lambda' zeta : ℝ}
    {ambient selected : DiscreteSet 2}
    {retentionInv : ENNReal}
    (h : WZ1LineNonConcentration tau lambda zeta ambient)
    (hsub : selected ⊆ ambient)
    (hretention : ambient.enncard ≤ retentionInv * selected.enncard)
    (habsorb : Kakeya.realRpowENN tau (-lambda * zeta) * retentionInv ≤
               Kakeya.realRpowENN tau (-lambda' * zeta))
    (htau : 0 < tau) (htauOne : tau ≤ 1) (hzeta : 0 ≤ zeta) :
    WZ1LineNonConcentration tau lambda' zeta selected := by
  intro normal hnormal level radius htauRadius hradiusOne
  have hradius : 0 < radius := htau.trans_le htauRadius
  let strip : Point2 → Prop :=
    fun point => |inner ℝ point normal - level| ≤ radius
  have hcount :
      ((selected.filter strip).card : ENNReal) ≤
        ((ambient.filter strip).card : ENNReal) := by
    exact_mod_cast
      Finset.card_le_card
        (Finset.filter_subset_filter strip hsub)
  have hambient :
      ((ambient.filter strip).card : ENNReal) ≤
        Kakeya.realRpowENN (Real.rpow tau (-lambda) * radius) zeta *
          ambient.enncard :=
    h normal hnormal level radius htauRadius hradiusOne
  have hpower_id :
      Kakeya.realRpowENN (Real.rpow tau (-lambda) * radius) zeta =
        Kakeya.realRpowENN tau (-lambda * zeta) *
          Kakeya.realRpowENN radius zeta :=
    local_line_power_identity htau hradius
  have hpower_id' :
      Kakeya.realRpowENN (Real.rpow tau (-lambda') * radius) zeta =
        Kakeya.realRpowENN tau (-lambda' * zeta) *
          Kakeya.realRpowENN radius zeta :=
    local_line_power_identity htau hradius
  calc
    ((selected.filter strip).card : ENNReal)
      ≤ Kakeya.realRpowENN (Real.rpow tau (-lambda) * radius) zeta *
          ambient.enncard := hcount.trans hambient
    _ = (Kakeya.realRpowENN tau (-lambda * zeta) *
           Kakeya.realRpowENN radius zeta) * ambient.enncard := by
        rw [hpower_id]
    _ ≤ (Kakeya.realRpowENN tau (-lambda * zeta) *
           Kakeya.realRpowENN radius zeta) *
          (retentionInv * selected.enncard) := by gcongr
    _ = (Kakeya.realRpowENN tau (-lambda * zeta) * retentionInv) *
          Kakeya.realRpowENN radius zeta * selected.enncard := by
        ring
    _ ≤ Kakeya.realRpowENN tau (-lambda' * zeta) *
          Kakeya.realRpowENN radius zeta * selected.enncard := by gcongr
    _ = Kakeya.realRpowENN (Real.rpow tau (-lambda') * radius) zeta *
          selected.enncard := by rw [hpower_id']

/--
Transfer a Frostman estimate from an ambient set to a selected subset,
multiplying the constant by a cardinality factor `K`.

Given `|ambient| ≤ K * |selected|`, the selected set inherits Frostman control
with constant `C * K`.
-/
lemma DiscreteSet.IsFrostman.subset_with_factor
    {delta : ℝ} {C K : ENNReal}
    {ambient selected : DiscreteSet 2}
    (h : ambient.IsFrostman delta 1 C)
    (hsub : selected ⊆ ambient)
    (hfactor : ambient.enncard ≤ K * selected.enncard) :
    selected.IsFrostman delta 1 (C * K) := by
  intro x r hdelta_r hr_one
  have hball :
      selected.ballCount x r ≤ ambient.ballCount x r := by
    simpa [DiscreteSet.ballCount] using
      Finset.card_le_card
        (Finset.filter_subset_filter _ hsub)
  have hmain : ambient.ballCount x r ≤
      C * Kakeya.realRpowENN r 1 * ambient.enncard :=
    h x r hdelta_r hr_one
  calc
    selected.ballCount x r
      ≤ ambient.ballCount x r := hball
    _ ≤ C * Kakeya.realRpowENN r 1 * ambient.enncard := hmain
    _ ≤ C * Kakeya.realRpowENN r 1 * (K * selected.enncard) := by gcongr
    _ = (C * K) * Kakeya.realRpowENN r 1 * selected.enncard := by
      ring

end Kakeya.Assouad
