import MyLeanRepo.Kakeya.Assouad.WZ1.PackingHelpers

/-!
# Cardinality of the separated family in WZ1 Lemma 17

The selected points lie in one bounded ball and are separated at scale
`rho^(1-epsilon)`.  A coarse three-dimensional packing estimate gives the
very generous polynomial bound `k ≤ 100 rho⁻³` used only to absorb the
harmonic Córdoba denominator.
-/

namespace Kakeya.Assouad

lemma cordoba_separated_cardinality
    {rho epsilon : ℝ}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon < 1)
    {k : ℕ} (p : Fin k → Point3) (center : Point3)
    (hball : ∀ i, dist (p i) center ≤ 1)
    (hsep :
      ∀ i j, i ≠ j →
        Real.rpow rho (1 - epsilon) ≤ dist (p i) (p j)) :
    (k : ℝ) ≤ 100 * Real.rpow rho (-3) := by
  classical
  let E : DiscreteSet 3 := Finset.univ.image p
  let sep : ℝ := Real.rpow rho (1 - epsilon)
  have hsep_pos : 0 < sep := Real.rpow_pos_of_pos hrho _
  have hp_inj : Function.Injective p := by
    intro i j hij
    by_contra hne
    have hpos : 0 < dist (p i) (p j) :=
      hsep_pos.trans_le (hsep i j hne)
    rw [hij, dist_self] at hpos
    linarith
  have hE_card : E.card = k := by
    dsimp only [E]
    simpa using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin k)) hp_inj)
  have hE_sep : E.IsDeltaSeparated sep := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨j, _hj, rfl⟩
    have hij : i ≠ j := by
      intro h
      subst h
      exact hxy rfl
    exact hsep i j hij
  have hE_ball : ∀ x ∈ E, dist x center ≤ 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    exact hball i
  have hpack :
      E.enncard ≤ ENNReal.ofReal ((2 / sep + 1) ^ (3 : ℕ)) := by
    simpa using
      delta_separated_ball_card_bound hsep_pos (show (0 : ℝ) < 1 by norm_num)
        hE_sep center hE_ball
  have hsep_le_one : sep ≤ 1 := by
    exact Real.rpow_le_one hrho.le hrho_one (by linarith)
  have hinv_sep : 1 ≤ 1 / sep := by
    exact (le_div_iff₀ hsep_pos).2 (by simpa using hsep_le_one)
  have hbase :
      2 / sep + 1 ≤ 3 / sep := by
    calc
      2 / sep + 1 ≤ 2 / sep + 1 / sep := by gcongr
      _ = 3 / sep := by ring
  have hcube :
      (2 / sep + 1) ^ (3 : ℕ) ≤ (3 / sep) ^ (3 : ℕ) := by
    gcongr
  have hpack_real :
      (k : ℝ) ≤ (3 / sep) ^ (3 : ℕ) := by
    have hnonneg : 0 ≤ (3 / sep) ^ (3 : ℕ) := by positivity
    have hpack' :
        (E.card : ENNReal) ≤ ENNReal.ofReal ((3 / sep) ^ (3 : ℕ)) :=
      hpack.trans (ENNReal.ofReal_mono hcube)
    rw [hE_card] at hpack'
    have hk : (k : ENNReal) = ENNReal.ofReal (k : ℝ) := by norm_cast
    rw [hk] at hpack'
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hpack'
  have hsep_power :
      sep ^ (3 : ℕ) = Real.rpow rho (3 * (1 - epsilon)) := by
    dsimp only [sep]
    calc
      (Real.rpow rho (1 - epsilon)) ^ (3 : ℕ) =
          Real.rpow (Real.rpow rho (1 - epsilon)) (3 : ℝ) :=
        (Real.rpow_natCast _ 3).symm
      _ = Real.rpow rho ((1 - epsilon) * 3) :=
        (Real.rpow_mul hrho.le (1 - epsilon) 3).symm
      _ = Real.rpow rho (3 * (1 - epsilon)) := by ring_nf
  have hratio :
      (3 / sep) ^ (3 : ℕ) =
        27 * Real.rpow rho (-3 * (1 - epsilon)) := by
    rw [div_pow, hsep_power]
    have hinv :
        (Real.rpow rho (3 * (1 - epsilon)))⁻¹ =
          Real.rpow rho (-3 * (1 - epsilon)) := by
      calc
        (Real.rpow rho (3 * (1 - epsilon)))⁻¹ =
            Real.rpow rho (-(3 * (1 - epsilon))) :=
          (Real.rpow_neg hrho.le _).symm
        _ = Real.rpow rho (-3 * (1 - epsilon)) := by ring_nf
    rw [div_eq_mul_inv, hinv]
    norm_num
  have hexp : -3 ≤ -3 * (1 - epsilon) := by
    nlinarith
  have hpower :
      Real.rpow rho (-3 * (1 - epsilon)) ≤
        Real.rpow rho (-3) :=
    Real.rpow_le_rpow_of_exponent_ge hrho hrho_one hexp
  calc
    (k : ℝ) ≤ (3 / sep) ^ (3 : ℕ) := hpack_real
    _ = 27 * Real.rpow rho (-3 * (1 - epsilon)) := hratio
    _ ≤ 27 * Real.rpow rho (-3) :=
      mul_le_mul_of_nonneg_left hpower (by norm_num)
    _ ≤ 100 * Real.rpow rho (-3) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hrho.le _)

/--
The form used by the Lemma 17 extraction: the points are represented by a
total sequence, with membership and separation hypotheses restricted to the
initial segment of length `k`.
-/
lemma cordoba_separated_cardinality_of_lt
    {rho epsilon : ℝ}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon < 1)
    {k : ℕ} (p : ℕ → Point3) (center : Point3)
    (hball : ∀ m < k, dist (p m) center ≤ 1)
    (hsep :
      ∀ m n, m < k → n < k → m ≠ n →
        Real.rpow rho (1 - epsilon) ≤ dist (p m) (p n)) :
    (k : ℝ) ≤ 100 * Real.rpow rho (-3) := by
  let pFin : Fin k → Point3 := fun i => p i
  apply cordoba_separated_cardinality hrho hrho_one hepsilon hepsilon_one pFin center
  · intro i
    exact hball i i.isLt
  · intro i j hij
    apply hsep i j i.isLt j.isLt
    intro hval
    exact hij (Fin.ext hval)

end Kakeya.Assouad
