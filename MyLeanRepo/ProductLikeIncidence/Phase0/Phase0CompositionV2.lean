module

/-
# Phase 0 Composition V2

Unconditional version: derives h_popular directly from δ-set lower bounds
and adds missing outputs needed by downstream phases.

## Dependencies:
- h_size_bound: Nδ(Pz z) ≤ C·δ^{-s} (provided by trimming step)
- hP_small: Nδ(P) < δ^{-(2s+η)} (contradiction assumption)

## h_popular derivation:
- |X_y| ≥ δ^{-s}/C (from δ-set lower bound)
- |cubesOf(Pz)| ≥ δ^{-s}/C (from δ-set lower bound)
- Bounded overlap ≤ 7
- ⇒ |U_y| ≥ δ^{-2s}/(7C²)
- |T| < δ^{-(2s+η)}
- c = δ^η/(7C²) ⇒ |U_y| ≥ c·|T|
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.ProductLikeIncidence.Phase0.CubeUnion
public import MyLeanRepo.ProductLikeIncidence.Phase0.CubeFamilyAggregation
public import MyLeanRepo.ProductLikeIncidence.Phase0.OverlapBound
public import MyLeanRepo.ProductLikeIncidence.Phase0.RefinementCubes
public import MyLeanRepo.ProductLikeIncidence.Phase0.CardinalityLowerBoundK
public import MyLeanRepo.ProductLikeIncidence.CoveringLowerBound
public import MyLeanRepo.ProductLikeIncidence.FrostmanFromDeltaSet
public import MyLeanRepo.ProductLikeIncidence.Phase0.QuantitativeBox
public import MyLeanRepo.ProductLikeIncidence.Phase0.BoxBridge
public import MyLeanRepo.ProductLikeIncidence.Phase0.BoxComposition
public import MyLeanRepo.CoveringToFinset
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ProductLikeIncidence ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

private lemma mkPoint2_in_incidenceSet_v2 {Y : Set ℝ} {X : ℝ → Set ℝ}
    {x y : ℝ} (hy : y ∈ Y) (hx : x ∈ X y) :
    mkPoint2 x y ∈ productLikeIncidenceSet Y X := by
  simp only [productLikeIncidenceSet, Set.mem_iUnion]
  refine ⟨y, hy, ?_⟩
  simp only [Set.mem_setOf_eq, mkPoint2_fst, mkPoint2_snd]
  exact ⟨hx, trivial⟩

/-- **Phase 0 composition V2**: unconditional popularity derivation + full outputs. -/
lemma phase0_composition_v2
    {δ s τ C η η_small κ0 qBox : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_pos : 0 < s) (hs_le_one : s ≤ 1)
    (hC_ge1 : 1 ≤ C) (hC_pos : 0 < C)
    (_hη_pos : 0 < η)
    (hη_small_pos : 0 < η_small)
    (hC_le : C ≤ δ ^ (-η))
    (_hκ : η_small + 4 * η < 2 * (s - κ0))
    (hδ_pbar : δ ^ (-(2 * s - 2 * κ0 - η_small - 4 * η)) ≥ 98)
    (hτ_pos : 0 < τ)
    (hqBox_pos : 0 < qBox)
    (hδ_box_small : δ ^ (-qBox) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * C * 2 ^ τ) / (δ ^ η_small / (7 * C ^ 2))) ^ (1 / τ) + 6 * δ))
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hY_fin : Y.Finite) (hY_nonempty : Y.Nonempty)
    (_hY_sub : Y ⊆ productLikeUnitGrid δ)
    (_hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    (hy_bounds : ∀ y ∈ Y, 0 ≤ y ∧ y ≤ 1)
    (hPz_delta : ∀ z ∈ productLikeIncidenceSet Y X, IsDeltaSCSet (d := 2) δ s C (Pz z))
    (hPz_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_bounded : ∀ z ∈ productLikeIncidenceSet Y X, Bornology.IsBounded (Pz z))
    -- Upper bound on each Pz covering number (from trimming)
    (h_size_bound : ∀ z ∈ productLikeIncidenceSet Y X,
      ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) ≤ ENNReal.ofReal (C * δ^(-s)))
    -- Contradiction assumption: total P is small
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ (⋃ z ∈ productLikeIncidenceSet Y X, Pz z)) <
      ENNReal.ofReal (δ ^ (-(2 * s + η_small))))
    -- For box output: need c * |Y| > 2 where c = δ^η / (7C^2)
    (h_cY_large : 2 < (δ ^ η_small / (7 * C ^ 2)) * (Y.ncard : ℝ)) :
    let U_y : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2))) := fun y =>
      ⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))
    let T : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ y ∈ Y, U_y y
    let c : ℝ := δ ^ η_small / (7 * C ^ 2)
    ∃ (Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))),
      Tbar ⊆ T ∧
      IsDeltaSCSet (d := 2) δ (2 * s) (4 * (49 * C^4) / c^2) (⋃₀ Tbar) ∧
      ENat.toENNReal Tbar.encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal T.encard ∧
      (∀ Q ∈ Tbar, ENat.toENNReal ({y ∈ Y | Q ∈ U_y y}).encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) ∧
      -- Point multiplicity
      (∀ p ∈ ⋃₀ Tbar,
        ENat.toENNReal ({y ∈ Y | p ∈ ⋃₀ (Tbar ∩ U_y y)}).encard ≥
          ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) ∧
      -- Projection bound (4δ due to cube diameter)
      (∀ y ∈ Y, ∀ p ∈ ⋃₀ (Tbar ∩ U_y y),
        ∃ x ∈ X y, |p 0 * y + p 1 - x| ≤ 4 * δ) ∧
      -- Strong Pbar size lower bound
      ENNReal.ofReal (δ ^ (-2 * s + η_small) / (98 * C ^ 4)) ≤ ENat.toENNReal Tbar.encard ∧
      -- Pbar size lower bound (weaker corollary)
      ENNReal.ofReal (δ ^ (-2 * κ0)) ≤ ENat.toENNReal Tbar.encard ∧
      -- Uniform power-of-two box containing Pbar
      (∃ (Rpow : ℝ), (∃ (k : ℕ), Rpow = (2 : ℝ) ^ k) ∧
        (∀ p ∈ ⋃₀ Tbar, |p 0| ≤ Rpow ∧ |p 1| ≤ Rpow) ∧
        4 * Rpow ≤ δ ^ (-qBox)) := by
  let U_y : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2))) := fun y =>
    ⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))
  let T : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ y ∈ Y, U_y y
  let c : ℝ := δ ^ η_small / (7 * C ^ 2)

  have hc_pos : 0 < c := by positivity

  -- Finiteness
  have hX_finite : ∀ y ∈ Y, (X y).Finite := by
    intro y hy
    have h1 : X y ⊆ productLikeUnitGrid δ := (hXy_delta y hy).1
    have h2 : (productLikeUnitGrid δ).Finite := productLikeUnitGrid_finite hδ_pos
    exact Set.Finite.subset h2 h1
  have hCz_finite : ∀ y ∈ Y, ∀ x ∈ X y, (dyadicCubesMeeting δ (Pz (mkPoint2 x y))).Finite := by
    intro y hy x hx
    let z := mkPoint2 x y
    have hz : z ∈ productLikeIncidenceSet Y X := mkPoint2_in_incidenceSet_v2 hy hx
    have h_bdd : Bornology.IsBounded (Pz z) := hPz_bounded z hz
    exact dyadicCubesMeeting_finite hδ_pos h_bdd

  -- Helper: bounded overlap for a fixed y and cube Q
  let overlap_7 : ∀ (y : ℝ), y ∈ Y → ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))) →
      ({x ∈ X y | Q ∈ dyadicCubesMeeting δ (Pz (mkPoint2 x y))}.Finite ∧
       {x ∈ X y | Q ∈ dyadicCubesMeeting δ (Pz (mkPoint2 x y))}.encard ≤ 7) := by
    intro y hy Q hQ
    rcases Set.mem_iUnion₂.mp hQ with ⟨x, hx, hQx⟩
    have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hQx.1
    let S : Set ℝ := {x ∈ X y | Q ∈ dyadicCubesMeeting δ (Pz (mkPoint2 x y))}
    have hS_sub1 : S ⊆ productLikeIntegerGrid δ := by
      intro x hx
      have h_in_unit : x ∈ productLikeUnitGrid δ := (hXy_delta y hy).1 hx.1
      exact h_in_unit.1
    rcases hQ_dyadic with ⟨k, hQ_eq⟩
    let a : ℝ := δ * (k 0 : ℝ)
    let b : ℝ := δ * (k 1 : ℝ)
    have h_p_bounds : ∀ p ∈ Q,
        a ≤ p 0 ∧ p 0 < a + δ ∧ b ≤ p 1 ∧ p 1 < b + δ := by
      intro p hp
      have h_eq1 : a + δ = δ * ((k 0 : ℝ) + 1) := by dsimp only [a]; ring
      have h_eq2 : b + δ = δ * ((k 1 : ℝ) + 1) := by dsimp only [b]; ring
      have h : p ∈ dyadicCube δ k := by rw [hQ_eq] at hp; exact hp
      exact ⟨(h 0).1, by rw [h_eq1]; exact (h 0).2, (h 1).1, by rw [h_eq2]; exact (h 1).2⟩
    let raw_lo : ℝ := a * y + b
    let raw_hi : ℝ := (a + δ) * y + (b + δ)
    let lo : ℝ := raw_lo - 2 * δ
    let hi : ℝ := raw_hi + 2 * δ
    have h_len : hi - lo ≤ 6 * δ := by
      dsimp only [lo, hi, raw_lo, raw_hi]
      nlinarith [(hy_bounds y hy).2]
    have hS_sub2 : S ⊆ Set.Icc lo hi := by
      intro x hx
      have hQ_in : Q ∈ dyadicCubesMeeting δ (Pz (mkPoint2 x y)) := hx.2
      have hQ_meet : (Q ∩ Pz (mkPoint2 x y)).Nonempty := hQ_in.2
      rcases hQ_meet with ⟨p, hpQ, hpPz⟩
      let z := mkPoint2 x y
      have hz : z ∈ productLikeIncidenceSet Y X := mkPoint2_in_incidenceSet_v2 hy hx.1
      have h_ineq : |p 0 * y + p 1 - x| ≤ 2 * δ := hPz_approx z hz p hpPz
      have hpb := h_p_bounds p hpQ
      have h5 : raw_lo ≤ p 0 * y + p 1 := by
        dsimp only [raw_lo]; nlinarith [(hy_bounds y hy).1, hpb.1, hpb.2.2.1]
      have h6 : p 0 * y + p 1 ≤ raw_hi := by
        dsimp only [raw_hi]; nlinarith [(hy_bounds y hy).1, (hy_bounds y hy).2, hpb.2.1, hpb.2.2.2]
      have h7 : |x - (p 0 * y + p 1)| ≤ 2 * δ := by
        have h : x - (p 0 * y + p 1) = -(p 0 * y + p 1 - x) := by ring
        rw [h, abs_neg]; exact h_ineq
      have h8 : p 0 * y + p 1 - 2 * δ ≤ x := by linarith [abs_le.mp h7]
      have h9 : x ≤ p 0 * y + p 1 + 2 * δ := by linarith [abs_le.mp h7]
      have h10 : lo ≤ x := by dsimp only [lo]; linarith
      have h11 : x ≤ hi := by dsimp only [hi]; linarith
      exact ⟨h10, h11⟩
    exact grid_points_in_six_delta_interval hδ_pos hS_sub1 hS_sub2 h_len

  -- Per-y regularity
  have h_per_y_regular : ∀ y ∈ Y,
      IsDeltaSCSet (d := 2) δ (2 * s) (49 * C^4) (⋃₀ (U_y y)) := by
    intro y hy
    let X_y := X y
    let Cz : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2))) := fun x =>
      dyadicCubesMeeting δ (Pz (mkPoint2 x y))
    have hX_grid : X_y ⊆ productLikeIntegerGrid δ := by
      intro x hx
      have h_in_unit : x ∈ productLikeUnitGrid δ := (hXy_delta y hy).1 hx
      exact h_in_unit.1
    have hX_set : IsProductLikeRealDeltaSCSet δ s C X_y := (hXy_delta y hy).2
    have hCz_sub : ∀ x ∈ X_y, Cz x ⊆ dyadicCubes 2 δ := by
      intro x _ Q hQ; exact hQ.1
    have hP_x_delta : ∀ x ∈ X_y, IsDeltaSCSet (d := 2) δ s C (⋃₀ (Cz x)) := by
      intro x hx
      let z := mkPoint2 x y
      have hz : z ∈ productLikeIncidenceSet Y X := mkPoint2_in_incidenceSet_v2 hy hx
      have h1 : ⋃₀ (Cz x) = cubeUnion δ (Pz z) := by rfl
      rw [h1]
      exact cube_union_preserves_delta_set hδ_pos hδ_dyadic (hPz_delta z hz)
    have h_approx : ∀ x ∈ X_y, ∀ Q ∈ Cz x,
        ∃ p ∈ Q, |x - (p 0 * y + p 1)| ≤ 2 * δ := by
      intro x hx Q hQ
      let z := mkPoint2 x y
      have hz : z ∈ productLikeIncidenceSet Y X := mkPoint2_in_incidenceSet_v2 hy hx
      have hQ_meet : (Q ∩ Pz z).Nonempty := hQ.2
      rcases hQ_meet with ⟨p, hpQ, hpPz⟩
      have h_ineq : |p 0 * y + p 1 - x| ≤ 2 * δ := hPz_approx z hz p hpPz
      have h_final : |x - (p 0 * y + p 1)| ≤ 2 * δ := by
        have h : x - (p 0 * y + p 1) = -(p 0 * y + p 1 - x) := by ring
        rw [h, abs_neg]; exact h_ineq
      exact ⟨p, hpQ, h_final⟩
    have h_bounded_overlap := overlap_7 y hy
    have h_card : ∀ x ∈ X_y,
        ENat.toENNReal (Cz x).encard ≤ ENNReal.ofReal (C * δ^(-s)) := by
      intro x hx
      let z := mkPoint2 x y
      have hz : z ∈ productLikeIncidenceSet Y X := mkPoint2_in_incidenceSet_v2 hy hx
      have h1 : (Cz x).encard = dyadicCoveringNumber δ (Pz z) := by
        dsimp only [Cz, z, dyadicCoveringNumber]
      rw [h1]
      exact h_size_bound z hz
    have h_main := cube_family_T_y_is_delta_2s_set
      hδ_pos hδ_dyadic (le_of_lt hs_pos) hs_le_one hC_pos (by norm_num)
      (hy_bounds y hy).1 (hy_bounds y hy).2
      hX_grid hX_set hCz_sub hP_x_delta h_approx h_bounded_overlap h_card
    have h_const : (7 * (7 : ℝ) * C^4) = 49 * C^4 := by ring
    simpa [h_const, U_y] using h_main

  -- Per-y cardinality lower bound using cardinality_lower_bound_K_finite
  have h_per_y_lower : ∀ y ∈ Y,
      ENNReal.ofReal (δ ^ (-2 * s) / (7 * C ^ 2)) ≤
        ENat.toENNReal (U_y y).encard := by
    intro y hy
    let X_y := X y
    let Cz : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2))) := fun x =>
      dyadicCubesMeeting δ (Pz (mkPoint2 x y))
    let cell : Set (EuclideanSpace ℝ (Fin 2)) → Set (EuclideanSpace ℝ (Fin 2)) := id
    have hX_regular : IsDeltaSCSet δ s C (productLikeRealLineCopy X_y) :=
      (hXy_delta y hy).2
    have hX_finite' : X_y.Finite := hX_finite y hy
    have hCz_finite' : ∀ x ∈ X_y, (Cz x).Finite := hCz_finite y hy
    have hcell : ∀ x ∈ X_y, ∀ Q ∈ Cz x, cell Q ∈ dyadicCubes 2 δ := by
      intro x _ Q hQ; exact hQ.1
    have hcell_inj : Set.InjOn cell (⋃ x ∈ X_y, Cz x) := by
      intro a _ b _ h; exact h
    have hTx_regular : ∀ x ∈ X_y,
        IsDeltaSCSet δ s C (cellRealization cell (Cz x)) := by
      intro x hx
      let z := mkPoint2 x y
      have hz : z ∈ productLikeIncidenceSet Y X := mkPoint2_in_incidenceSet_v2 hy hx
      have h1 : cellRealization cell (Cz x) = ⋃₀ (Cz x) := by
        ext p; simp [cellRealization, cell]
      rw [h1]
      exact cube_union_preserves_delta_set hδ_pos hδ_dyadic (hPz_delta z hz)
    have hoverlap := overlap_7 y hy
    exact cardinality_lower_bound_K_finite (y := y)
      hδ_pos hδ_dyadic hs_pos hC_ge1 (by norm_num)
      hX_regular hX_finite' hCz_finite' hcell hcell_inj hTx_regular hoverlap

  -- Upper bound on |T|
  have hT_upper : ENat.toENNReal T.encard < ENNReal.ofReal (δ ^ (-(2 * s + η_small))) := by
    have h_sub : T ⊆ dyadicCubesMeeting δ (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) := by
      intro Q hQ
      rcases Set.mem_iUnion₂.mp hQ with ⟨y, hy, hQy⟩
      rcases Set.mem_iUnion₂.mp hQy with ⟨x, hx, hQx⟩
      have hQ1 : Q ∈ dyadicCubes 2 δ := hQx.1
      have hQ2 : (Q ∩ Pz (mkPoint2 x y)).Nonempty := hQx.2
      have hz : mkPoint2 x y ∈ productLikeIncidenceSet Y X := mkPoint2_in_incidenceSet_v2 hy hx
      have h3 : (Q ∩ (⋃ z' ∈ productLikeIncidenceSet Y X, Pz z')).Nonempty := by
        rcases hQ2 with ⟨p, hpQ, hpPz⟩
        have hp_in_union : p ∈ ⋃ z' ∈ productLikeIncidenceSet Y X, Pz z' := by
          exact Set.mem_iUnion₂.mpr ⟨mkPoint2 x y, hz, hpPz⟩
        exact ⟨p, hpQ, hp_in_union⟩
      exact ⟨hQ1, h3⟩
    have h1 : ENat.toENNReal T.encard ≤
        ENat.toENNReal (dyadicCoveringNumber δ (⋃ z ∈ productLikeIncidenceSet Y X, Pz z)) := by
      have h2 : T ⊆ dyadicCubesMeeting δ (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) := h_sub
      have h3 : ENat.toENNReal T.encard ≤ ENat.toENNReal (dyadicCubesMeeting δ (⋃ z ∈ productLikeIncidenceSet Y X, Pz z)).encard := by
        exact_mod_cast Set.encard_mono h2
      simpa [dyadicCoveringNumber] using h3
    exact lt_of_le_of_lt h1 hP_small

  -- Derive h_popular
  have h_popular : ∀ y ∈ Y,
      ENat.toENNReal (U_y y).encard ≥ ENNReal.ofReal c * ENat.toENNReal T.encard := by
    intro y hy
    have h_lower : ENNReal.ofReal (δ ^ (-2 * s) / (7 * C ^ 2)) ≤
        ENat.toENNReal (U_y y).encard := h_per_y_lower y hy
    have h_c_def : c = δ ^ η_small / (7 * C ^ 2) := by rfl
    have h_eq : c * δ ^ (-(2 * s + η_small)) = δ ^ (-2 * s) / (7 * C ^ 2) := by
      dsimp only [c]
      have h_exp : δ ^ η_small * δ ^ (-(2 * s + η_small)) = δ ^ (-2 * s) := by
        have h_sum : η_small + (-(2 * s + η_small)) = -2 * s := by ring
        have h : δ ^ η_small * δ ^ (-(2 * s + η_small)) = δ ^ (η_small + (-(2 * s + η_small))) := by
          rw [← Real.rpow_add (by linarith)]
        rw [h, h_sum]
      field_simp
      <;> rw [h_exp]
      <;> ring_nf
    have h_pos1 : 0 ≤ c := by positivity
    have h_mul_upper : ENNReal.ofReal c * ENat.toENNReal T.encard <
        ENNReal.ofReal (δ ^ (-2 * s) / (7 * C ^ 2)) := by
      have h3 : ENNReal.ofReal c * ENat.toENNReal T.encard <
          ENNReal.ofReal c * ENNReal.ofReal (δ ^ (-(2 * s + η_small))) := by
        have hc_pos' : ENNReal.ofReal c ≠ 0 := by positivity
        have hc_ne_top : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
        exact ENNReal.mul_lt_mul_right hc_pos' hc_ne_top hT_upper
      have h4 : ENNReal.ofReal c * ENNReal.ofReal (δ ^ (-(2 * s + η_small))) =
          ENNReal.ofReal (c * δ ^ (-(2 * s + η_small))) := by
        rw [← ENNReal.ofReal_mul h_pos1]
      have h5 : ENNReal.ofReal (c * δ ^ (-(2 * s + η_small))) =
          ENNReal.ofReal (δ ^ (-2 * s) / (7 * C ^ 2)) := by
        rw [h_eq]
      rw [h4, h5] at h3
      exact h3
    exact le_trans (le_of_lt h_mul_upper) h_lower

  -- Apply global refinement
  have hT_y_set : ∀ y ∈ Y, IsDeltaSCSet (d := 2) δ (2 * s) (49 * C^4) (⋃₀ (U_y y)) :=
    h_per_y_regular
  have hT_y_sub : ∀ y ∈ Y, U_y y ⊆ T := by
    intro y hy Q hQ
    exact Set.mem_iUnion₂.mpr ⟨y, hy, hQ⟩
  have hT_cubes : T ⊆ dyadicCubes 2 δ := by
    intro Q hQ
    rcases Set.mem_iUnion₂.mp hQ with ⟨y, _, hQy⟩
    rcases Set.mem_iUnion₂.mp hQy with ⟨x, _, hQx⟩
    exact hQx.1

  rcases phase0_refinement_cubes hδ_pos hδ_dyadic (le_of_lt hs_pos) (by linarith)
    (by positivity) hc_pos hY_fin hY_nonempty hT_y_set hT_y_sub hT_cubes h_popular with
    ⟨Tbar, hTbar_sub, hTbar_regular, hTbar_size, hTbar_mult⟩

  -- Point multiplicity
  have h_point_mult : ∀ p ∈ ⋃₀ Tbar,
      ENat.toENNReal ({y ∈ Y | p ∈ ⋃₀ (Tbar ∩ U_y y)}).encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard := by
    intro p hp
    rcases Set.mem_sUnion.mp hp with ⟨Q, hQ_Tbar, hpQ⟩
    have hQ_mult : ENat.toENNReal ({y ∈ Y | Q ∈ U_y y}).encard ≥
        ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard := hTbar_mult Q hQ_Tbar
    have h_set_eq : {y ∈ Y | p ∈ ⋃₀ (Tbar ∩ U_y y)} = {y ∈ Y | Q ∈ U_y y} := by
      ext y
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        rcases Set.mem_sUnion.mp h.2 with ⟨Q', hQ'_in, hpQ'⟩
        have hQ'_in_Tbar : Q' ∈ Tbar := hQ'_in.1
        have hQ'_Uy : Q' ∈ U_y y := hQ'_in.2
        by_cases hy' : y ∈ Y
        · have hQ'_cube : Q' ∈ dyadicCubes 2 δ := hT_cubes (hT_y_sub y hy' hQ'_Uy)
          have hQ_cube : Q ∈ dyadicCubes 2 δ := hT_cubes (hTbar_sub hQ_Tbar)
          rcases hQ'_cube with ⟨k', hQ'_eq⟩
          rcases hQ_cube with ⟨k, hQ_eq⟩
          have h_inter : (Q' ∩ Q).Nonempty := ⟨p, hpQ', hpQ⟩
          have h_k_eq : k' = k := by
            by_contra h
            have h_disj : Disjoint Q' Q := by
              rw [hQ'_eq, hQ_eq]
              exact robust_projection.dyadic_cubes_disjoint hδ_pos h
            have h_empty : Q' ∩ Q = ∅ := by
              simpa [Set.disjoint_iff_inter_eq_empty] using h_disj
            rw [h_empty] at h_inter
            exact Set.not_nonempty_empty h_inter
          have hQ'_eq_Q : Q' = Q := by
            rw [hQ'_eq, hQ_eq, h_k_eq]
          rw [hQ'_eq_Q] at hQ'_Uy
          exact ⟨hy', hQ'_Uy⟩
        · exact False.elim (hy' (by tauto))
      · intro h
        have hQ_in' : Q ∈ Tbar ∩ U_y y := ⟨hQ_Tbar, h.2⟩
        exact ⟨h.1, Set.mem_sUnion.mpr ⟨Q, hQ_in', hpQ⟩⟩
    rw [h_set_eq]
    exact hQ_mult

  -- Projection bound (4δ)
  have h_proj_bound : ∀ y ∈ Y, ∀ p ∈ ⋃₀ (Tbar ∩ U_y y),
      ∃ x ∈ X y, |p 0 * y + p 1 - x| ≤ 4 * δ := by
    intro y hy p hp
    rcases Set.mem_sUnion.mp hp with ⟨Q, hQ_in, hpQ⟩
    have hQ_Uy : Q ∈ U_y y := hQ_in.2
    rcases Set.mem_iUnion₂.mp hQ_Uy with ⟨x, hx, hQx⟩
    have hQ_meet : (Q ∩ Pz (mkPoint2 x y)).Nonempty := hQx.2
    rcases hQ_meet with ⟨q, hqQ, hqPz⟩
    let z := mkPoint2 x y
    have hz : z ∈ productLikeIncidenceSet Y X := mkPoint2_in_incidenceSet_v2 hy hx
    have h_ineq : |q 0 * y + q 1 - x| ≤ 2 * δ := hPz_approx z hz q hqPz
    rcases hQx.1 with ⟨k, hQ_eq⟩
    have h_p0 : δ * (k 0 : ℝ) ≤ p 0 := by rw [hQ_eq] at hpQ; exact (hpQ 0).1
    have h_p1 : p 0 < δ * ((k 0 : ℝ) + 1) := by rw [hQ_eq] at hpQ; exact (hpQ 0).2
    have h_p2 : δ * (k 1 : ℝ) ≤ p 1 := by rw [hQ_eq] at hpQ; exact (hpQ 1).1
    have h_p3 : p 1 < δ * ((k 1 : ℝ) + 1) := by rw [hQ_eq] at hpQ; exact (hpQ 1).2
    have h_q0 : δ * (k 0 : ℝ) ≤ q 0 := by rw [hQ_eq] at hqQ; exact (hqQ 0).1
    have h_q1 : q 0 < δ * ((k 0 : ℝ) + 1) := by rw [hQ_eq] at hqQ; exact (hqQ 0).2
    have h_q2 : δ * (k 1 : ℝ) ≤ q 1 := by rw [hQ_eq] at hqQ; exact (hqQ 1).1
    have h_q3 : q 1 < δ * ((k 1 : ℝ) + 1) := by rw [hQ_eq] at hqQ; exact (hqQ 1).2
    have h_diff1 : |p 0 - q 0| < δ := by
      have h1 : p 0 - q 0 > -δ := by linarith
      have h2 : p 0 - q 0 < δ := by linarith
      rw [abs_lt]; exact ⟨h1, h2⟩
    have h_diff2 : |p 1 - q 1| < δ := by
      have h1 : p 1 - q 1 > -δ := by linarith
      have h2 : p 1 - q 1 < δ := by linarith
      rw [abs_lt]; exact ⟨h1, h2⟩
    have h_y_abs : |y| ≤ 1 := by
      have h0 : 0 ≤ y := (hy_bounds y hy).1
      have h1 : y ≤ 1 := (hy_bounds y hy).2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h_main_ineq : |p 0 * y + p 1 - x| ≤ 4 * δ := by
      have h_abs1 : |(p 0 - q 0) * y + (p 1 - q 1)| ≤ |(p 0 - q 0) * y| + |p 1 - q 1| := by exact abs_add_le ((p.ofLp 0 - q.ofLp 0) * y) (p.ofLp 1 - q.ofLp 1)
      have h1 : |(p 0 - q 0) * y + (p 1 - q 1)| ≤ |p 0 - q 0| * |y| + |p 1 - q 1| := by
        calc
          |(p 0 - q 0) * y + (p 1 - q 1)|
            ≤ |(p 0 - q 0) * y| + |p 1 - q 1| := h_abs1
          _ = |p 0 - q 0| * |y| + |p 1 - q 1| := by rw [abs_mul]
      have h2 : |p 0 - q 0| * |y| ≤ δ := by
        have h3 : |p 0 - q 0| < δ := h_diff1
        have h4 : |y| ≤ 1 := h_y_abs
        have h5 : |p 0 - q 0| * |y| ≤ |p 0 - q 0| := by
          calc
            |p 0 - q 0| * |y| ≤ |p 0 - q 0| * 1 := by gcongr
            _ = |p 0 - q 0| := by ring
        exact le_trans h5 (le_of_lt h3)
      have h3 : |p 1 - q 1| < δ := h_diff2
      have h_abs2 : |(p 0 - q 0) * y + (p 1 - q 1) + (q 0 * y + q 1 - x)| ≤
          |(p 0 - q 0) * y + (p 1 - q 1)| + |q 0 * y + q 1 - x| := by exact abs_add_le ((p.ofLp 0 - q.ofLp 0) * y + (p.ofLp 1 - q.ofLp 1)) (q.ofLp 0 * y + q.ofLp 1 - x)
      have h6 : |(p 0 - q 0) * y + (p 1 - q 1)| + |q 0 * y + q 1 - x| ≤
          (|p 0 - q 0| * |y| + |p 1 - q 1|) + |q 0 * y + q 1 - x| := by
        gcongr
      calc
        |p 0 * y + p 1 - x|
          = |(p 0 - q 0) * y + (p 1 - q 1) + (q 0 * y + q 1 - x)| := by ring_nf
        _ ≤ |(p 0 - q 0) * y + (p 1 - q 1)| + |q 0 * y + q 1 - x| := h_abs2
        _ ≤ (|p 0 - q 0| * |y| + |p 1 - q 1|) + |q 0 * y + q 1 - x| := h6
        _ ≤ δ + δ + 2 * δ := by linarith
        _ = 4 * δ := by ring
    exact ⟨x, hx, h_main_ineq⟩

  -- Pbar size bound: |Tbar| ≥ δ^{-2κ0}
  rcases hY_nonempty with ⟨y0, hy0⟩
  have hT_lower : ENNReal.ofReal (δ ^ (-2 * s) / (7 * C ^ 2)) ≤
      ENat.toENNReal T.encard := by
    have hUy_sub : U_y y0 ⊆ T := hT_y_sub y0 hy0
    have h1a : (U_y y0).encard ≤ T.encard := Set.encard_mono hUy_sub
    have h1 : ENat.toENNReal (U_y y0).encard ≤ ENat.toENNReal T.encard :=
      ENat.toENNReal_mono h1a
    have h2 : ENNReal.ofReal (δ ^ (-2 * s) / (7 * C ^ 2)) ≤
        ENat.toENNReal (U_y y0).encard := h_per_y_lower y0 hy0
    exact le_trans h2 h1
  have h_const1 : (c / 2) * (δ ^ (-2 * s) / (7 * C ^ 2)) =
      δ ^ (-2 * s + η_small) / (98 * C ^ 4) := by
    dsimp only [c]
    have h9 : δ ^ η_small * δ ^ (-2 * s) = δ ^ (-2 * s + η_small) := by
      rw [← Real.rpow_add (by linarith)] <;> ring_nf
    have h10 : (δ ^ η_small / (7 * C ^ 2) / 2) * (δ ^ (-2 * s) / (7 * C ^ 2)) =
        (δ ^ η_small * δ ^ (-2 * s)) / (98 * C ^ 4) := by ring
    rw [h10, h9]
  have hTbar_lower : ENNReal.ofReal (δ ^ (-2 * s + η_small) / (98 * C ^ 4)) ≤
      ENat.toENNReal Tbar.encard := by
    have h3 : ENNReal.ofReal (c / 2) * ENat.toENNReal T.encard ≤
        ENat.toENNReal Tbar.encard := hTbar_size
    have h4 : ENNReal.ofReal (c / 2) * ENNReal.ofReal (δ ^ (-2 * s) / (7 * C ^ 2)) ≤
        ENNReal.ofReal (c / 2) * ENat.toENNReal T.encard := by
      gcongr
    have h5 : ENNReal.ofReal (c / 2) * ENNReal.ofReal (δ ^ (-2 * s) / (7 * C ^ 2)) =
        ENNReal.ofReal ((c / 2) * (δ ^ (-2 * s) / (7 * C ^ 2))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h5, h_const1] at h4
    exact le_trans h4 h3
  -- Strong Pbar size bound is hTbar_lower above

  -- Derive weak bound: |Tbar| ≥ δ^{-2κ0} from strong bound + hC_le + hδ_pbar
  have hC4_le : C ^ 4 ≤ δ ^ (-4 * η) := by
    have h1 : C ≤ δ ^ (-η) := hC_le
    have h2 : C ^ 4 ≤ (δ ^ (-η)) ^ 4 := by gcongr
    have h3 : (δ ^ (-η)) ^ 4 = δ ^ (-4 * η) := by
      have h31 : (δ ^ (-η)) ^ 4 = (δ ^ (-η)) ^ (4 : ℝ) := by norm_cast
      have h32 : (δ ^ (-η)) ^ (4 : ℝ) = δ ^ ((-η) * 4) :=
        (Real.rpow_mul hδ_pos.le (-η) 4).symm
      have h33 : (-η) * 4 = -4 * η := by ring
      rw [h31, h32, h33]
    rw [h3] at h2
    exact h2
  have h_strong2 : δ ^ (-2 * s + η_small) / (98 * C ^ 4) ≥ δ ^ (-2 * s + η_small + 4 * η) / 98 := by
    have h4 : 1 / (98 * C ^ 4) ≥ 1 / (98 * δ ^ (-4 * η)) := by gcongr
    have h5 : δ ^ (-2 * s + η_small) / (98 * C ^ 4) ≥ δ ^ (-2 * s + η_small) / (98 * δ ^ (-4 * η)) := by gcongr
    have h6 : δ ^ (-2 * s + η_small) / (98 * δ ^ (-4 * η)) = δ ^ (-2 * s + η_small + 4 * η) / 98 := by
      have h7 : δ ^ (-2 * s + η_small) / (98 * δ ^ (-4 * η)) =
          (δ ^ (-2 * s + η_small) / δ ^ (-4 * η)) / 98 := by ring
      rw [h7]
      have h8 : δ ^ (-2 * s + η_small) / δ ^ (-4 * η) = δ ^ ((-2 * s + η_small) - (-4 * η)) := by
        rw [Real.rpow_sub (by linarith)]
      rw [h8]
      have h9 : (-2 * s + η_small) - (-4 * η) = -2 * s + η_small + 4 * η := by ring
      rw [h9]
    rw [h6] at h5
    exact h5
  have h_exp3 : δ ^ (-2 * s + η_small + 4 * η) / 98 ≥ δ ^ (-2 * κ0) := by
    have h9 : δ ^ (-(2 * s - 2 * κ0 - η_small - 4 * η)) ≥ 98 := hδ_pbar
    have h10 : 98 ≤ δ ^ (-2 * s + 2 * κ0 + η_small + 4 * η) := by
      have h11 : -(2 * s - 2 * κ0 - η_small - 4 * η) = -2 * s + 2 * κ0 + η_small + 4 * η := by ring
      rw [h11] at h9
      exact h9
    have h12 : δ ^ (-2 * s + η_small + 4 * η) ≥ 98 * δ ^ (-2 * κ0) := by
      have h13 : δ ^ (-2 * s + η_small + 4 * η) = δ ^ (-2 * κ0) * δ ^ (-2 * s + 2 * κ0 + η_small + 4 * η) := by
        rw [← Real.rpow_add (by linarith)] <;> ring_nf
      rw [h13]
      have h14 : 0 ≤ δ ^ (-2 * κ0) := by positivity
      have h15 : δ ^ (-2 * κ0) * 98 ≤ δ ^ (-2 * κ0) * δ ^ (-2 * s + 2 * κ0 + η_small + 4 * η) :=
        mul_le_mul_of_nonneg_left h10 h14
      have h16 : δ ^ (-2 * κ0) * δ ^ (-2 * s + 2 * κ0 + η_small + 4 * η) ≥ 98 * δ ^ (-2 * κ0) := by
        linarith [mul_comm (δ ^ (-2 * κ0)) 98]
      exact h16
    have h14 : 0 < 98 := by norm_num
    calc
      δ ^ (-2 * s + η_small + 4 * η) / 98 ≥ (98 * δ ^ (-2 * κ0)) / 98 := by gcongr
      _ = δ ^ (-2 * κ0) := by field_simp [h14.ne']
  have h_exp4 : δ ^ (-2 * s + η_small) / (98 * C ^ 4) ≥ δ ^ (-2 * κ0) :=
    le_trans h_exp3 h_strong2
  have h_pbar_size : ENNReal.ofReal (δ ^ (-2 * κ0)) ≤ ENat.toENNReal Tbar.encard := by
    have h10 : ENNReal.ofReal (δ ^ (-2 * κ0)) ≤
        ENNReal.ofReal (δ ^ (-2 * s + η_small) / (98 * C ^ 4)) :=
      ENNReal.ofReal_le_ofReal h_exp4
    exact le_trans h10 hTbar_lower

  -- Box output: uniform power-of-two box containing Pbar
  -- Uses phase0_box_composition (verified production lemma)
  have hδ_le_one : δ ≤ 1 := by
    rcases hδ_dyadic with ⟨n, hn⟩
    rw [hn]
    have h1 : (2 : ℝ) ^ (-(n : ℤ)) = 1 / (2 : ℝ) ^ n := by
      rw [zpow_neg, one_div]
      <;> norm_cast
    rw [h1]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      have h3 : ∀ m : ℕ, 1 ≤ (2 : ℝ) ^ m := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih => simp [pow_succ] at * <;> nlinarith
      exact h3 n
    exact (div_le_one (by positivity)).mpr h2
  have hTbar_dyadic : ∀ Q ∈ Tbar, Q ∈ dyadicCubes 2 δ := by
    intro Q hQ
    exact hT_cubes (hTbar_sub hQ)
  have hXy_sub' : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ := by
    intro y hy
    exact (hXy_delta y hy).1
  obtain ⟨Rpow, ⟨k, hk_eq⟩, hPbar_box, hRpow_lt⟩ :=
    phase0_box_composition
      (hδ_pos := hδ_pos)
      (hδ_dyadic := hδ_dyadic)
      (hδ_le_one := hδ_le_one)
      (hτ_pos := hτ_pos)
      (hC_pos := hC_pos)
      (hc_pos := hc_pos)
      (hY_grid := _hY_sub)
      (hY_delta := _hY_delta)
      (hXy_sub := hXy_sub')
      (h_mult := hTbar_mult)
      (hTbar_dyadic := hTbar_dyadic)
      (h_incidence := h_proj_bound)
      (h_large_Y := h_cY_large)
  let R_expr := 1 + (1 + 12 * δ) / (((c / 2) / (3 * C * 2 ^ τ)) ^ (1 / τ)) + 6 * δ
  have hR_ge_one : 1 ≤ R_expr := by
    dsimp only [R_expr]
    have h_pos1 : 0 ≤ (1 + 12 * δ) / (((c / 2) / (3 * C * 2 ^ τ)) ^ (1 / τ)) := by positivity
    have h_pos2 : 0 ≤ 6 * δ := by positivity
    linarith
  have h_max : max 1 R_expr = R_expr := by
    rw [max_eq_right hR_ge_one]
  have h_alg : (1 + 12 * δ) / (((c / 2) / (3 * C * 2 ^ τ)) ^ (1 / τ)) =
      (1 + 12 * δ) * ((6 * C * 2 ^ τ) / (δ ^ η_small / (7 * C ^ 2))) ^ (1 / τ) := by
    have h1 : (c / 2) / (3 * C * 2 ^ τ) = c / (6 * C * 2 ^ τ) := by ring
    have hc : c = δ ^ η_small / (7 * C ^ 2) := by dsimp only [c]
    have h_pos : 0 < c / (6 * C * 2 ^ τ) := by positivity
    have h_inv : 1 / ((c / (6 * C * 2 ^ τ)) ^ (1 / τ)) = ((6 * C * 2 ^ τ) / c) ^ (1 / τ) := by
      have h_pos : 0 < c / (6 * C * 2 ^ τ) := by positivity
      have h4 : (c / (6 * C * 2 ^ τ))⁻¹ = (6 * C * 2 ^ τ) / c := by
        field_simp [h_pos.ne']
      have h5 : 1 / ((c / (6 * C * 2 ^ τ)) ^ (1 / τ)) = ((c / (6 * C * 2 ^ τ)) ^ (1 / τ))⁻¹ := by
        exact one_div _
      have h6 : ((c / (6 * C * 2 ^ τ)) ^ (1 / τ))⁻¹ = ((c / (6 * C * 2 ^ τ))⁻¹) ^ (1 / τ) := by
        rw [Real.inv_rpow (by positivity) (1 / τ)]
      rw [h5, h6, h4]
    have h_div : (1 + 12 * δ) / ((c / (6 * C * 2 ^ τ)) ^ (1 / τ)) =
        (1 + 12 * δ) * (1 / ((c / (6 * C * 2 ^ τ)) ^ (1 / τ))) := by ring
    rw [h1, h_div, h_inv, hc]
  have hR_expr_eq : R_expr = 1 + (1 + 12 * δ) * ((6 * C * 2 ^ τ) / (δ ^ η_small / (7 * C ^ 2))) ^ (1 / τ) + 6 * δ := by
    dsimp only [R_expr]
    rw [h_alg]
  have h4Rpow_le : 4 * Rpow ≤ δ ^ (-qBox) := by
    rw [h_max] at hRpow_lt
    have h_final : 8 * R_expr ≤ δ ^ (-qBox) := by
      rw [hR_expr_eq]
      exact hδ_box_small
    have h_strict : 4 * Rpow < 8 * R_expr := by linarith
    exact le_of_lt (lt_of_lt_of_le h_strict h_final)
  have h_box : ∃ (Rpow : ℝ), (∃ (k : ℕ), Rpow = (2 : ℝ) ^ k) ∧
      (∀ p ∈ ⋃₀ Tbar, |p 0| ≤ Rpow ∧ |p 1| ≤ Rpow) ∧ 4 * Rpow ≤ δ ^ (-qBox) :=
    ⟨Rpow, ⟨k, hk_eq⟩, hPbar_box, h4Rpow_le⟩

  exact ⟨Tbar, hTbar_sub, hTbar_regular, hTbar_size, hTbar_mult, h_point_mult, h_proj_bound, hTbar_lower, h_pbar_size, h_box⟩

end ProductLikeIncidence.ProductReduction
