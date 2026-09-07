import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalTransfer
import Mathlib.Tactic

/-!
# Intersection mass retention for the every-scale local AD iteration

This module provides the pointwise intersection infrastructure and the
mass-retention lemma used by the intersection approach in
`RelaxedEveryScale.lean`.

## Main results

- `intersectShadingsList`: pointwise intersection of a nonempty list of shadings
- `IntersectionExtremalRetention`: hypothesis type for mass retention
- `intersection_mass_retention`: union-bound proof that the intersection of N
  subshadings each retaining ≥ 1-δ^ε of Y.mass retains ≥ 1/2 of Y.mass, and
  is therefore extremal at outputLoss.

## Proof sketch

For each pair of subshadings A, B of Y, inclusion-exclusion gives:
`A.mass + B.mass ≤ Y.mass + (A∩B).mass`.

Iterating this over a list via foldl, if each Z_k satisfies
`Y.mass ≤ Z_k.mass + c * Y.mass`, then the intersection Z satisfies
`Y.mass ≤ Z.mass + |Zs| * c * Y.mass`.

With `c = δ^ε` and `|Zs| * δ^ε ≤ 1/2`, we get `Z.mass ≥ (1/2) * Y.mass`,
which is enough to transfer extremality from Y at inputLoss to Z at outputLoss
with K=2 via `transfer_cropped_extremal_to_subshading`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Pointwise intersection of two shadings. -/
def intersectTwoShadings
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z1 Z2 : WZ1PaperTubeShading F) :
    WZ1PaperTubeShading F :=
  ⟨fun i => Z1.carrier i ∩ Z2.carrier i,
    fun i => (Z1.measurable_carrier i).inter (Z2.measurable_carrier i),
    fun i p hp => Z1.subset_body i hp.1⟩

/-- Pointwise intersection of a nonempty list of shadings. -/
def intersectShadingsList
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Zs : List (WZ1PaperTubeShading F)) (hne : Zs ≠ []) :
    WZ1PaperTubeShading F :=
  match Zs with
  | Z :: Zs => List.foldl intersectTwoShadings Z Zs
  | [] => False.elim (hne rfl)

/-- `intersectTwoShadings A B` is a subshading of both A and B. -/
lemma intersectTwoShadings_sub_left
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (A B : WZ1PaperTubeShading F) :
    PaperIsSubshading' (intersectTwoShadings A B) A :=
  fun i p hp => hp.1

lemma intersectTwoShadings_sub_right
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (A B : WZ1PaperTubeShading F) :
    PaperIsSubshading' (intersectTwoShadings A B) B :=
  fun i p hp => hp.2

/-- Foldl intersection is a subshading of the initial accumulator. -/
lemma foldl_intersect_sub_init
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (A : WZ1PaperTubeShading F) (Ys : List (WZ1PaperTubeShading F)) :
    PaperIsSubshading' (List.foldl intersectTwoShadings A Ys) A := by
  induction Ys generalizing A with
  | nil => exact fun i p hp => hp
  | cons B Ys ih =>
    have h1 : PaperIsSubshading' (List.foldl intersectTwoShadings (intersectTwoShadings A B) Ys)
        (intersectTwoShadings A B) := ih (A := intersectTwoShadings A B)
    intro i p hp
    exact (intersectTwoShadings_sub_left A B) i (h1 i hp)

/-- Foldl intersection is a subshading of any element in the list. -/
lemma foldl_intersect_sub_elem
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Ys : List (WZ1PaperTubeShading F)}
    {Z : WZ1PaperTubeShading F} (hZ : Z ∈ Ys) :
    ∀ (A : WZ1PaperTubeShading F),
      PaperIsSubshading' (List.foldl intersectTwoShadings A Ys) Z := by
  induction Ys with
  | nil =>
    exfalso
    simpa using hZ
  | cons B Ys ih =>
    intro A
    have h_mem : Z = B ∨ Z ∈ Ys := by simpa [List.mem_cons] using hZ
    by_cases h : Z = B
    · -- Z = B
      have h1 : PaperIsSubshading' (List.foldl intersectTwoShadings (intersectTwoShadings A B) Ys)
          (intersectTwoShadings A B) :=
        foldl_intersect_sub_init (intersectTwoShadings A B) Ys
      have h2 : PaperIsSubshading' (intersectTwoShadings A B) B :=
        intersectTwoShadings_sub_right A B
      rw [h]
      intro i p hp
      exact h2 i (h1 i hp)
    · -- Z ≠ B, so Z ∈ Ys
      have hZ' : Z ∈ Ys := h_mem.resolve_left h
      exact ih hZ' (intersectTwoShadings A B)

/-- The intersection is a subshading of each input. -/
lemma intersectShadingsList_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Zs : List (WZ1PaperTubeShading F)} {hne : Zs ≠ []}
    {Z : WZ1PaperTubeShading F} (hZ : Z ∈ Zs) :
    PaperIsSubshading' (intersectShadingsList Zs hne) Z := by
  have h_exists : ∃ (Y : WZ1PaperTubeShading F) (Ys : List (WZ1PaperTubeShading F)), Zs = Y :: Ys := by
    cases Zs with
    | nil => exfalso; exact hne rfl
    | cons Y Ys => exact ⟨Y, Ys, rfl⟩
  rcases h_exists with ⟨Y, Ys, h_eq⟩
  subst h_eq
  have hne' : (Y :: Ys) ≠ [] := by simp
  dsimp only [intersectShadingsList]
  have h_mem : Z = Y ∨ Z ∈ Ys := by simpa [List.mem_cons] using hZ
  rcases h_mem with (h_eq_Z | hZ')
  · rw [h_eq_Z]
    exact foldl_intersect_sub_init Y Ys
  · exact foldl_intersect_sub_elem hZ' Y

/--
Mass-retention hypothesis for the intersection approach.

Given a nonempty list of subshadings `Zs` of `Y`, each extremal at `outputLoss`,
and each retaining at least fraction `(1 - δ^ε)` of `Y.mass`, their pointwise
intersection is also extremal at `outputLoss` and satisfies the CWA bound.

This is discharged by `intersection_mass_retention` using the union bound:
intersection of N subshadings each retaining ≥ 1-δ^ε retains ≥ 1-N·δ^ε ≥ 1/2.
-/
def IntersectionExtremalRetention
    (sigma outputLoss : ℝ)
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} : Prop :=
  ∀ (N : ℕ) (epsilon inputLoss : ℝ),
    0 < N → 0 < epsilon → inputLoss < outputLoss → 0 < outputLoss →
    0 < delta → delta ≤ 1 →
    (N : ℝ) * Real.rpow delta epsilon ≤ 1 / 2 →
    WZ2PaperCroppedIsExtremal sigma inputLoss F Y →
    (2 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤ Kakeya.realRpowENN delta inputLoss →
    ∀ (Zs : List (WZ1PaperTubeShading F)) (hne : Zs ≠ []) (hZs_length : Zs.length = N),
      (∀ Z ∈ Zs, PaperIsSubshading' Z Y) →
      (∀ Z ∈ Zs, WZ2PaperCroppedIsExtremal sigma outputLoss F Z) →
      (∀ Z ∈ Zs, WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-outputLoss))) →
      (∀ Z ∈ Zs, ENNReal.ofReal (1 - Real.rpow delta epsilon) * Y.mass ≤ Z.mass) →
      WZ2PaperCroppedIsExtremal sigma outputLoss F (intersectShadingsList Zs hne) ∧
      WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-outputLoss))

/-- Intersection of two cubical paper shadings is cubical. -/
lemma intersectTwoShadings_cubical
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {A B : WZ1PaperTubeShading F}
    (hA : WZ1PaperIsCubicalShading A)
    (hB : WZ1PaperIsCubicalShading B) :
    WZ1PaperIsCubicalShading (intersectTwoShadings A B) := by
  intro i p hp
  have h1 : wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ A.carrier i := hA i p hp.1
  have h2 : wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ B.carrier i := hB i p hp.2
  intro q hq
  exact ⟨h1 hq, h2 hq⟩

/-- Pointwise intersection of a nonempty list of cubical paper shadings is cubical. -/
lemma intersectShadingsList_cubical
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Zs : List (WZ1PaperTubeShading F)} {hne : Zs ≠ []}
    (h : ∀ Z ∈ Zs, WZ1PaperIsCubicalShading Z) :
    WZ1PaperIsCubicalShading (intersectShadingsList Zs hne) := by
  have h_main : ∀ (L : List (WZ1PaperTubeShading F)) (A : WZ1PaperTubeShading F),
      WZ1PaperIsCubicalShading A →
      (∀ B ∈ L, WZ1PaperIsCubicalShading B) →
      WZ1PaperIsCubicalShading (List.foldl intersectTwoShadings A L) := by
    intro L
    induction L with
    | nil =>
      intro A hA _; exact hA
    | cons B L' ih =>
      intro A hA hB
      have hB_cub : WZ1PaperIsCubicalShading B := hB B (by simp)
      have hL'_cub : ∀ C ∈ L', WZ1PaperIsCubicalShading C :=
        fun C hC => hB C (by simp [hC])
      exact ih (intersectTwoShadings A B) (intersectTwoShadings_cubical hA hB_cub) hL'_cub
  rcases List.exists_cons_of_ne_nil hne with ⟨Z0, Ztail, rfl⟩
  exact h_main Ztail Z0 (h Z0 (by simp)) (fun W hW => h W (by simp [hW]))

/-- For two subshadings A, B of Y: A.mass + B.mass ≤ Y.mass + (A∩B).mass.

This is the per-tube inclusion-exclusion inequality summed over all tubes. -/
lemma intersectTwoShadings_mass_ineq
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y A B : WZ1PaperTubeShading F}
    (hA : PaperIsSubshading' A Y)
    (hB : PaperIsSubshading' B Y) :
    A.mass + B.mass ≤ Y.mass + (intersectTwoShadings A B).mass := by
  have h_per_tube : ∀ i : Fin F.card,
      volume (A.carrier i) + volume (B.carrier i) ≤
      volume (Y.carrier i) + volume ((intersectTwoShadings A B).carrier i) := by
    intro i
    have h_measA : MeasurableSet (A.carrier i) := A.measurable_carrier i
    have h_union : volume (A.carrier i ∪ B.carrier i) + volume (A.carrier i ∩ B.carrier i) =
        volume (A.carrier i) + volume (B.carrier i) :=
      MeasureTheory.measure_union_add_inter' h_measA (B.carrier i)
    have h_sub_union : A.carrier i ∪ B.carrier i ⊆ Y.carrier i := by
      intro x hx
      rcases hx with (hxA | hxB) <;> tauto
    have h_vol_union : volume (A.carrier i ∪ B.carrier i) ≤ volume (Y.carrier i) :=
      measure_mono h_sub_union
    have h_eq : (intersectTwoShadings A B).carrier i = A.carrier i ∩ B.carrier i := by rfl
    calc volume (A.carrier i) + volume (B.carrier i)
        = volume (A.carrier i ∪ B.carrier i) + volume (A.carrier i ∩ B.carrier i) := h_union.symm
      _ ≤ volume (Y.carrier i) + volume (A.carrier i ∩ B.carrier i) := by gcongr
      _ = volume (Y.carrier i) + volume ((intersectTwoShadings A B).carrier i) := by rw [h_eq]
  dsimp only [Kakeya.Streamlined.Shading.mass]
  calc (∑ i, volume (A.carrier i)) + (∑ i, volume (B.carrier i))
      = ∑ i, (volume (A.carrier i) + volume (B.carrier i)) := by rw [Finset.sum_add_distrib]
    _ ≤ ∑ i, (volume (Y.carrier i) + volume ((intersectTwoShadings A B).carrier i)) := by
        apply Finset.sum_le_sum; intro i _; exact h_per_tube i
    _ = (∑ i, volume (Y.carrier i)) + (∑ i, volume ((intersectTwoShadings A B).carrier i)) := by
        rw [Finset.sum_add_distrib]

/-- Union-bound mass lemma for foldl intersection.

Generalized over accumulator A and count k: if A retains ≥ fraction 1/(k·c)
and each W in L retains ≥ fraction 1/c, then the foldl intersection retains
≥ fraction 1/((k+|L|)·c) of Y's mass. -/
lemma foldl_intersect_mass_bound
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (c : ENNReal) (hY_mass_ne_top : Y.mass ≠ ⊤) :
    ∀ (L : List (WZ1PaperTubeShading F))
      (A : WZ1PaperTubeShading F) (k : ENNReal),
      PaperIsSubshading' A Y →
      Y.mass ≤ A.mass + k * c * Y.mass →
      (∀ W ∈ L, PaperIsSubshading' W Y) →
      (∀ W ∈ L, Y.mass ≤ W.mass + c * Y.mass) →
      Y.mass ≤ (List.foldl intersectTwoShadings A L).mass + (k + (L.length : ENNReal)) * c * Y.mass := by
  intro L
  induction L with
  | nil =>
    intro A k hA_sub hA_mass _ _
    simpa using hA_mass
  | cons W L' ih =>
    intro A k hA_sub hA_mass hL_sub hL_ret
    let A' := intersectTwoShadings A W
    have hA'_sub : PaperIsSubshading' A' Y := by
      intro i p hp; exact hA_sub i hp.1
    have hW_sub : PaperIsSubshading' W Y := hL_sub W (by simp)
    have h_mass_ineq : A.mass + W.mass ≤ Y.mass + A'.mass :=
      intersectTwoShadings_mass_ineq hA_sub hW_sub
    have hW_mass : Y.mass ≤ W.mass + c * Y.mass := hL_ret W (by simp)
    have h_k1 : k * c * Y.mass + c * Y.mass = (k + 1) * c * Y.mass := by
      have h2 : k * c + c = (k + 1) * c := by
        simp [add_mul] <;> abel
      calc k * c * Y.mass + c * Y.mass
          = (k * c) * Y.mass + c * Y.mass := by rfl
        _ = (k * c + c) * Y.mass := by rw [← add_mul]
        _ = ((k + 1) * c) * Y.mass := by rw [h2]
        _ = (k + 1) * c * Y.mass := by rfl
    have hA'_mass : Y.mass ≤ A'.mass + (k + 1) * c * Y.mass := by
      have h4 : Y.mass + Y.mass ≤ A.mass + W.mass + (k + 1) * c * Y.mass := by
        calc Y.mass + Y.mass
            ≤ (A.mass + k * c * Y.mass) + (W.mass + c * Y.mass) := by gcongr
          _ = A.mass + W.mass + (k * c * Y.mass + c * Y.mass) := by abel
          _ = A.mass + W.mass + (k + 1) * c * Y.mass := by rw [h_k1]
      have h5 : Y.mass + Y.mass ≤ Y.mass + (A'.mass + (k + 1) * c * Y.mass) := by
        calc Y.mass + Y.mass
            ≤ A.mass + W.mass + (k + 1) * c * Y.mass := h4
          _ ≤ Y.mass + A'.mass + (k + 1) * c * Y.mass := by gcongr <;> exact h_mass_ineq
          _ = Y.mass + (A'.mass + (k + 1) * c * Y.mass) := by abel
      exact (ENNReal.add_le_add_iff_left hY_mass_ne_top).mp h5
    have hL'_sub : ∀ X ∈ L', PaperIsSubshading' X Y :=
      fun X hX => hL_sub X (by simp [hX])
    have hL'_ret : ∀ X ∈ L', Y.mass ≤ X.mass + c * Y.mass :=
      fun X hX => hL_ret X (by simp [hX])
    have h_ih := ih A' (k + 1) hA'_sub hA'_mass hL'_sub hL'_ret
    have h_len : (k + 1 : ENNReal) + (L'.length : ENNReal) = k + ((W :: L').length : ENNReal) := by
      simp [add_assoc] <;> abel
    rw [h_len] at h_ih
    exact h_ih

/-- Union-bound mass lower bound for intersection of a list of subshadings.

If each Z_k satisfies `Y.mass ≤ Z_k.mass + c * Y.mass`, then
`Y.mass ≤ Z.mass + |Zs| * c * Y.mass`. -/
lemma intersectShadingsList_mass_bound
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (c : ENNReal)
    (Zs : List (WZ1PaperTubeShading F)) (hne : Zs ≠ [])
    (hZs_sub : ∀ Z ∈ Zs, PaperIsSubshading' Z Y)
    (h_ret : ∀ Z ∈ Zs, Y.mass ≤ Z.mass + c * Y.mass)
    (hY_mass_ne_top : Y.mass ≠ ⊤) :
    Y.mass ≤ (intersectShadingsList Zs hne).mass + (Zs.length : ENNReal) * c * Y.mass := by
  rcases List.exists_cons_of_ne_nil hne with ⟨Z0, Ztail, rfl⟩
  have hZ0_sub : PaperIsSubshading' Z0 Y := hZs_sub Z0 (by simp)
  have hZ0_mass : Y.mass ≤ Z0.mass + c * Y.mass := h_ret Z0 (by simp)
  have hZtail_sub : ∀ W ∈ Ztail, PaperIsSubshading' W Y :=
    fun W hW => hZs_sub W (by simp [hW])
  have hZtail_ret : ∀ W ∈ Ztail, Y.mass ≤ W.mass + c * Y.mass :=
    fun W hW => h_ret W (by simp [hW])
  have hZ0_mass' : Y.mass ≤ Z0.mass + (1 : ENNReal) * c * Y.mass := by
    have h1 : (1 : ENNReal) * c * Y.mass = c * Y.mass := by simp
    rw [h1]
    exact hZ0_mass
  have h := foldl_intersect_mass_bound c hY_mass_ne_top Ztail Z0 1 hZ0_sub hZ0_mass' hZtail_sub hZtail_ret
  have h_len : (1 : ENNReal) + (Ztail.length : ENNReal) = ((Z0 :: Ztail).length : ENNReal) := by
    have h2 : ((Z0 :: Ztail).length : ENNReal) = (Ztail.length : ENNReal) + 1 := by
      simp [List.length_cons, Nat.cast_add]
    rw [h2] <;> abel
  rw [h_len] at h
  exact h

/-- From `Y.mass ≤ Z.mass + N * c * Y.mass` and `N * c ≤ 1/2`, deduce `(1/2) * Y.mass ≤ Z.mass`. -/
lemma half_mass_from_bound
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : WZ1PaperTubeShading F} (c N : ENNReal)
    (hY_ne_top : Y.mass ≠ ⊤)
    (h_bound : Y.mass ≤ Z.mass + N * c * Y.mass)
    (h_small : N * c ≤ (1 / 2 : ENNReal)) :
    (1 / 2 : ENNReal) * Y.mass ≤ Z.mass := by
  have h4 : N * c * Y.mass ≤ (1 / 2 : ENNReal) * Y.mass := by
    gcongr <;> exact h_small
  have h5 : Y.mass ≤ Z.mass + (1 / 2 : ENNReal) * Y.mass :=
    h_bound.trans (by gcongr <;> exact h4)
  have h7 : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
    have h71 : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = (2 : ENNReal) * (1 / 2 : ENNReal) := by
      rw [two_mul]
    rw [h71]
    have h72 : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
      have h_div : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
        simp [one_div]
      rw [h_div]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    exact h72
  have h6 : Y.mass = (1 / 2 : ENNReal) * Y.mass + (1 / 2 : ENNReal) * Y.mass := by
    have h61 : Y.mass = 1 * Y.mass := by simp
    have h62 : 1 * Y.mass = ((1 / 2 : ENNReal) + (1 / 2 : ENNReal)) * Y.mass := by rw [h7] <;> simp
    have h63 : ((1 / 2 : ENNReal) + (1 / 2 : ENNReal)) * Y.mass =
        (1 / 2 : ENNReal) * Y.mass + (1 / 2 : ENNReal) * Y.mass := by rw [add_mul]
    exact h61.trans h62 |>.trans h63
  have h_half_ne_top : (1 / 2 : ENNReal) * Y.mass ≠ ⊤ :=
    mul_ne_top (by norm_num) hY_ne_top
  have h5' : (1 / 2 : ENNReal) * Y.mass + (1 / 2 : ENNReal) * Y.mass ≤
      Z.mass + (1 / 2 : ENNReal) * Y.mass := by
    have h_eq : (1 / 2 : ENNReal) * Y.mass + (1 / 2 : ENNReal) * Y.mass = Y.mass := h6.symm
    rw [h_eq]
    exact h5
  exact (ENNReal.add_le_add_iff_right h_half_ne_top).mp h5'

/--
Mass retention lemma for the intersection approach.

Given N subshadings Z_k of Y, each retaining at least fraction (1 - δ^ε) of Y's mass,
their intersection Z retains at least fraction (1 - N·δ^ε) of Y's mass.

For small δ and ε = outputLoss/(2N), this gives Z.mass ≥ (1/2) · Y.mass,
which is enough for the density condition at outputLoss.

The retention hypothesis `h_retention` must be established from the specific
construction of each Z_k (e.g., from the one-scale lemma's internal pruning).
-/
lemma intersection_mass_retention
    {delta sigma inputLoss outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (N : ℕ) (hN_pos : 0 < N)
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon)
    (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hinput_lt_output : inputLoss < outputLoss)
    (houtput_pos : 0 < outputLoss)
    (hsmall : (N : ℝ) * Real.rpow delta epsilon ≤ 1 / 2)
    (Zs : List (WZ1PaperTubeShading F)) (hne : Zs ≠ [])
    (hZs_length : Zs.length = N)
    (hZs_sub : ∀ Z ∈ Zs, PaperIsSubshading' Z Y)
    (hZs_ext : ∀ Z ∈ Zs, WZ2PaperCroppedIsExtremal sigma outputLoss F Z)
    (hZs_cwa : ∀ Z ∈ Zs, WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-outputLoss)))
    (h_retention : ∀ Z ∈ Zs,
      ENNReal.ofReal (1 - Real.rpow delta epsilon) * Y.mass ≤ Z.mass)
    (hY_ext : WZ2PaperCroppedIsExtremal sigma inputLoss F Y)
    (hslack : (2 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤ Kakeya.realRpowENN delta inputLoss) :
    WZ2PaperCroppedIsExtremal sigma outputLoss F (intersectShadingsList Zs hne) ∧
    WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-outputLoss)) := by
  let Z := intersectShadingsList Zs hne
  let c : ENNReal := ENNReal.ofReal (Real.rpow delta epsilon)

  -- Y.mass is finite
  have hY_mass_ne_top : Y.mass ≠ ⊤ := by
    have h1 : volume Y.union ≤ Kakeya.realRpowENN delta (sigma - inputLoss) := hY_ext.volume_upper
    have h2 : volume Y.union ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]) h1
    have h3 : Y.mass ≤ (F.card : ENNReal) * volume Y.union := by
      dsimp only [Kakeya.Streamlined.Shading.mass]
      have h4 : ∀ i : Fin F.card, volume (Y.carrier i) ≤ volume Y.union := by
        intro i; apply measure_mono; intro p hp; exact ⟨i, hp⟩
      calc ∑ i : Fin F.card, volume (Y.carrier i)
          ≤ ∑ i : Fin F.card, volume Y.union := Finset.sum_le_sum fun i _ => h4 i
        _ = (F.card : ENNReal) * volume Y.union := by
          simp [Finset.sum_const, mul_comm]
    exact ne_top_of_le_ne_top (mul_ne_top (by exact ENNReal.natCast_ne_top _) h2) h3

  -- Convert retention: Y.mass ≤ Z_k.mass + c * Y.mass
  have h1m : ENNReal.ofReal (1 - Real.rpow delta epsilon) + c = 1 := by
    have h4 : 0 ≤ 1 - Real.rpow delta epsilon := by
      have h5 : Real.rpow delta epsilon ≤ 1 :=
        Real.rpow_le_one hdelta_pos.le hdelta_le_one hepsilon_pos.le
      linarith
    have h_x_nonneg : 0 ≤ Real.rpow delta epsilon := Real.rpow_nonneg hdelta_pos.le epsilon
    have h_add : ENNReal.ofReal (1 - Real.rpow delta epsilon) + ENNReal.ofReal (Real.rpow delta epsilon) =
        ENNReal.ofReal ((1 - Real.rpow delta epsilon) + Real.rpow delta epsilon) :=
      (ENNReal.ofReal_add h4 h_x_nonneg).symm
    have h_sum : (1 - Real.rpow delta epsilon) + Real.rpow delta epsilon = 1 := by ring
    dsimp only [c]
    rw [h_add, h_sum]
    <;> simp
  have h_ret' : ∀ W ∈ Zs, Y.mass ≤ W.mass + c * Y.mass := by
    intro W hW
    have h5 : ENNReal.ofReal (1 - Real.rpow delta epsilon) * Y.mass ≤ W.mass := h_retention W hW
    have h6 : (ENNReal.ofReal (1 - Real.rpow delta epsilon) + c) * Y.mass = Y.mass := by
      rw [h1m]
      <;> simp
    calc Y.mass
      = (ENNReal.ofReal (1 - Real.rpow delta epsilon) + c) * Y.mass := h6.symm
    _ = ENNReal.ofReal (1 - Real.rpow delta epsilon) * Y.mass + c * Y.mass := by rw [add_mul]
    _ ≤ W.mass + c * Y.mass := add_le_add h5 (le_refl (c * Y.mass))

  -- Union bound mass lower bound
  have h_mass_bound : Y.mass ≤ Z.mass + (Zs.length : ENNReal) * c * Y.mass :=
    intersectShadingsList_mass_bound c Zs hne hZs_sub h_ret' hY_mass_ne_top

  -- Convert hsmall to ENNReal
  have hsmall' : (N : ENNReal) * c ≤ (1 / 2 : ENNReal) := by
    have h_N : (N : ENNReal) = ENNReal.ofReal (N : ℝ) := by norm_cast
    have h_c : c = ENNReal.ofReal (Real.rpow delta epsilon) := by rfl
    rw [h_N, h_c]
    have h_mul : ENNReal.ofReal (N : ℝ) * ENNReal.ofReal (Real.rpow delta epsilon) =
        ENNReal.ofReal ((N : ℝ) * Real.rpow delta epsilon) := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ (N : ℝ) by positivity)]
      <;> rfl
    rw [h_mul]
    have h_half : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
      have h1 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by simp [one_div]
      rw [h1]
      have h2 : (2 : ENNReal)⁻¹ = (ENNReal.ofReal (2 : ℝ))⁻¹ := by norm_cast
      rw [h2]
      have h3 : (ENNReal.ofReal (2 : ℝ))⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by
        rw [← ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < 2 by norm_num)]
      rw [h3]
      have h4 : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num
      rw [h4]
    rw [h_half]
    exact ENNReal.ofReal_le_ofReal hsmall

  -- Half mass bound
  have h3 : (Zs.length : ENNReal) = (N : ENNReal) := by
    rw [hZs_length] <;> norm_cast
  have h_half_mass : (1 / 2 : ENNReal) * Y.mass ≤ Z.mass := by
    rw [h3] at h_mass_bound
    exact half_mass_from_bound (c := c) (N := (N : ENNReal)) hY_mass_ne_top h_mass_bound hsmall'

  -- Cubicality
  have hZ_cubical : WZ1PaperIsCubicalShading Z :=
    intersectShadingsList_cubical (fun W hW => (hZs_ext W hW).cubical)

  -- Subshading
  rcases List.exists_cons_of_ne_nil hne with ⟨Z0, Ztail, hZs_eq⟩
  have hZ0_in_Zs : Z0 ∈ Zs := by
    rw [hZs_eq] <;> simp
  have hZ_sub_Z0 : PaperIsSubshading' Z Z0 :=
    intersectShadingsList_subshading hZ0_in_Zs
  have hZ_sub_Y : PaperIsSubshading Z Y := by
    intro i p hp
    exact hZs_sub Z0 hZ0_in_Zs i (hZ_sub_Z0 i hp)

  -- Transfer extremal
  have hK_inv : (2 : ENNReal)⁻¹ = (1 / 2 : ENNReal) := by simp [one_div]
  have h_half_mass' : (2 : ENNReal)⁻¹ * Y.mass ≤ Z.mass := by
    rw [hK_inv]
    exact h_half_mass
  have hZ_ext : WZ2PaperCroppedIsExtremal sigma outputLoss F Z :=
    transfer_cropped_extremal_to_subshading
      (K := (2 : ENNReal))
      (by norm_num) (by norm_num)
      hY_ext hZ_sub_Y h_half_mass' hZ_cubical
      (by linarith) hslack hdelta_pos hdelta_le_one houtput_pos

  -- CWA
  have hZ_cwa : WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-outputLoss)) :=
    hZs_cwa Z0 hZ0_in_Zs

  exact ⟨hZ_ext, hZ_cwa⟩

end Kakeya.Assouad.PureWZ2
