/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedProfile
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedTowerGeometryData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody Tube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

/-- Proposed four-parameter local line packing auxiliary, motivated by
S:153-163 and S:4833-4850. -/
theorem source_lineED_card_in_thin_tube
    {iota : Type u} {delta rho : NNReal} {A : Nat}
    (s : Finset iota) (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
    (P : Tube rho (EuclideanSpace Real (Fin 3)))
    (hdelta : 0 < delta) (hscale : delta <= rho) (hrho : rho <= 1 / 40)
    (hcontain : ∀ i ∈ s, (T i).toConvexSpaceBody <= P.toConvexSpaceBody)
    (hed : Kakeya.VeryNotSticky.IsLineEssDistinct A s T) :
    (s.card : Real) <= (2 ^ 40 : Real) * (A : Real) *
      ((rho : Real) / (delta : Real)) ^ 4 := by
  classical
  let E := EuclideanSpace Real (Fin 3)
  let F := P.perpSpace
  let H := WithLp 2 (F × F)
  let pr : E →L[Real] F := ((Real ∙ P.direction)ᗮ).orthogonalProjectionOnto
  let ax : E → Real := fun z => inner Real P.direction z
  let slope : iota → F := fun i => (ax (T i).direction)⁻¹ • pr (T i).direction
  let offset : iota → F := fun i =>
    pr ((T i).x - P.x) - ax ((T i).x - P.x) • slope i
  let param : iota → H := fun i => WithLp.toLp 2 (offset i, slope i)
  have hd : 0 < (delta : Real) := hdelta
  have hr : (rho : Real) ≤ 1 / 40 := by exact_mod_cast hrho
  have hpr (z : E) : (pr z : E) = z - ax z • P.direction :=
    (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton P.norm_direction z).1
  have hprnorm (z : E) : ‖pr z‖ = ‖z - ax z • P.direction‖ :=
    (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton P.norm_direction z).2
  have hposition {z : E} (hz : z ∈ P.carrier) :
      ‖z - P.x‖ ≤ 2 ∧ |ax (z - P.x)| ≤ 2 ∧ ‖pr (z - P.x)‖ ≤ rho := by
    have hperp : ‖pr (z - P.x)‖ ≤ rho := by
      rw [hprnorm]
      exact P.perp_norm_le_of_mem_carrier hz
    obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp (P.carrier_eq ▸ hz)
    have hc1 : dist c P.x ≤ 1 := (convex_closedBall P.x (1 : Real)).segment_subset
      (mem_closedBall_self zero_le_one)
      (by rw [mem_closedBall, dist_comm]; exact P.dist_eq_one.le) hc
    have hz2 : ‖z - P.x‖ ≤ 2 := by
      have hzdist := dist_triangle z c P.x
      rw [mem_closedBall] at hzc
      rw [← dist_eq_norm]
      linarith
    refine ⟨hz2, ?_, hperp⟩
    calc
      |ax (z - P.x)| ≤ ‖P.direction‖ * ‖z - P.x‖ := abs_real_inner_le_norm _ _
      _ ≤ 2 := by rw [P.norm_direction, one_mul]; exact hz2
  have htilt (i : iota) (hi : i ∈ s) :
      1 / 2 ≤ |ax (T i).direction| ∧ ‖slope i‖ ≤ 4 * (rho : Real) := by
    have hp : ‖pr (T i).direction‖ ≤ 2 * (rho : Real) := by
      rw [hprnorm]
      exact P.perp_norm_direction_le_of_subset (T i) (hcontain i hi)
    have hsq : (ax (T i).direction) ^ 2 + ‖pr (T i).direction‖ ^ 2 = 1 := by
      rw [hprnorm]
      have hh := P.norm_sq_sub (T i).direction 0
      simpa only [ax, sub_zero, (T i).norm_direction, one_pow] using hh.symm
    have ha : 1 / 2 ≤ |ax (T i).direction| := by
      have hpn := norm_nonneg (pr (T i).direction)
      have han := abs_nonneg (ax (T i).direction)
      nlinarith [sq_abs (ax (T i).direction)]
    refine ⟨ha, ?_⟩
    have hainv : |ax (T i).direction|⁻¹ ≤ 2 :=
      (inv_le_iff_one_le_mul₀ (by linarith : 0 < |ax (T i).direction|)).2 (by linarith)
    calc
      ‖slope i‖ = |ax (T i).direction|⁻¹ * ‖pr (T i).direction‖ := by
        simp only [slope, norm_smul, Real.norm_eq_abs, abs_inv]
      _ ≤ 2 * (2 * (rho : Real)) := mul_le_mul hainv hp (norm_nonneg _) (by norm_num)
      _ = 4 * (rho : Real) := by ring
  have hparam (i : iota) (hi : i ∈ s) : ‖param i‖ ≤ 16 * (rho : Real) := by
    have hx := hposition (hcontain i hi (T i).x_mem_carrier)
    have hs := (htilt i hi).2
    have ho : ‖offset i‖ ≤ 9 * (rho : Real) := by
      calc
        ‖offset i‖ ≤ ‖pr ((T i).x - P.x)‖ + ‖ax ((T i).x - P.x) • slope i‖ := norm_sub_le _ _
        _ = ‖pr ((T i).x - P.x)‖ + |ax ((T i).x - P.x)| * ‖slope i‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (rho : Real) + 2 * (4 * (rho : Real)) :=
          add_le_add hx.2.2 (mul_le_mul hx.2.1 hs (norm_nonneg _) (by norm_num))
        _ = 9 * (rho : Real) := by ring
    have heq := WithLp.prod_norm_sq_eq_of_L2 (param i)
    change ‖param i‖ ^ 2 = ‖offset i‖ ^ 2 + ‖slope i‖ ^ 2 at heq
    nlinarith [norm_nonneg (offset i), norm_nonneg (slope i),
      norm_nonneg (param i), rho.coe_nonneg]
  have hdir (j : iota) (hj : j ∈ s) :
      P.direction + (slope j : E) = (ax (T j).direction)⁻¹ • (T j).direction := by
    have hne : ax (T j).direction ≠ 0 := by
      have := (htilt j hj).1
      intro hz
      simp only [hz, abs_zero] at this
      norm_num at this
    change P.direction + (ax (T j).direction)⁻¹ • (pr (T j).direction : E) = _
    rw [hpr, smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
    module
  have hbase (j : iota) :
      P.x + (offset j : E) + ax ((T j).x - P.x) • (P.direction + (slope j : E)) =
        (T j).x := by
    change P.x + ((pr ((T j).x - P.x) : E) -
      ax ((T j).x - P.x) • (slope j : E)) +
      ax ((T j).x - P.x) • (P.direction + (slope j : E)) = (T j).x
    rw [hpr]
    module
  have hline (j : iota) (hj : j ∈ s) (t : Real) :
      P.x + (offset j : E) + t • (P.direction + (slope j : E)) ∈
        Kakeya.VeryNotSticky.lineSet (T j).x (T j).direction := by
    refine ⟨(t - ax ((T j).x - P.x)) * (ax (T j).direction)⁻¹, ?_⟩
    calc
      P.x + (offset j : E) + t • (P.direction + (slope j : E))
        = (P.x + (offset j : E) + ax ((T j).x - P.x) •
            (P.direction + (slope j : E))) +
            (t - ax ((T j).x - P.x)) • (P.direction + (slope j : E)) := by module
      _ = (T j).x + ((t - ax ((T j).x - P.x)) *
          (ax (T j).direction)⁻¹) • (T j).direction := by rw [hbase, hdir j hj, smul_smul]
  have hclose (i j : iota) (hi : i ∈ s) (hj : j ∈ s)
      (hij : dist (param i) (param j) ≤ delta) :
      (T i).carrier ⊆ Kakeya.VeryNotSticky.lineNbhd (T j).x (T j).direction (5 * (delta : Real)) := by
    have ho : ‖offset i - offset j‖ ≤ delta := by
      have hh := (WithLp.dist_fst_le (param i) (param j)).trans hij
      change dist (offset i) (offset j) ≤ (delta : Real) at hh
      rwa [dist_eq_norm] at hh
    have hs : ‖slope i - slope j‖ ≤ delta := by
      have hh := (WithLp.dist_snd_le (param i) (param j)).trans hij
      change dist (slope i) (slope j) ≤ (delta : Real) at hh
      rwa [dist_eq_norm] at hh
    intro z hz
    obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp ((T i).carrier_eq ▸ hz)
    have hcT : c ∈ (T i).carrier := by
      rw [(T i).carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨c, hc, mem_closedBall_self delta.coe_nonneg⟩
    have hcax := (hposition (hcontain i hi hcT)).2.1
    let t := ax (c - P.x)
    let q := P.x + (offset j : E) + t • (P.direction + (slope j : E))
    have hcform : c = P.x + (offset i : E) + t • (P.direction + (slope i : E)) := by
      rw [segment_eq_image_lineMap] at hc
      obtain ⟨u, hu, huc⟩ := hc
      have hc' : c = (T i).x + u • (T i).direction := by
        rw [← huc]
        simp [AffineMap.lineMap_apply, Tube.direction]
        module
      have ht : t = ax ((T i).x - P.x) + u * ax (T i).direction := by
        dsimp [t, ax]
        rw [hc']
        have hh : (T i).x + u • (T i).direction - P.x =
            ((T i).x - P.x) + u • (T i).direction := by module
        rw [hh, inner_add_right, real_inner_smul_right]
      rw [ht, add_smul, ← add_assoc, hbase, hdir i hi, smul_smul]
      have hne : ax (T i).direction ≠ 0 := by
        have := (htilt i hi).1
        intro hz
        simp only [hz, abs_zero] at this
        norm_num at this
      rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
      exact hc'
    have hcq : dist c q ≤ 3 * (delta : Real) := by
      rw [dist_eq_norm, hcform]
      have heq : P.x + (offset i : E) + t • (P.direction + (slope i : E)) - q =
          ((offset i - offset j : F) : E) + t • ((slope i - slope j : F) : E) := by
        change P.x + (offset i : E) + t • (P.direction + (slope i : E)) -
          (P.x + (offset j : E) + t • (P.direction + (slope j : E))) =
          ((offset i : E) - (offset j : E)) + t • ((slope i : E) - (slope j : E))
        module
      rw [heq]
      calc
        ‖((offset i - offset j : F) : E) + t • ((slope i - slope j : F) : E)‖
          ≤ ‖offset i - offset j‖ + |t| * ‖slope i - slope j‖ := by
            simpa only [norm_smul, Real.norm_eq_abs, Submodule.norm_coe] using
              norm_add_le ((offset i - offset j : F) : E) (t • ((slope i - slope j : F) : E))
        _ ≤ (delta : Real) + 2 * (delta : Real) :=
          add_le_add ho (mul_le_mul hcax hs (norm_nonneg _) (by norm_num))
        _ = 3 * (delta : Real) := by ring
    apply Metric.mem_cthickening_of_dist_le z q (5 * (delta : Real)) _ (hline j hj t)
    rw [mem_closedBall] at hzc
    exact (dist_triangle z c q).trans (by linarith)
  have hdim : Module.finrank Real H = 4 := by
    calc
      Module.finrank Real H = Module.finrank Real (F × F) :=
        LinearEquiv.finrank_eq (WithLp.linearEquiv 2 Real (F × F))
      _ = Module.finrank Real F + Module.finrank Real F := Module.finrank_prod
      _ = 4 := by simp [F, Tube.finrank_perpSpace]
  letI : Nontrivial H := Module.nontrivial_of_finrank_pos (R := Real) (M := H)
    (by rw [hdim]; norm_num)
  letI : MeasurableSpace H := borel H
  letI : BorelSpace H := ⟨rfl⟩
  obtain ⟨v, hvsub, hvsep, hvcover, _⟩ :=
    (s.image param).finite_toSet.isBounded.exists_finset_isSeparated_isCover_closedBall hdelta
  have hcover (i : iota) (hi : i ∈ s) : ∃ c ∈ v, dist (param i) c ≤ delta := by
    simpa only [mem_closedBall, exists_prop] using
      Set.mem_iUnion₂.mp (hvcover (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  let label : iota → H := fun i => if hi : i ∈ s then (hcover i hi).choose else 0
  have hlabel (i : iota) (hi : i ∈ s) : label i ∈ v ∧ dist (param i) (label i) ≤ delta := by
    simpa only [label, dif_pos hi] using (hcover i hi).choose_spec
  have hcount : s.card ≤ A * v.card := by
    apply Finset.card_le_mul_card_image_of_maps_to (fun i hi => (hlabel i hi).1) A
    intro c hc
    obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp (hvsub hc)
    refine (Finset.card_le_card ?_).trans (hed (T j).x (T j).direction (T j).norm_direction)
    intro i hi
    obtain ⟨his, hic⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨his, hclose i j his hj ?_⟩
    simpa only [hic, hjc] using (hlabel i his).2
  have hvball : (v : Set H) ⊆ closedBall 0 (16 * (rho : Real)) := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hvsub hc)
    simpa only [mem_closedBall, dist_zero_right] using hparam i hi
  have hvcard : (v.card : Real) ≤ (2 ^ 40 : Real) * ((rho : Real) / (delta : Real)) ^ 4 := by
    have hpack := Metric.card_le_of_isSeparated_subset_closedBall hdelta
      (by positivity : 0 ≤ 16 * (rho : Real)) hvball hvsep
    rw [hdim] at hpack
    have hratio : 2 * (16 * (rho : Real) + delta) / (delta : Real) ≤
        34 * ((rho : Real) / (delta : Real)) := by
      rw [div_le_iff₀ hd]
      have hsc : (delta : Real) ≤ rho := hscale
      field_simp
      linarith
    calc
      (v.card : Real) ≤ (2 * (16 * (rho : Real) + delta) / (delta : Real)) ^ 4 := hpack
      _ ≤ (34 * ((rho : Real) / (delta : Real))) ^ 4 := by gcongr
      _ ≤ (2 ^ 40 : Real) * ((rho : Real) / (delta : Real)) ^ 4 := by
        rw [mul_pow]
        gcongr
        norm_num
  calc
    (s.card : Real) ≤ (A : Real) * (v.card : Real) := by exact_mod_cast hcount
    _ ≤ (A : Real) * ((2 ^ 40 : Real) * ((rho : Real) / (delta : Real)) ^ 4) := by gcongr
    _ = (2 ^ 40 : Real) * (A : Real) * ((rho : Real) / (delta : Real)) ^ 4 := by ring

/-- S:2679-2686 for the fixed source constants. The generous local packing
coefficient must fit the unchanged sourceTowerWindowConstant. -/
theorem source_assignedProfile_crude_four
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M : Nat}
    (Q : SourceThreadedTower S T M sourceThreadConstant)
    (hM : 2 <= M) (hdelta : 0 < delta)
    (hsmall : delta < (400 : NNReal) ^ (-(M : Real)))
    (hgeometry : SourceTowerGeometry Q sourceBottomED sourceLevelED)
    {a b : Nat} (hab : a < b) (hb : b <= M) :
    Q.assignedProfile S a b <=
      (sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED : ENNReal) *
        ENNReal.ofReal (((sourceTowerRadius delta M a : Real) /
          (sourceTowerRadius delta M b : Real)) ^ 4) := by
  classical
  have hMr : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  let x : NNReal := delta ^ (1 / (M : Real))
  have hx : x ≤ (1 / 400 : NNReal) := by
    calc
      x ≤ ((400 : NNReal) ^ (-(M : Real))) ^ (1 / (M : Real)) :=
        NNReal.rpow_le_rpow hsmall.le (by positivity)
      _ = 1 / 400 := by
        rw [← NNReal.rpow_mul]
        have he : (-(M : Real)) * (1 / (M : Real)) = -1 := by field_simp
        rw [he]
        norm_num
  have hx1 : x ≤ 1 := hx.trans (by
    norm_num [div_le_iff₀ (show (0 : NNReal) < 400 by norm_num)])
  have hrep (k : Nat) : delta ^ ((k : Real) / (M : Real)) = x ^ k := by
    rw [show (k : Real) / (M : Real) = (1 / (M : Real)) * (k : Real) by ring,
      NNReal.rpow_mul, NNReal.rpow_natCast]
  have hbottom : delta = x ^ M := by
    simpa [div_self hMr.ne', NNReal.rpow_one] using hrep M
  have hrpos (k : Nat) : 0 < sourceTowerRadius delta M k := by
    unfold sourceTowerRadius
    split <;> positivity
  have hrsmall (k : Nat) (hk : k < M) : sourceTowerRadius delta M k ≤ 1 / 40 := by
    rw [sourceTowerRadius, if_pos hk, hrep]
    have hpow : x ^ k ≤ 1 := by
      simpa using pow_le_pow_of_le_one (by positivity : 0 ≤ x) hx1 (Nat.zero_le k)
    exact mul_le_of_le_one_right (by positivity) hpow
  have haM : a < M := by omega
  have hrorder : sourceTowerRadius delta M b ≤ sourceTowerRadius delta M a := by
    simp only [sourceTowerRadius, if_pos haM, hrep]
    by_cases hbM : b < M
    · rw [if_pos hbM]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by positivity) hx1 hab.le) (by positivity)
    · rw [if_neg hbM, hbottom]
      have hp : x ^ M ≤ x ^ a * x := by
        rw [← pow_succ]
        exact pow_le_pow_of_le_one (by positivity) hx1 (by omega)
      calc
        x ^ M ≤ x ^ a * x := hp
        _ ≤ x ^ a * (1 / 400) := mul_le_mul_of_nonneg_left hx (by positivity)
        _ ≤ (1 / 40) * x ^ a := by nlinarith [show 0 ≤ x ^ a by positivity]
  have hpath : ∀ k, a ≤ k → k ≤ M → ∀ i ∈ S,
      (Q.tube k (Q.place k i)).toConvexSpaceBody ≤
        (Q.tube a (Q.place a i)).toConvexSpaceBody := by
    intro k hak
    induction k, hak using Nat.le_induction with
    | base => intro _ i hi; exact le_rfl
    | succ k hak ih =>
      intro hk i hi
      have hp := Q.parent_containment k (by omega) (Q.place (k + 1) i)
        (Q.place_mem (k + 1) hk i hi)
      rw [← Q.parent_composition k (by omega) i hi] at hp
      exact hp.trans (ih (by omega) i hi)
  let A := max sourceBottomED sourceLevelED
  have hed : Kakeya.VeryNotSticky.IsLineEssDistinct A (Q.indexSet b) (Q.tube b) := by
    by_cases hbM : b = M
    · subst b
      intro p d hd
      have hcarr (i : iota) (hi : i ∈ S) : (Q.tube M i).carrier = (T i).carrier :=
        congrArg ConvexSpaceBody.carrier (Q.bottom_body i hi)
      have hfilters :
          ((Q.indexSet M).filter (fun i => (Q.tube M i).carrier ⊆
            Kakeya.VeryNotSticky.lineNbhd p d (5 * (sourceTowerRadius delta M M : Real)))) =
          S.filter (fun i => (T i).carrier ⊆
            Kakeya.VeryNotSticky.lineNbhd p d (5 * (delta : Real))) := by
        rw [Q.bottom_index]
        apply Finset.filter_congr
        intro i hi
        rw [hcarr i hi]
        simp only [sourceTowerRadius, lt_self_iff_false, if_false]
      rw [hfilters]
      exact (hgeometry.original_ed p d hd).trans (le_max_left _ _)
    · intro p d hd
      exact (hgeometry.coarse_ed b (by omega) p d hd).trans (le_max_right _ _)
  have hconst : (2 ^ 40 : Real) * (A : Real) ≤
      (sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED : Real) := by
    norm_num [A, sourceTowerWindowConstant, sourceThreadConstant, sourceBottomED, sourceLevelED]
  unfold SourceThreadedTower.assignedProfile
  apply Finset.sup_le
  intro j hj
  let f := Q.retainedAssignedFibre S a b j
  have hfsub : f ⊆ Q.indexSet b := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Q.place_mem b hb i (Finset.mem_filter.mp hi).1
  have hfcontain (k : iota) (hk : k ∈ f) :
      (Q.tube b k).toConvexSpaceBody ≤ (Q.tube a j).toConvexSpaceBody := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
    simpa only [hij] using hpath b hab.le hb i his
  have hcard := source_lineED_card_in_thin_tube f (Q.tube b) (Q.tube a j)
    (hrpos b) hrorder (hrsmall a haM) hfcontain (hed.subset hfsub)
  have hbound : (f.card : Real) ≤
      (sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED : Real) *
        (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ 4) :=
    hcard.trans (mul_le_mul_of_nonneg_right hconst (by positivity))
  refine (Kakeya.maxDensity_le_card f (fun k => (Q.tube b k).toConvexSpaceBody)).trans ?_
  have hboundE := ENNReal.ofReal_le_ofReal hbound
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using hboundE

end Kakeya.ML2Core
