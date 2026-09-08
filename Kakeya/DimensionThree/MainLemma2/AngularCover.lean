/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ShadedUniform
public import Kakeya.Tube.Nets
public import Kakeya.Covers
public import Kakeya.Mathlib.Analysis.IsSeparated
public import Kakeya.Asymptotics

/-!
# The angular hierarchy of a family of directions

Blueprint `lem:ml2murho` needs a multiscale hierarchy on the *directions* of a family of
`δ`-tubes, not on their positions: the object it uniformizes is `𝕋_Y(x)` read as a subset of
`S²`.  The spatial hierarchy carried by `Kakeya.VeryNotSticky` cannot serve, because two tubes
through a common point with the same direction but different positions along the axis lie in no
common thin tube, while the angular fibre of `defmurho` does not separate them.

This file builds the angular hierarchy as an honest `Tube.GridCoverSystem`, by the device
of moving every tube to the origin: `Kakeya.AngularCover.dirTube σ v i` is the `σ`-tube with
midpoint `0` and direction `v i`, so that containment of one such tube in another is a condition
on directions *alone*.  The nodes are the tubes of a nested family of `σ_k/8`-separated nets of
directions, so the classes of the cover are exactly the angular cells at the scale `σ_k`, and
two members of a class have directions within `σ_k/2` of each other
(`Kakeya.AngularCover.norm_sub_of_assign_eq`).

The counting lemma the consumer needs is `Kakeya.AngularCover.card_image_le_of_ball`: a family of
members whose directions lie in a ball of radius `R` around a fixed direction (or around its
antipode) meets at most `C (1 + R/σ_k)^n` classes at the scale `σ_k`.  It is a pure packing
bound on the separated net of node directions, with no tube geometry in it at all; the tube
geometry is confined to the construction of the cover system.
-/

@[expose] public section

open MeasureTheory Metric Set

open scoped ENNReal NNReal

namespace Kakeya.AngularCover

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The `σ`-tube with midpoint `0` and direction `v i`. -/
noncomputable def dirTube {ι : Type*} (σ : NNReal) (v : ι → E) (hv : ∀ i, ‖v i‖ = 1) (i : ι) :
    Tube σ E :=
  Tube.ofMidpointDirection σ 0 (v i) (hv i)

@[simp] lemma dirTube_midpoint {ι : Type*} (σ : NNReal) (v : ι → E) (hv : ∀ i, ‖v i‖ = 1)
    (i : ι) : (dirTube σ v hv i).midpoint = 0 := by
  show (1/2 : ℝ) • ((0 - (1/2 : ℝ) • v i) + (0 + (1/2 : ℝ) • v i)) = 0
  module

@[simp] lemma dirTube_direction {ι : Type*} (σ : NNReal) (v : ι → E) (hv : ∀ i, ‖v i‖ = 1)
    (i : ι) : (dirTube σ v hv i).direction = v i := by
  show (0 + (1/2 : ℝ) • v i) - (0 - (1/2 : ℝ) • v i) = v i
  module

/-- A `dirTube` at a small radius sits inside a `dirTube` at a large radius as soon as the two
directions are close: `ε/2 + σ ≤ τ`. -/
lemma dirTube_le_dirTube {ι : Type*} {σ τ : NNReal} (v : ι → E) (hv : ∀ i, ‖v i‖ = 1)
    {i j : ι} {ε : ℝ} (hd : ‖v i - v j‖ ≤ ε) (hcond : ε / 2 + (σ : ℝ) ≤ (τ : ℝ)) :
    (dirTube σ v hv i).toConvexSpaceBody ≤ (dirTube τ v hv j).toConvexSpaceBody := by
  refine Tube.tube_carrier_subset_of_close (dirTube σ v hv i) (dirTube τ v hv j)
    (ε_dir := ε) (ε_pos := 0) ?_ ?_ ?_
  · simpa using hd
  · have h0 : (dirTube σ v hv i).midpoint - (dirTube τ v hv j).midpoint = 0 := by
      show (1/2 : ℝ) • ((0 - (1/2 : ℝ) • v i) + (0 + (1/2 : ℝ) • v i))
          - (1/2 : ℝ) • ((0 - (1/2 : ℝ) • v j) + (0 + (1/2 : ℝ) • v j)) = 0
      module
    rw [h0, norm_zero]
  · linarith

/-- Iterated retraction along the levels of the grid: `netIter r N m` is
`r (N - m) ∘ ⋯ ∘ r (N - 1)`. -/
def netIter {ι : Type*} (r : ℕ → ι → ι) (N : ℕ) : ℕ → ι → ι
  | 0 => id
  | (m + 1) => r (N - (m + 1)) ∘ netIter r N m

/-- The level-`k` assignment of the angular hierarchy built from the retractions `r`. -/
def angAssign {ι : Type*} (r : ℕ → ι → ι) (N k : ℕ) : ι → ι := netIter r N (N - k)

lemma angAssign_top {ι : Type*} (r : ℕ → ι → ι) (N : ℕ) : angAssign r N N = id := by
  simp [angAssign, netIter]

lemma angAssign_succ {ι : Type*} (r : ℕ → ι → ι) {N k : ℕ} (hk : k < N) :
    angAssign r N k = r k ∘ angAssign r N (k + 1) := by
  have h1 : N - k = (N - (k + 1)) + 1 := by omega
  have h2 : N - ((N - (k + 1)) + 1) = k := by omega
  simp only [angAssign, h1, netIter, h2]


section Construction

variable {ι : Type*} [DecidableEq ι]

/-- **Existence of the angular hierarchy** at the grid of length `N` over the scale `σ`.

The nodes at the index `k` are the `σ_k`-tubes through the origin in the directions of a maximal
`σ_k/8`-separated subset of the directions of `s`, and the assignment is the composite of the
retractions from the bottom of the grid up to the index `k`, so the classes are nested by
construction.  The side conclusions are what the counting arguments consume: the assignment stays
inside `s`, it moves a direction by at most `σ_k/4`, and — above the bottom of the grid, where the
assignment is the identity for want of room — distinct nodes have `σ_k/8`-separated directions. -/
theorem exists_angularCover (s : Finset ι) (v : ι → E) (hv : ∀ i, ‖v i‖ = 1)
    {σ : NNReal} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {N : ℕ} (hN : 0 < N)
    (hσN : σ ≤ (16 : NNReal) ^ (-(N : ℝ))) :
    ∃ 𝒢 : Tube.GridCoverSystem s (dirTube σ v hv) N,
      (∀ k, ∀ i ∈ s, 𝒢.assign k i ∈ s) ∧
      (∀ k ≤ N, ∀ i ∈ s, ‖v i - v (𝒢.assign k i)‖ ≤ (Tube.gridScale σ N k : ℝ) / 4) ∧
      (∀ k < N, ∀ a ∈ 𝒢.indexSet k, ∀ b ∈ 𝒢.indexSet k, a ≠ b →
        (Tube.gridScale σ N k : ℝ) / 8 ≤ ‖v a - v b‖) ∧
      (∀ k, 𝒢.indexSet k = s.image (𝒢.assign k)) := by
  classical
  set ρ : ℕ → ℝ := fun k => (Tube.gridScale σ N k : ℝ) with hρdef
  have hρeq : ∀ k, (Tube.gridScale σ N k : ℝ) = ρ k := fun k => by rw [hρdef]
  have hρpos : ∀ k, 0 < ρ k := fun k => by
    simpa [hρdef] using (NNReal.coe_pos.mpr (Tube.gridScale_pos hσ N k))
  have hstep : ∀ k < N, 16 * ρ (k + 1) ≤ ρ k := by
    intro k hk
    have h := Tube.sixteen_mul_gridScale_succ_le hσ hσN hk
    have h' := NNReal.coe_le_coe.mpr h
    push_cast at h'
    simpa [hρdef] using h'
  have hσρ : ∀ k < N, 8 * (σ : ℝ) ≤ ρ k := by
    intro k hk
    have h := Tube.eight_delta_le_gridScale hσ hσ1 hk hσN
    have h' := NNReal.coe_le_coe.mpr h
    push_cast at h'
    simpa [hρdef] using h'
  -- the retraction data at every level
  have hnet : ∀ k : ℕ, ∃ P : Finset ι, P ⊆ s ∧
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → ρ k / 8 ≤ ‖v a - v b‖) ∧
      (∀ i ∈ s, ∃ w ∈ P, ‖v i - v w‖ < ρ k / 8) := by
    intro k
    have hpos : (0 : ℝ) < ρ k / 8 := by have := hρpos k; linarith
    obtain ⟨P, hPs, hPsep, hPcov⟩ :=
      exists_maximal_separated_finset (ε := ρ k / 8) s (fun a b => ‖v a - v b‖)
        (fun a => by simpa using hpos) (fun a b => norm_sub_rev _ _)
    exact ⟨P, hPs, hPsep, hPcov⟩
  choose Pn hPnsub hPnsep hPncov using hnet
  have hr : ∀ (k : ℕ) (i : ι), ∃ w : ι,
      (i ∈ s → w ∈ Pn k ∧ ‖v i - v w‖ < ρ k / 8) := by
    intro k i
    by_cases hi : i ∈ s
    · obtain ⟨w, hw, hwd⟩ := hPncov k i hi
      exact ⟨w, fun _ => ⟨hw, hwd⟩⟩
    · exact ⟨i, fun h => absurd h hi⟩
  choose r hrspec using hr
  have hnetIter_succ : ∀ (m : ℕ) (i : ι),
      netIter r N (m + 1) i = r (N - (m + 1)) (netIter r N m i) := fun _ _ => rfl
  -- the iterated retraction stays inside `s`
  have hiter_mem : ∀ (m : ℕ), ∀ i ∈ s, netIter r N m i ∈ s := by
    intro m
    induction m with
    | zero => intro i hi; simpa [netIter] using hi
    | succ m ih =>
        intro i hi
        have h1 : netIter r N m i ∈ s := ih i hi
        rw [hnetIter_succ]
        exact hPnsub _ ((hrspec (N - (m + 1)) (netIter r N m i) h1).1)
  have hassign_mem : ∀ k, ∀ i ∈ s, angAssign r N k i ∈ s := fun k i hi => hiter_mem (N - k) i hi
  -- the iterated retraction moves a direction by at most `ρ k / 4`
  have hiter_dist : ∀ (m : ℕ), m ≤ N → ∀ i ∈ s,
      ‖v i - v (netIter r N m i)‖ ≤ ρ (N - m) / 4 := by
    intro m
    induction m with
    | zero =>
        intro _ i _
        have h0 : netIter r N 0 i = i := rfl
        rw [h0, sub_self, norm_zero]
        have := hρpos (N - 0); linarith
    | succ m ih =>
        intro hm1 i hi
        have hkN : N - (m + 1) < N := by omega
        have hNm : N - m = (N - (m + 1)) + 1 := by omega
        have h1 : ‖v i - v (netIter r N m i)‖ ≤ ρ ((N - (m + 1)) + 1) / 4 := by
          have h := ih (by omega) i hi
          rwa [hNm] at h
        have hmem : netIter r N m i ∈ s := hiter_mem m i hi
        have h2 : ‖v (netIter r N m i) - v (r (N - (m + 1)) (netIter r N m i))‖
            < ρ (N - (m + 1)) / 8 := (hrspec (N - (m + 1)) (netIter r N m i) hmem).2
        have h3 := hstep _ hkN
        have h4 := hρpos ((N - (m + 1)) + 1)
        rw [hnetIter_succ]
        calc ‖v i - v (r (N - (m + 1)) (netIter r N m i))‖
            ≤ ‖v i - v (netIter r N m i)‖
              + ‖v (netIter r N m i) - v (r (N - (m + 1)) (netIter r N m i))‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ρ (N - (m + 1)) / 4 := by linarith
  have hassign_dist : ∀ k ≤ N, ∀ i ∈ s, ‖v i - v (angAssign r N k i)‖ ≤ ρ k / 4 := by
    intro k hk i hi
    have h := hiter_dist (N - k) (by omega) i hi
    rwa [show N - (N - k) = k by omega] at h
  have hassign_succ : ∀ k < N, ∀ i, angAssign r N k i = r k (angAssign r N (k + 1) i) := by
    intro k hk i
    rw [angAssign_succ r hk]
    rfl
  have hindex_mem : ∀ k < N, ∀ a ∈ s.image (angAssign r N k), a ∈ Pn k := by
    intro k hk a ha
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    rw [hassign_succ k hk a']
    exact (hrspec k (angAssign r N (k + 1) a') (hassign_mem (k + 1) a' ha')).1
  refine ⟨{ indexSet := fun k => s.image (angAssign r N k)
            assign := angAssign r N
            tube := fun k j => dirTube (Tube.gridScale σ N k) v hv j
            assign_mem := by
              intro k _ i hi
              exact Finset.mem_image_of_mem _ hi
            le_tube_assign := by
              intro k hk i hi
              by_cases hkN : k < N
              · refine dirTube_le_dirTube v hv (ε := ρ k / 4) (hassign_dist k hk i hi) ?_
                simp only [hρeq]
                have h1 := hσρ k hkN
                have h2 := hρpos k
                linarith
              · have hkeq : k = N := le_antisymm hk (not_lt.mp hkN)
                have hid : angAssign r N k i = i := by rw [hkeq, angAssign_top]; rfl
                rw [hid]
                refine dirTube_le_dirTube v hv (ε := 0) (by simp) ?_
                have hgs : (Tube.gridScale σ N k : ℝ) = (σ : ℝ) := by
                  rw [hkeq, Tube.gridScale_self σ hN]
                rw [hgs]
                norm_num
            nested := by
              intro k hk1 i _ j _ hij
              rw [hassign_succ k (by omega), hassign_succ k (by omega), hij]
            tube_nested := by
              intro k hk1 i hi
              have hkN : k < N := by omega
              have hmem : angAssign r N (k + 1) i ∈ s := hassign_mem (k + 1) i hi
              have hd : ‖v (angAssign r N (k + 1) i) - v (angAssign r N k i)‖ ≤ ρ k / 8 := by
                rw [hassign_succ k hkN i]
                exact le_of_lt (hrspec k _ hmem).2
              refine dirTube_le_dirTube v hv (ε := ρ k / 8) hd ?_
              simp only [hρeq]
              have h3 := hstep k hkN
              have h4 := hρpos (k + 1)
              linarith },
    hassign_mem, ?_, ?_, fun k => rfl⟩
  · intro k hk i hi
    simpa [hρdef] using hassign_dist k hk i hi
  · intro k hk a ha b hb hab
    have := hPnsep k a (hindex_mem k hk a ha) b (hindex_mem k hk b hb) hab
    simpa [hρdef] using this

end Construction


section Counting

variable {ι : Type*} [DecidableEq ι]

/-- **A separated set of directions in a ball is small.**  The `Finset` form of the packing
bound `Kakeya.finite_and_card_le_of_separated`, read through a direction map `v` that the
separation hypothesis makes injective. -/
theorem card_le_of_sep_ball (v : ι → E) (H : Finset ι) {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ H, ∀ y ∈ H, x ≠ y → ε ≤ ‖v x - v y‖) {u : E}
    (hball : ∀ j ∈ H, ‖v j - u‖ < R) :
    (H.card : ℝ) ≤ (1 + 2 * R / ε) ^ (Module.finrank ℝ E) := by
  classical
  have hinj : Set.InjOn v (H : Set ι) := by
    intro x hx y hy hxy
    by_contra hne
    have := hsep x hx y hy hne
    rw [hxy, sub_self, norm_zero] at this
    linarith
  have hsub : (v '' (H : Set ι)) ⊆ Metric.ball u R := by
    rintro _ ⟨j, hj, rfl⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hball j hj
  have hsep' : ∀ y ∈ (v '' (H : Set ι)), ∀ z ∈ (v '' (H : Set ι)), y ≠ z → ε ≤ dist y z := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    have hxy : x ≠ y := fun h => hne (by rw [h])
    simpa [dist_eq_norm] using hsep x hx y hy hxy
  have hcard := (Kakeya.finite_and_card_le_of_separated hε hR u hsep' hsub).2
  rwa [hinj.ncard_image, Set.ncard_coe_finset] at hcard

/-- **Counting the angular cells met by a family whose directions lie in one directional ball.**

If every member of `F` has direction within `R` of `w` or of `-w`, if the assignment moves a
direction by at most `d`, and if distinct assigned nodes have `ε`-separated directions, then `F`
meets at most `2 (1 + 2(R + d + ε)/ε)^n` nodes.  This is the only counting input of blueprint
`lem:ml2murho` beyond the shading pigeonhole, and it is pure packing: no tube enters. -/
theorem card_image_le_of_ball (v : ι → E) (F : Finset ι) (a : ι → ι)
    {ε d R : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ F.image a, ∀ y ∈ F.image a, x ≠ y → ε ≤ ‖v x - v y‖)
    (hdist : ∀ i ∈ F, ‖v i - v (a i)‖ ≤ d)
    {w : E} (hball : ∀ i ∈ F, ‖v i - w‖ ≤ R ∨ ‖v i + w‖ ≤ R) :
    ((F.image a).card : ℝ) ≤ 2 * (1 + 2 * (R + d + ε) / ε) ^ (Module.finrank ℝ E) := by
  classical
  set G : Finset ι := F.image a with hG
  set R' : ℝ := R + d + ε with hR'def
  have hR' : 0 ≤ R' := by simp only [hR'def]; linarith
  have hcls : ∀ j ∈ G, ‖v j - w‖ < R' ∨ ‖v j - (-w)‖ < R' := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hstep : ‖v (a i) - v i‖ ≤ d := by rw [norm_sub_rev]; exact hdist i hi
    rcases hball i hi with h | h
    · left
      calc ‖v (a i) - w‖ ≤ ‖v (a i) - v i‖ + ‖v i - w‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < R' := by simp only [hR'def]; linarith
    · right
      have h' : ‖v i - (-w)‖ ≤ R := by simpa [sub_neg_eq_add] using h
      calc ‖v (a i) - (-w)‖ ≤ ‖v (a i) - v i‖ + ‖v i - (-w)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < R' := by simp only [hR'def]; linarith
  set Gp : Finset ι := G.filter (fun j => ‖v j - w‖ < R') with hGp
  set Gm : Finset ι := G.filter (fun j => ‖v j - (-w)‖ < R') with hGm
  have hGsub : G ⊆ Gp ∪ Gm := by
    intro j hj
    rcases hcls j hj with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, h⟩)
  have hbnd : ∀ (u : E) (H : Finset ι), H ⊆ G → (∀ j ∈ H, ‖v j - u‖ < R') →
      (H.card : ℝ) ≤ (1 + 2 * R' / ε) ^ (Module.finrank ℝ E) := by
    intro u H hHG hHball
    exact card_le_of_sep_ball v H hε hR'
      (fun x hx y hy hxy => hsep x (hHG hx) y (hHG hy) hxy) hHball
  have hplus : (Gp.card : ℝ) ≤ (1 + 2 * R' / ε) ^ (Module.finrank ℝ E) :=
    hbnd w Gp (Finset.filter_subset _ _) (fun j hj => (Finset.mem_filter.mp hj).2)
  have hminus : (Gm.card : ℝ) ≤ (1 + 2 * R' / ε) ^ (Module.finrank ℝ E) :=
    hbnd (-w) Gm (Finset.filter_subset _ _) (fun j hj => (Finset.mem_filter.mp hj).2)
  have hle : (G.card : ℝ) ≤ (Gp.card : ℝ) + (Gm.card : ℝ) := by
    have h1 : G.card ≤ (Gp ∪ Gm).card := Finset.card_le_card hGsub
    have h2 : (Gp ∪ Gm).card ≤ Gp.card + Gm.card := Finset.card_union_le _ _
    exact_mod_cast le_trans h1 h2
  calc (G.card : ℝ) ≤ (Gp.card : ℝ) + (Gm.card : ℝ) := hle
    _ ≤ (1 + 2 * R' / ε) ^ (Module.finrank ℝ E) + (1 + 2 * R' / ε) ^ (Module.finrank ℝ E) := by
        linarith
    _ = 2 * (1 + 2 * (R + d + ε) / ε) ^ (Module.finrank ℝ E) := by rw [hR'def]; ring

/-- **Counting a family that lives in one directional ball, through its cells.**

A family `F` whose directions all lie within `R` of `w` (or of `-w`) meets at most
`2 (1 + 2(R+d+ε)/ε)^n` cells of the assignment `a`, by `Kakeya.AngularCover.card_image_le_of_ball`;
if in addition every member lies in a cell `Cls (a i)` of size at most `B`, then `F` itself has at
most that many members times `B`.

This is the upper half of the angular multiplicity estimate of blueprint `lem:ml2murho`: `Cls` is
instantiated at the shade class `ShadedTube.shadeClass` of the balanced refinement, whose size is
pinned to a dyadic band, and `F` at the angular fibre. -/
theorem card_le_of_ball_of_class_bound (v : ι → E) (F : Finset ι) (a : ι → ι)
    {ε d R B : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) (hR : 0 ≤ R) (hBnn : 0 ≤ B)
    (hsep : ∀ x ∈ F.image a, ∀ y ∈ F.image a, x ≠ y → ε ≤ ‖v x - v y‖)
    (hdist : ∀ i ∈ F, ‖v i - v (a i)‖ ≤ d)
    {w : E} (hball : ∀ i ∈ F, ‖v i - w‖ ≤ R ∨ ‖v i + w‖ ≤ R)
    (Cls : ι → Finset ι) (hcover : ∀ i ∈ F, i ∈ Cls (a i))
    (hB : ∀ i ∈ F, ((Cls (a i)).card : ℝ) ≤ B) :
    (F.card : ℝ) ≤ 2 * (1 + 2 * (R + d + ε) / ε) ^ (Module.finrank ℝ E) * B := by
  classical
  set G : Finset ι := F.image a with hG
  have hsub : F ⊆ G.biUnion Cls := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨a i, Finset.mem_image_of_mem _ hi, hcover i hi⟩
  have hcard₁ : (F.card : ℝ) ≤ ∑ P ∈ G, ((Cls P).card : ℝ) := by
    have h₁ : F.card ≤ ∑ P ∈ G, (Cls P).card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
    exact_mod_cast h₁
  have hcard₂ : ∑ P ∈ G, ((Cls P).card : ℝ) ≤ (G.card : ℝ) * B := by
    have hle : ∀ P ∈ G, ((Cls P).card : ℝ) ≤ B := by
      intro P hP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
      exact hB i hi
    calc ∑ P ∈ G, ((Cls P).card : ℝ) ≤ ∑ _P ∈ G, B := Finset.sum_le_sum hle
      _ = (G.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
  have himg : (G.card : ℝ) ≤ 2 * (1 + 2 * (R + d + ε) / ε) ^ (Module.finrank ℝ E) :=
    card_image_le_of_ball v F a hε hd hR hsep hdist hball
  calc (F.card : ℝ) ≤ (G.card : ℝ) * B := hcard₁.trans hcard₂
    _ ≤ 2 * (1 + 2 * (R + d + ε) / ε) ^ (Module.finrank ℝ E) * B :=
        mul_le_mul_of_nonneg_right himg hBnn

end Counting

section Arithmetic

/-! ### The scalar losses of `lem:ml2murho`

Three purely numerical facts, kept here because
`Kakeya.VeryNotSticky.exists_angularMultiplicity` is their only consumer and because they fix
the two constants that make its statement non-vacuous: the refinement constant `c ≥ δ^η`, which
is the reciprocal of the two-stage pigeonhole loss `(⌊log₂|𝕋|⌋+1)^{2N+2}`, and the comparison
constant `C ≤ δ^{-η}`, which is `97336 · δ^{-6/N}` — the packing constant of one angular grid
step in `ℝ³` times the ratio of two consecutive grid scales, cubed. Both are subpolynomial only
below a threshold on `δ` determined by `η` alone, which is what these lemmas produce. -/

/-- **Extract an explicit threshold from an eventually-statement on `𝓝[>] 0`.**

A copy of `Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT`, repeated here rather
than imported so that the angular machinery of blueprint `lem:ml2murho` does not put
`Kakeya.Sticky` — and with it the only axiom of the development — on the import path of
`Kakeya.DimensionThree.MainLemma2.NonSlabAngle`.  The enlarged instance environment is not free
either: two `finrank`-folded definitions of
`Kakeya.DimensionThree.MainLemma2.ThinConfig` sit on the edge of their heartbeat budget and are
pushed over it by that import. -/
private lemma exists_threshold_of_eventually {p : NNReal → Prop}
    (h : ∀ᶠ δ : NNReal in nhdsWithin (0 : NNReal) (Set.Ioi 0), p δ) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → p δ := by
  rw [Filter.eventually_iff, mem_nhdsWithin] at h
  obtain ⟨U, hU_open, hU_mem0, hU_sub⟩ := h
  obtain ⟨t, ht_pos, ht_sub⟩ := nhds_bot_basis.mem_iff.mp (hU_open.mem_nhds hU_mem0)
  refine ⟨t / 2, div_pos ht_pos (by norm_num), fun δ hδ_pos hδ_le => ?_⟩
  have hδ_lt : δ < t := lt_of_le_of_lt hδ_le (div_lt_self ht_pos (by norm_num))
  exact hU_sub ⟨ht_sub hδ_lt, hδ_pos⟩

/-- **A fixed positive constant is subpolynomial, in threshold form.**  The `∃ δ₀` reading of
`Kakeya.absorb_const_le_rpow_neg`. -/
lemma exists_const_threshold {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → C ≤ (δ : ℝ) ^ (-η) :=
  exists_threshold_of_eventually
    (Kakeya.nnreal_eventually_of_real_eventually (Kakeya.absorb_const_le_rpow_neg hC hη))

/-- **Polylogarithmic pigeonhole losses are subpolynomial, in threshold form.**

If a cardinality `nn` is at most `δ^{-m}`, then the dyadic-band count `⌊log₂ nn⌋ + 1` raised to
any fixed power `p` is at most `δ^{-η}` once `δ` is small enough — with a threshold that depends
only on `η`, `m` and `p`, all of which are fixed before `δ`.  This is the arithmetic that pays
for the two pigeonhole stages of `ShadedTube.exists_balanced_shadeRefinement_of_cover`. -/
lemma exists_polylog_threshold {η m : ℝ} (hη : 0 < η) (hm : 0 < m) (p : ℕ) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ →
      ∀ nn : ℕ, (nn : ℝ) ≤ (δ : ℝ) ^ (-m) →
        (((Nat.log 2 nn : ℕ) + 1 : ℕ) : ℝ) ^ p ≤ (δ : ℝ) ^ (-η) := by
  have hη2 : (0 : ℝ) < η / 2 := by linarith
  have hev1 : ∀ᶠ δ : NNReal in nhdsWithin (0 : NNReal) (Set.Ioi 0),
      ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) ^ p ≤ (δ : ENNReal) ^ (-(η / 2)) :=
    ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg hη2 p
  have hev2 : ∀ᶠ δ : NNReal in nhdsWithin (0 : NNReal) (Set.Ioi 0),
      ((1 + m) ^ p : ℝ) ≤ (δ : ℝ) ^ (-(η / 2)) :=
    Kakeya.nnreal_eventually_of_real_eventually
      (Kakeya.absorb_const_le_rpow_neg (by positivity) hη2)
  have hev3 : ∀ᶠ δ : NNReal in nhdsWithin (0 : NNReal) (Set.Ioi 0), (δ : ℝ) ≤ 1 / 2 := by
    have h : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ ≤ 1 / 2 :=
      Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1/2))
        (fun x hx => le_of_lt hx.2)
    exact Kakeya.nnreal_eventually_of_real_eventually h
  have hev0 : ∀ᶠ δ : NNReal in nhdsWithin (0 : NNReal) (Set.Ioi 0), (0 : NNReal) < δ :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun _ hx => hx)
  refine exists_threshold_of_eventually ?_
  filter_upwards [hev1, hev2, hev3, hev0] with δ h1 h2 h3 hδpos
  intro nn hnn
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hδr1 : (δ : ℝ) ≤ 1 := le_trans h3 (by norm_num)
  set L : ℝ := Real.logb 2 (1 / (δ : ℝ)) with hLdef
  have hLone : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have h2le : (2 : ℝ) ≤ 1 / (δ : ℝ) := by
      rw [le_div_iff₀ hδr]; linarith
    calc (1 : ℝ) = Real.logb 2 2 := by simp
      _ ≤ Real.logb 2 (1 / (δ : ℝ)) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2le
  have hpoly : (1 + L) ^ p ≤ (δ : ℝ) ^ (-(η / 2)) := by
    have hbase : (0 : ℝ) ≤ 1 + L := by linarith
    have hrhs : (0 : ℝ) ≤ (δ : ℝ) ^ (-(η / 2)) := Real.rpow_nonneg hδr.le _
    have h1' : ENNReal.ofReal ((1 + L) ^ p) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(η / 2))) := by
      rw [ENNReal.ofReal_pow hbase, ← Kakeya.ennreal_coe_nnreal_rpow hδr]
      exact h1
    exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp h1'
  have hlog : ((Nat.log 2 nn : ℕ) : ℝ) ≤ m * L := by
    rcases Nat.eq_zero_or_pos nn with rfl | hnn0
    · simp; positivity
    · have hnnR : (0 : ℝ) < (nn : ℝ) := by exact_mod_cast hnn0
      have hpow : (2 : ℕ) ^ (Nat.log 2 nn) ≤ nn := Nat.pow_log_le_self 2 hnn0.ne'
      have hpowR : (2 : ℝ) ^ (Nat.log 2 nn) ≤ (nn : ℝ) := by exact_mod_cast hpow
      have hstep : ((Nat.log 2 nn : ℕ) : ℝ) ≤ Real.logb 2 (nn : ℝ) := by
        have hstep0 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hpowR
        rw [Real.logb_pow] at hstep0
        rwa [Real.logb_self_eq_one (b := 2) (by norm_num), mul_one] at hstep0
      have hlast : Real.logb 2 (nn : ℝ) ≤ m * L := by
        refine le_trans (Real.logb_le_logb_of_le (by norm_num) hnnR hnn) ?_
        rw [hLdef, Real.logb, Real.logb, Real.log_rpow hδr, Real.log_div one_ne_zero hδr.ne']
        rw [Real.log_one]
        have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        field_simp
        linarith
      exact hstep.trans hlast
  have hsum : (((Nat.log 2 nn : ℕ) + 1 : ℕ) : ℝ) ≤ (1 + m) * (1 + L) := by
    push_cast
    nlinarith [hm.le, hLone]
  calc (((Nat.log 2 nn : ℕ) + 1 : ℕ) : ℝ) ^ p
      ≤ ((1 + m) * (1 + L)) ^ p := by
        apply pow_le_pow_left₀ (by positivity) hsum
    _ = (1 + m) ^ p * (1 + L) ^ p := by rw [mul_pow]
    _ ≤ (δ : ℝ) ^ (-(η / 2)) * (δ : ℝ) ^ (-(η / 2)) :=
        mul_le_mul h2 hpoly (by positivity) (Real.rpow_nonneg hδr.le _)
    _ = (δ : ℝ) ^ (-η) := by
        rw [← Real.rpow_add hδr]; ring_nf

/-- `ℝ≥0∞`-input form of `Kakeya.AngularCover.exists_polylog_threshold`: the cardinality bound
arrives as `|𝕋| ≤ K · δ^{-m}` in `ℝ≥0∞`, which is how `Kakeya.Tube.card_le_of_densityIn_le`
states it. -/
lemma exists_polylog_threshold_ennreal {η m : ℝ} (hη : 0 < η) (hm : 0 < m) (p : ℕ) (K : NNReal) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ →
      ∀ nn : ℕ, (nn : ENNReal) ≤ (K : ENNReal) * (δ : ENNReal) ^ (-m) →
        (((Nat.log 2 nn + 1 : ℕ) : NNReal)) ^ p ≤ δ ^ (-η) := by
  obtain ⟨δa, hδa, ha⟩ := exists_polylog_threshold hη (m := m + 1) (by linarith) p
  obtain ⟨δb, hδb, hb⟩ := exists_const_threshold (C := (K : ℝ) + 1) (by positivity)
    (show (0:ℝ) < 1 by norm_num)
  refine ⟨min δa δb, lt_min hδa hδb, ?_⟩
  intro δ hδ hδle nn hnn
  have hδr : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ
  have hKle : (K:ℝ) ≤ (δ:ℝ) ^ (-(1:ℝ)) := by
    have h := hb δ hδ (le_trans hδle (min_le_right _ _))
    linarith
  have hreal : (nn : ℝ) ≤ (K:ℝ) * (δ:ℝ) ^ (-m) := by
    rw [Kakeya.ennreal_coe_nnreal_rpow hδr, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul K.coe_nonneg] at hnn
    have hnn' : ENNReal.ofReal (nn : ℝ) ≤ ENNReal.ofReal ((K:ℝ) * (δ:ℝ) ^ (-m)) := by
      simpa using hnn
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hnn'
  have hreal2 : (nn : ℝ) ≤ (δ:ℝ) ^ (-(m+1)) := by
    calc (nn : ℝ) ≤ (K:ℝ) * (δ:ℝ) ^ (-m) := hreal
      _ ≤ (δ:ℝ) ^ (-(1:ℝ)) * (δ:ℝ) ^ (-m) :=
          mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hδr.le _)
      _ = (δ:ℝ) ^ (-(m+1)) := by rw [← Real.rpow_add hδr]; ring_nf
  have hmain := ha δ hδ (le_trans hδle (min_le_left _ _)) nn hreal2
  rw [← NNReal.coe_le_coe]
  push_cast
  push_cast at hmain
  exact hmain

/-- **The scalar half of the upper bound of `lem:ml2murho`.**

The packing bound of `Kakeya.AngularCover.card_le_of_ball_of_class_bound`, read at the angular
scale `rk` with separation `rk/8`, assignment displacement `rk/4` and radius `ρ ≤ q · rk`, is at
most `97336 q³` times the dyadic band `B`.  The numeral is `2 · 23³ · 4`: two hemispheres, the
packing exponent `3 = dim ℝ³`, and the factor `4` of the dyadic band. -/
lemma murho_packing_arith {ρ rk q B : ℝ} (hρ : 0 < ρ) (hr : 0 < rk) (hq : 1 ≤ q)
    (hd : ρ ≤ q * rk) (hB : 0 ≤ B) :
    2 * (1 + 2 * (ρ + rk / 4 + rk / 8) / (rk / 8)) ^ 3 * (4 * B) ≤ 97336 * q ^ 3 * B := by
  have hexp : 1 + 2 * (ρ + rk / 4 + rk / 8) / (rk / 8) = 7 + 16 * (ρ / rk) := by
    field_simp; ring
  have hdq : ρ / rk ≤ q := by rw [div_le_iff₀ hr]; linarith
  have hnn : (0:ℝ) ≤ 7 + 16 * (ρ / rk) := by
    have h0 : (0:ℝ) ≤ ρ / rk := div_nonneg hρ.le hr.le
    linarith
  have hkey : 7 + 16 * (ρ / rk) ≤ 23 * q := by linarith
  have hcube : (7 + 16 * (ρ / rk)) ^ 3 ≤ (23 * q) ^ 3 := pow_le_pow_left₀ hnn hkey 3
  rw [hexp]
  calc 2 * (7 + 16 * (ρ / rk)) ^ 3 * (4 * B)
      = 8 * ((7 + 16 * (ρ / rk)) ^ 3) * B := by ring
    _ ≤ 8 * ((23 * q) ^ 3) * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by norm_num)) hB
    _ = 97336 * q ^ 3 * B := by ring

end Arithmetic

end Kakeya.AngularCover
