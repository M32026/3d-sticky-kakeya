/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBack
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreAssembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze

/-!
# The centring preparation: `lemcanonicalcover` at set level, the anisotropic map at `ρ = 1`,
and the cardinality half of the centred ledger

Source of record: the professor's refined proof
`260115_kakeyadetailedproofv3_revised_detailed.tex`

## Geometric containment

Under a centred Lemma 9.1 the site's equality binder
`hU : ∀ i, (U' i).toTube = (outerFamily … i).toTube` is unsatisfiable, and — this is the
obstruction — so is the containment `outerFamily … i ≤ U' i` against a **centred** `U' i` at the
same radius: two unit cores at one radius pin the axial parameter, so a centred container is
centred to within `6δ` of what it contains (`Kakeya.CentringObstruction`, §3 below).  The source
does not ask for that containment.  It composes (l.6003–6005)

> "Choose a fixed exact unit tube containing `B₁` and apply the anisotropic map with `ρ = 1`,
> **followed by** the canonical cover in Lemma `lemcanonicalcover`."

and `lemcanonicalcover` (l.4774–4800) takes **sets** — `X_i ⊂ B̄(0,2/5)` nonempty, each inside the
`r`-neighbourhood of a line — not tubes.  That set-level statement is what the tree lacked: the
existing/patched `Kakeya.Tube.exists_canonicalCentredCover` requires its *input* to be centred
(`hcen`), so it is the tower device of U1 and cannot centre anything.

## Main declarations

* `Kakeya.VeryNotSticky.exists_setCanonicalCentredCover` — **`lemcanonicalcover`, set level**:
  the refined hypotheses verbatim, output centred exact `ρ`-tubes at line tolerance `ρ/4`, with
  the all-used clause, the parameter bound `2/5 + ρ/4` (the source's `|p| ≤ 0.42`) and line-based
  essential distinctness at the absolute `Kakeya.Tube.canonicalCoverEDConstant`.
* `Kakeya.VeryNotSticky.centringDilate` and its two image lemmas — the anisotropic map
  `eqanisotropicmap` (l.4765–4772) **at `ρ = 1`**, where it collapses to the similarity
  `x ↦ x/8`.
* `Kakeya.VeryNotSticky.exists_centredRepresentatives` — the composite, with the radius
  bookkeeping chosen so the representatives live at the **same** radius as the input.
* `Kakeya.VeryNotSticky.fibre_card_le_of_lineEDAt` and
  `Kakeya.VeryNotSticky.card_le_of_centredRepresentatives` — the **cardinality half of
  `eq:defect-centred-ledger`** (l.6014, `F₁^{-1} #𝔾 ≤ #𝔾^ ≤ #𝔾`), at `F₁ := A` when the input
  family is line-essentially distinct at radius `8δ`.

The three remaining ledger clauses of l.6017–6023 (`μ`, `λ`, `Δ_max`) need a shading on the
representative family and the measure-theoretic half of `lemaffineinvariance`; they are **not**
in this leaf and are sized 
-/

@[expose] public section

-- RELOCATED to `Reduction/SpineCentredHandBack.lean` (imported above): the anisotropic map
-- at `ρ = 1` (`centringDilate`, `normalise`) and the two Props of ′
-- (`CentredHandBack`, `CountTransport`).  They must sit BELOW `SpineCoreAssembly`, which
-- names `CentredHandBack` in a binder, and this leaf imports `SpineCoreAssembly`.


open MeasureTheory Metric RealInnerProductSpace
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-! ### Normalising a line to its perpendicular foot -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- Re-basing a line at the foot of the perpendicular from the origin does not change the line. -/
theorem range_line_lineFoot (p d : E) :
    (Set.range fun t : ℝ ↦ Tube.lineFoot p d + t • d)
      = (Set.range fun t : ℝ ↦ p + t • d) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t - ⟪p, d⟫, by unfold Tube.lineFoot; module⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t + ⟪p, d⟫, by unfold Tube.lineFoot; module⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The foot is centred. -/
theorem inner_lineFoot_eq_zero (p d : E) (hd : ‖d‖ = 1) : ⟪Tube.lineFoot p d, d⟫ = (0 : ℝ) := by
  unfold Tube.lineFoot
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hd]
  ring

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- `‖foot‖` is the distance from the origin to the line. -/
theorem lineDist_zero_eq_norm_lineFoot (p d : E) :
    Tube.lineDist p d 0 = ‖Tube.lineFoot p d‖ := by
  unfold Tube.lineDist Tube.lineFoot
  rw [show ((0 : E) - p) = -p from by abel, inner_neg_left, ← norm_neg]
  congr 1
  module

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [ProperSpace E] in
/-- **The foot's norm bound** (refined l.4783: `|p| ≤ 0.42`): if the line carries a point of the
unit-scaled ball `B̄(0,R)` within `r`, its perpendicular foot has norm at most `R + r`. -/
theorem norm_lineFoot_le {p d z : E} (hd : ‖d‖ = 1) {r R : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ Metric.cthickening r (Set.range fun t : ℝ ↦ p + t • d)) (hzn : ‖z‖ ≤ R) :
    ‖Tube.lineFoot p d‖ ≤ R + r := by
  rw [← lineDist_zero_eq_norm_lineFoot]
  have h0 : Tube.lineDist p d 0
      ≤ Tube.lineDist p d z + ‖(0 : E) - z - ⟪(0 : E) - z, d⟫ • d‖ := by
    unfold Tube.lineDist
    have hkey := Tube.perp_sub_perp p d 0 z
    calc ‖((0 : E) - p) - ⟪(0 : E) - p, d⟫ • d‖
        = ‖(((z - p) - ⟪z - p, d⟫ • d))
            + ((((0 : E) - p) - ⟪(0 : E) - p, d⟫ • d) - ((z - p) - ⟪z - p, d⟫ • d))‖ := by abel_nf
      _ ≤ ‖(z - p) - ⟪z - p, d⟫ • d‖
            + ‖(((0 : E) - p) - ⟪(0 : E) - p, d⟫ • d) - ((z - p) - ⟪z - p, d⟫ • d)‖ :=
          norm_add_le _ _
      _ = _ := by rw [hkey]
  have h1 : Tube.lineDist p d z ≤ r := (Tube.mem_cthickening_line_iff hd hr).mp hz
  have h2 : ‖(0 : E) - z - ⟪(0 : E) - z, d⟫ • d‖ ≤ R := by
    have := Tube.lineDist_le_norm_sub (0 : E) d ((0 : E) - z) hd 0
    unfold Tube.lineDist at this
    have h3 : ‖(0 : E) - z‖ ≤ R := by simpa using hzn
    calc ‖(0 : E) - z - ⟪(0 : E) - z, d⟫ • d‖
        = ‖(((0 : E) - z) - (0 : E)) - ⟪((0 : E) - z) - (0 : E), d⟫ • d‖ := by simp
      _ ≤ ‖((0 : E) - z) - ((0 : E) + (0 : ℝ) • d)‖ := this
      _ = ‖(0 : E) - z‖ := by simp
      _ ≤ R := h3
  linarith

/-! ### The one-scale set-level canonical centred cover -/

open Classical in
/-- **`lemcanonicalcover`, set-level** (refined l.4774–4800 verbatim in its hypotheses). -/
theorem exists_setCanonicalCentredCover {ρ : NNReal} (hρ0 : 0 < ρ) (hρ : (ρ : ℝ) ≤ 1 / 20)
    {ι : Type*} (s : Finset ι) (X : ι → Set E) (p d : ι → E)
    (hd : ∀ i ∈ s, ‖d i‖ = 1)
    (hXne : ∀ i ∈ s, (X i).Nonempty)
    (hXball : ∀ i ∈ s, X i ⊆ Metric.closedBall (0 : E) (2 / 5))
    (hXline : ∀ i ∈ s, X i ⊆
      Metric.cthickening ((ρ : ℝ) / 4) (Set.range fun t : ℝ ↦ p i + t • d i)) :
    ∃ (G : Finset (Tube ρ E)) (ϖ : ι → Tube ρ E),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ i ∈ s, X i ⊆ (ϖ i).carrier) ∧
      (∀ W ∈ G, W.IsCentred) ∧
      (∀ W ∈ G, ‖W.midpoint‖ ≤ 2 / 5 + (ρ : ℝ) / 4) ∧
      (∀ o e : E, ‖e‖ = 1 →
        ((G.filter fun W : Tube ρ E ↦ W.carrier ⊆
            Metric.cthickening (5 * (ρ : ℝ)) (Set.range fun t : ℝ ↦ o + t • e)).card : ℝ)
          ≤ Tube.canonicalCoverEDConstant (Module.finrank ℝ E) (2 / 5 + (ρ : ℝ) / 4)) := by
  classical
  have hρr : (0 : ℝ) < (ρ : ℝ) := hρ0
  set r : ℝ := (ρ : ℝ) / 4 with hr_def
  have hr0 : 0 < r := by rw [hr_def]; positivity
  have hr80 : r ≤ 1 / 80 := by rw [hr_def]; linarith
  set R₀ : ℝ := 2 / 5 + r with hR₀
  have hR₀0 : 0 ≤ R₀ := by rw [hR₀]; linarith
  have hR₀half : R₀ ≤ 1 / 2 := by rw [hR₀]; linarith
  obtain ⟨G₀, hG₀cen, hG₀mid, hG₀sep, hG₀cover⟩ :=
    Tube.exists_centred_net (E := E) ρ R₀ (ε := (ρ : ℝ) / 8) (by positivity)
  -- the foot of each line, and its parameters
  have hfoot : ∀ i ∈ s, ⟪Tube.lineFoot (p i) (d i), d i⟫ = (0 : ℝ) :=
    fun i hi ↦ inner_lineFoot_eq_zero _ _ (hd i hi)
  have hfootn : ∀ i ∈ s, ‖Tube.lineFoot (p i) (d i)‖ ≤ R₀ := by
    intro i hi
    obtain ⟨z, hz⟩ := hXne i hi
    have hzn : ‖z‖ ≤ 2 / 5 := by
      simpa using Metric.mem_closedBall.mp (hXball i hi hz)
    exact norm_lineFoot_le (hd i hi) hr0.le (hXline i hi hz) hzn
  -- the assignment
  have hchoice : ∀ i, ∃ W : Tube ρ E, i ∈ s →
      W ∈ G₀ ∧ ‖Tube.lineFoot (p i) (d i) - W.midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) ∧
        ‖d i - W.direction‖ ≤ 2 * ((ρ : ℝ) / 8) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨W, hW, h1, h2⟩ :=
        hG₀cover (Tube.lineFoot (p i) (d i)) (d i) (hfoot i hi) (hd i hi) (hfootn i hi)
      exact ⟨W, fun _ ↦ ⟨hW, h1, h2⟩⟩
    · obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
      exact ⟨Tube.ofMidpointDirection ρ 0 (‖x₀‖⁻¹ • x₀)
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx₀)]),
        fun h ↦ (hi h).elim⟩
  choose ϖ hϖ using hchoice
  set G : Finset (Tube ρ E) := s.image ϖ with hG
  have hGsub : G ⊆ G₀ := by
    intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    exact (hϖ i hi).1
  have hq : 2 * ((ρ : ℝ) / 8) = r := by rw [hr_def]; ring
  refine ⟨G, ϖ, fun i hi ↦ Finset.mem_image_of_mem _ hi, ?_, ?_, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨i, hi, rfl⟩
  -- CONTAINMENT
  · intro i hi z hz
    obtain ⟨-, h1, h2⟩ := hϖ i hi
    rw [hq] at h1 h2
    set f : E := Tube.lineFoot (p i) (d i) with hf
    -- a foot on the line, at parameter τ
    have hzline : z ∈ Metric.cthickening r (Set.range fun t : ℝ ↦ f + t • d i) := by
      rw [range_line_lineFoot]; exact hXline i hi hz
    have hzd : Tube.lineDist f (d i) z ≤ r :=
      (Tube.mem_cthickening_line_iff (hd i hi) hr0.le).mp hzline
    set τ : ℝ := ⟪z - f, d i⟫ with hτ
    have hfoot' : ‖z - (f + τ • d i)‖ ≤ r := by
      rw [hτ, Tube.norm_sub_foot_eq f (d i) z (hd i hi)]
      exact hzd
    have hzn : ‖z‖ ≤ 2 / 5 := by simpa using Metric.mem_closedBall.mp (hXball i hi hz)
    have hτb : |τ| ≤ R₀ := by
      have hip : ⟪f + τ • d i, d i⟫ = τ := by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hd i hi,
          hfoot i hi]
        ring
      have h4 : |τ| ≤ ‖f + τ • d i‖ := by
        calc |τ| = |⟪f + τ • d i, d i⟫| := by rw [hip]
          _ ≤ ‖f + τ • d i‖ * ‖d i‖ := abs_real_inner_le_norm _ _
          _ = ‖f + τ • d i‖ := by rw [hd i hi]; ring
      have h5 : ‖f + τ • d i‖ ≤ ‖z‖ + r := by
        have := hfoot'
        calc ‖f + τ • d i‖ = ‖z - (z - (f + τ • d i))‖ := by abel_nf
          _ ≤ ‖z‖ + ‖z - (f + τ • d i)‖ := norm_sub_le _ _
          _ ≤ ‖z‖ + r := by gcongr
      rw [hR₀]; linarith
    -- the corresponding core point of the node
    have hτhalf : |τ| ≤ 1 / 2 := le_trans hτb hR₀half
    refine (ϖ i).mem_carrier_of_dist_le ((ϖ i).midpoint_add_smul_mem_segment hτhalf) ?_
    rw [dist_eq_norm]
    have hstep : ‖z - ((ϖ i).midpoint + τ • (ϖ i).direction)‖
        ≤ ‖z - (f + τ • d i)‖ + (‖f - (ϖ i).midpoint‖ + |τ| * ‖d i - (ϖ i).direction‖) := by
      calc ‖z - ((ϖ i).midpoint + τ • (ϖ i).direction)‖
          = ‖(z - (f + τ • d i))
              + ((f - (ϖ i).midpoint) + τ • (d i - (ϖ i).direction))‖ := by
            congr 1; module
        _ ≤ ‖z - (f + τ • d i)‖ + ‖(f - (ϖ i).midpoint) + τ • (d i - (ϖ i).direction)‖ :=
            norm_add_le _ _
        _ ≤ ‖z - (f + τ • d i)‖
              + (‖f - (ϖ i).midpoint‖ + ‖τ • (d i - (ϖ i).direction)‖) := by
            gcongr; exact norm_add_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs]
    have hmul : |τ| * ‖d i - (ϖ i).direction‖ ≤ R₀ * r :=
      mul_le_mul hτb h2 (norm_nonneg _) hR₀0
    have hfin : ‖z - ((ϖ i).midpoint + τ • (ϖ i).direction)‖ ≤ r + (r + R₀ * r) := by
      refine hstep.trans ?_
      linarith
    refine hfin.trans ?_
    rw [hr_def, hR₀, hr_def]
    nlinarith [hρr]
  · intro W hW; exact hG₀cen W (hGsub hW)
  · intro W hW; exact hG₀mid W (hGsub hW)
  -- ED count
  · intro o e he
    have h := Tube.card_filter_line_le_of_centred_sep G hρ0 (fun W : Tube ρ E ↦ W)
      (fun W hW ↦ hG₀cen W (hGsub hW)) hR₀0 (fun W hW ↦ hG₀mid W (hGsub hW))
      (m := 8) (by norm_num)
      (fun a ha b hb hab ↦ hG₀sep a (hGsub ha) b (hGsub hb) hab)
      (K := 5) (by norm_num) o e he
    rw [Tube.canonicalCoverEDConstant]
    exact h

open Classical in
/-- **`exists_setCanonicalCentredCover` with the assignment's two `ρ/4` estimates exported.**

Additive sibling;   Both conjuncts are already established
inside that proof — they are `hϖ i hi`'s second and third components, at `2 · (ρ/8) = ρ/4` — but
they are not exported, and a consumer that has to bound the node's fibre needs them: they are what
turns "the member sits in the node" into a triangle estimate against an arbitrary containing tube.
Stated relative to the **member** (`p i`, `d i`), not to the cover tube, so that the consumer's own
containment is what the estimate consumes. -/
theorem exists_setCanonicalCentredCover_data {ρ : NNReal} (hρ0 : 0 < ρ) (hρ : (ρ : ℝ) ≤ 1 / 20)
    {ι : Type*} (s : Finset ι) (X : ι → Set E) (p d : ι → E)
    (hd : ∀ i ∈ s, ‖d i‖ = 1)
    (hXne : ∀ i ∈ s, (X i).Nonempty)
    (hXball : ∀ i ∈ s, X i ⊆ Metric.closedBall (0 : E) (2 / 5))
    (hXline : ∀ i ∈ s, X i ⊆
      Metric.cthickening ((ρ : ℝ) / 4) (Set.range fun t : ℝ ↦ p i + t • d i)) :
    ∃ (G : Finset (Tube ρ E)) (ϖ : ι → Tube ρ E),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ i ∈ s, X i ⊆ (ϖ i).carrier) ∧
      (∀ W ∈ G, W.IsCentred) ∧
      (∀ W ∈ G, ‖W.midpoint‖ ≤ 2 / 5 + (ρ : ℝ) / 4) ∧
      (∀ o e : E, ‖e‖ = 1 →
        ((G.filter fun W : Tube ρ E ↦ W.carrier ⊆
            Metric.cthickening (5 * (ρ : ℝ)) (Set.range fun t : ℝ ↦ o + t • e)).card : ℝ)
          ≤ Tube.canonicalCoverEDConstant (Module.finrank ℝ E) (2 / 5 + (ρ : ℝ) / 4)) ∧
      (∀ i ∈ s, ‖Tube.lineFoot (p i) (d i) - (ϖ i).midpoint‖ ≤ (ρ : ℝ) / 4) ∧
      (∀ i ∈ s, ‖d i - (ϖ i).direction‖ ≤ (ρ : ℝ) / 4) := by
  classical
  have hρr : (0 : ℝ) < (ρ : ℝ) := hρ0
  set r : ℝ := (ρ : ℝ) / 4 with hr_def
  have hr0 : 0 < r := by rw [hr_def]; positivity
  have hr80 : r ≤ 1 / 80 := by rw [hr_def]; linarith
  set R₀ : ℝ := 2 / 5 + r with hR₀
  have hR₀0 : 0 ≤ R₀ := by rw [hR₀]; linarith
  have hR₀half : R₀ ≤ 1 / 2 := by rw [hR₀]; linarith
  obtain ⟨G₀, hG₀cen, hG₀mid, hG₀sep, hG₀cover⟩ :=
    Tube.exists_centred_net (E := E) ρ R₀ (ε := (ρ : ℝ) / 8) (by positivity)
  -- the foot of each line, and its parameters
  have hfoot : ∀ i ∈ s, ⟪Tube.lineFoot (p i) (d i), d i⟫ = (0 : ℝ) :=
    fun i hi ↦ inner_lineFoot_eq_zero _ _ (hd i hi)
  have hfootn : ∀ i ∈ s, ‖Tube.lineFoot (p i) (d i)‖ ≤ R₀ := by
    intro i hi
    obtain ⟨z, hz⟩ := hXne i hi
    have hzn : ‖z‖ ≤ 2 / 5 := by
      simpa using Metric.mem_closedBall.mp (hXball i hi hz)
    exact norm_lineFoot_le (hd i hi) hr0.le (hXline i hi hz) hzn
  -- the assignment
  have hchoice : ∀ i, ∃ W : Tube ρ E, i ∈ s →
      W ∈ G₀ ∧ ‖Tube.lineFoot (p i) (d i) - W.midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) ∧
        ‖d i - W.direction‖ ≤ 2 * ((ρ : ℝ) / 8) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨W, hW, h1, h2⟩ :=
        hG₀cover (Tube.lineFoot (p i) (d i)) (d i) (hfoot i hi) (hd i hi) (hfootn i hi)
      exact ⟨W, fun _ ↦ ⟨hW, h1, h2⟩⟩
    · obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
      exact ⟨Tube.ofMidpointDirection ρ 0 (‖x₀‖⁻¹ • x₀)
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx₀)]),
        fun h ↦ (hi h).elim⟩
  choose ϖ hϖ using hchoice
  set G : Finset (Tube ρ E) := s.image ϖ with hG
  have hGsub : G ⊆ G₀ := by
    intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    exact (hϖ i hi).1
  have hq : 2 * ((ρ : ℝ) / 8) = r := by rw [hr_def]; ring
  refine ⟨G, ϖ, fun i hi ↦ Finset.mem_image_of_mem _ hi, ?_, ?_, ?_, ?_, ?_,
    fun i hi ↦ by rw [← hq]; exact (hϖ i hi).2.1,
    fun i hi ↦ by rw [← hq]; exact (hϖ i hi).2.2⟩
  · intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨i, hi, rfl⟩
  -- CONTAINMENT
  · intro i hi z hz
    obtain ⟨-, h1, h2⟩ := hϖ i hi
    rw [hq] at h1 h2
    set f : E := Tube.lineFoot (p i) (d i) with hf
    -- a foot on the line, at parameter τ
    have hzline : z ∈ Metric.cthickening r (Set.range fun t : ℝ ↦ f + t • d i) := by
      rw [range_line_lineFoot]; exact hXline i hi hz
    have hzd : Tube.lineDist f (d i) z ≤ r :=
      (Tube.mem_cthickening_line_iff (hd i hi) hr0.le).mp hzline
    set τ : ℝ := ⟪z - f, d i⟫ with hτ
    have hfoot' : ‖z - (f + τ • d i)‖ ≤ r := by
      rw [hτ, Tube.norm_sub_foot_eq f (d i) z (hd i hi)]
      exact hzd
    have hzn : ‖z‖ ≤ 2 / 5 := by simpa using Metric.mem_closedBall.mp (hXball i hi hz)
    have hτb : |τ| ≤ R₀ := by
      have hip : ⟪f + τ • d i, d i⟫ = τ := by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hd i hi,
          hfoot i hi]
        ring
      have h4 : |τ| ≤ ‖f + τ • d i‖ := by
        calc |τ| = |⟪f + τ • d i, d i⟫| := by rw [hip]
          _ ≤ ‖f + τ • d i‖ * ‖d i‖ := abs_real_inner_le_norm _ _
          _ = ‖f + τ • d i‖ := by rw [hd i hi]; ring
      have h5 : ‖f + τ • d i‖ ≤ ‖z‖ + r := by
        have := hfoot'
        calc ‖f + τ • d i‖ = ‖z - (z - (f + τ • d i))‖ := by abel_nf
          _ ≤ ‖z‖ + ‖z - (f + τ • d i)‖ := norm_sub_le _ _
          _ ≤ ‖z‖ + r := by gcongr
      rw [hR₀]; linarith
    -- the corresponding core point of the node
    have hτhalf : |τ| ≤ 1 / 2 := le_trans hτb hR₀half
    refine (ϖ i).mem_carrier_of_dist_le ((ϖ i).midpoint_add_smul_mem_segment hτhalf) ?_
    rw [dist_eq_norm]
    have hstep : ‖z - ((ϖ i).midpoint + τ • (ϖ i).direction)‖
        ≤ ‖z - (f + τ • d i)‖ + (‖f - (ϖ i).midpoint‖ + |τ| * ‖d i - (ϖ i).direction‖) := by
      calc ‖z - ((ϖ i).midpoint + τ • (ϖ i).direction)‖
          = ‖(z - (f + τ • d i))
              + ((f - (ϖ i).midpoint) + τ • (d i - (ϖ i).direction))‖ := by
            congr 1; module
        _ ≤ ‖z - (f + τ • d i)‖ + ‖(f - (ϖ i).midpoint) + τ • (d i - (ϖ i).direction)‖ :=
            norm_add_le _ _
        _ ≤ ‖z - (f + τ • d i)‖
              + (‖f - (ϖ i).midpoint‖ + ‖τ • (d i - (ϖ i).direction)‖) := by
            gcongr; exact norm_add_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs]
    have hmul : |τ| * ‖d i - (ϖ i).direction‖ ≤ R₀ * r :=
      mul_le_mul hτb h2 (norm_nonneg _) hR₀0
    have hfin : ‖z - ((ϖ i).midpoint + τ • (ϖ i).direction)‖ ≤ r + (r + R₀ * r) := by
      refine hstep.trans ?_
      linarith
    refine hfin.trans ?_
    rw [hr_def, hR₀, hr_def]
    nlinarith [hρr]
  · intro W hW; exact hG₀cen W (hGsub hW)
  · intro W hW; exact hG₀mid W (hGsub hW)
  -- ED count
  · intro o e he
    have h := Tube.card_filter_line_le_of_centred_sep G hρ0 (fun W : Tube ρ E ↦ W)
      (fun W hW ↦ hG₀cen W (hGsub hW)) hR₀0 (fun W hW ↦ hG₀mid W (hGsub hW))
      (m := 8) (by norm_num)
      (fun a ha b hb hab ↦ hG₀sep a (hGsub ha) b (hGsub hb) hab)
      (K := 5) (by norm_num) o e he
    rw [Tube.canonicalCoverEDConstant]
    exact h

open Classical in
/-- **the `_data` sibling projects onto the existing statement.**  The leading conjuncts are
shared character for character, so they cannot drift apart. -/
theorem exists_setCanonicalCentredCover_of_data {ρ : NNReal} (hρ0 : 0 < ρ) (hρ : (ρ : ℝ) ≤ 1 / 20)
    {ι : Type*} (s : Finset ι) (X : ι → Set E) (p d : ι → E)
    (hd : ∀ i ∈ s, ‖d i‖ = 1)
    (hXne : ∀ i ∈ s, (X i).Nonempty)
    (hXball : ∀ i ∈ s, X i ⊆ Metric.closedBall (0 : E) (2 / 5))
    (hXline : ∀ i ∈ s, X i ⊆
      Metric.cthickening ((ρ : ℝ) / 4) (Set.range fun t : ℝ ↦ p i + t • d i)) :
    ∃ (G : Finset (Tube ρ E)) (ϖ : ι → Tube ρ E),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ i ∈ s, X i ⊆ (ϖ i).carrier) ∧
      (∀ W ∈ G, W.IsCentred) ∧
      (∀ W ∈ G, ‖W.midpoint‖ ≤ 2 / 5 + (ρ : ℝ) / 4) ∧
      (∀ o e : E, ‖e‖ = 1 →
        ((G.filter fun W : Tube ρ E ↦ W.carrier ⊆
            Metric.cthickening (5 * (ρ : ℝ)) (Set.range fun t : ℝ ↦ o + t • e)).card : ℝ)
          ≤ Tube.canonicalCoverEDConstant (Module.finrank ℝ E) (2 / 5 + (ρ : ℝ) / 4)) := by
  obtain ⟨G, ϖ, h1, h2, h3, h4, h5, h6, -, -⟩ :=
    exists_setCanonicalCentredCover_data hρ0 hρ s X p d hd hXne hXball hXline
  exact ⟨G, ϖ, h1, h2, h3, h4, h5, h6⟩

/-! ### The anisotropic map at `ρ = 1`, and the `δ'/4 → δ'` bookkeeping -/

open Classical in
/-- **The centred representatives of a family, at the SAME radius** (refined l.6003–6013).

The composite of the anisotropic map at `ρ = 1` with the set-level canonical cover, with the
radius bookkeeping chosen so that the output radius is exactly the input radius: apply
`exists_setCanonicalCentredCover` at `ρ := δ'`, whose line tolerance is `δ'/4`, to the images,
whose line tolerance is `δ'/8`.  (The source's own bookkeeping produces `d = δ/2`, l.6011, because
it fixes `r = δ/8` and takes `4r`; reading `r = δ'/4` instead costs nothing — the essential
distinctness constant of `lemcanonicalcover` is `r`-free — and it removes the scale shift, so the
representatives can be fed to `Lemma91At` at the *same* `δ'`.)

This is the geometric core of the centring hand-back: an all-used family of **centred** exact
`δ'`-tubes, each containing the dilated original, line-essentially distinct at an absolute
constant. -/
theorem exists_centredRepresentatives {δ' : NNReal} (hδ0 : 0 < δ') (hδ : (δ' : ℝ) ≤ 1 / 20)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ' E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ (G : Finset (Tube δ' E)) (ϖ : ι → Tube δ' E),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ i ∈ s, centringDilate '' (T i).carrier ⊆ (ϖ i).carrier) ∧
      (∀ W ∈ G, W.IsCentred) ∧
      (∀ W ∈ G, ‖W.midpoint‖ ≤ 2 / 5 + (δ' : ℝ) / 4) ∧
      G.card ≤ s.card ∧
      (∀ o e : E, ‖e‖ = 1 →
        ((G.filter fun W : Tube δ' E ↦ W.carrier ⊆
            Metric.cthickening (5 * (δ' : ℝ)) (Set.range fun t : ℝ ↦ o + t • e)).card : ℝ)
          ≤ Tube.canonicalCoverEDConstant (Module.finrank ℝ E) (2 / 5 + (δ' : ℝ) / 4)) := by
  classical
  have hδr : (0 : ℝ) < (δ' : ℝ) := hδ0
  obtain ⟨G, ϖ, hmem, hsurj, hcov, hcen, hmid, hED⟩ :=
    exists_setCanonicalCentredCover (E := E) hδ0 hδ s
      (fun i ↦ centringDilate '' (T i).carrier)
      (fun i ↦ centringDilate (T i).midpoint) (fun i ↦ (T i).direction)
      (fun i _ ↦ (T i).norm_direction)
      (fun i _ ↦ ⟨centringDilate (T i).midpoint,
        ⟨(T i).midpoint, Tube.midpoint_mem_carrier hδ0 (T i), rfl⟩⟩)
      (fun i hi ↦ centringDilate_image_subset_ball (hball i hi))
      (fun i _ ↦ (centringDilate_image_subset_lineNbhd (T i)).trans
        (Metric.cthickening_mono (by linarith) _))
  refine ⟨G, ϖ, hmem, hsurj, hcov, hcen, hmid, ?_, hED⟩
  calc G.card ≤ (s.image ϖ).card := by
        refine Finset.card_le_card ?_
        intro W hW
        obtain ⟨i, hi, rfl⟩ := hsurj W hW
        exact Finset.mem_image_of_mem _ hi
    _ ≤ s.card := Finset.card_image_le

open Classical in
/-- **`exists_centredRepresentatives` with the node's two `δ'/4` estimates exported.**

Additive sibling;   This is the form the count transport's
producer consumes: with the node's midpoint within `δ'/4` of the **member's** line foot and its
direction within `δ'/4` of the **member's** direction — stated relative to the member, not to the
cover tube — a consumer holding the member's own containment in an arbitrary tube `W` closes the
fibre bound by one triangle estimate.  Both conjuncts come straight from
`exists_setCanonicalCentredCover_data`, which exports what its own proof already had. -/
theorem exists_centredRepresentatives_data {δ' : NNReal} (hδ0 : 0 < δ') (hδ : (δ' : ℝ) ≤ 1 / 20)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ' E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ (G : Finset (Tube δ' E)) (ϖ : ι → Tube δ' E),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ i ∈ s, centringDilate '' (T i).carrier ⊆ (ϖ i).carrier) ∧
      (∀ W ∈ G, W.IsCentred) ∧
      (∀ W ∈ G, ‖W.midpoint‖ ≤ 2 / 5 + (δ' : ℝ) / 4) ∧
      G.card ≤ s.card ∧
      (∀ o e : E, ‖e‖ = 1 →
        ((G.filter fun W : Tube δ' E ↦ W.carrier ⊆
            Metric.cthickening (5 * (δ' : ℝ)) (Set.range fun t : ℝ ↦ o + t • e)).card : ℝ)
          ≤ Tube.canonicalCoverEDConstant (Module.finrank ℝ E) (2 / 5 + (δ' : ℝ) / 4)) ∧
      (∀ i ∈ s, ‖Tube.lineFoot (centringDilate (T i).midpoint) ((T i).direction)
        - (ϖ i).midpoint‖ ≤ (δ' : ℝ) / 4) ∧
      (∀ i ∈ s, ‖(T i).direction - (ϖ i).direction‖ ≤ (δ' : ℝ) / 4) := by
  classical
  have hδr : (0 : ℝ) < (δ' : ℝ) := hδ0
  obtain ⟨G, ϖ, hmem, hsurj, hcov, hcen, hmid, hED, hfoot, hdir⟩ :=
    exists_setCanonicalCentredCover_data (E := E) hδ0 hδ s
      (fun i ↦ centringDilate '' (T i).carrier)
      (fun i ↦ centringDilate (T i).midpoint) (fun i ↦ (T i).direction)
      (fun i _ ↦ (T i).norm_direction)
      (fun i _ ↦ ⟨centringDilate (T i).midpoint,
        ⟨(T i).midpoint, Tube.midpoint_mem_carrier hδ0 (T i), rfl⟩⟩)
      (fun i hi ↦ centringDilate_image_subset_ball (hball i hi))
      (fun i _ ↦ (centringDilate_image_subset_lineNbhd (T i)).trans
        (Metric.cthickening_mono (by linarith) _))
  refine ⟨G, ϖ, hmem, hsurj, hcov, hcen, hmid, ?_, hED, hfoot, hdir⟩
  calc G.card ≤ (s.image ϖ).card := by
        refine Finset.card_le_card ?_
        intro W hW
        obtain ⟨i, hi, rfl⟩ := hsurj W hW
        exact Finset.mem_image_of_mem _ hi
    _ ≤ s.card := Finset.card_image_le

open Classical in
/-- **the `_data` sibling projects onto the existing statement.** -/
theorem exists_centredRepresentatives_of_data {δ' : NNReal} (hδ0 : 0 < δ') (hδ : (δ' : ℝ) ≤ 1 / 20)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ' E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ (G : Finset (Tube δ' E)) (ϖ : ι → Tube δ' E),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ i ∈ s, centringDilate '' (T i).carrier ⊆ (ϖ i).carrier) ∧
      (∀ W ∈ G, W.IsCentred) ∧
      (∀ W ∈ G, ‖W.midpoint‖ ≤ 2 / 5 + (δ' : ℝ) / 4) ∧
      G.card ≤ s.card ∧
      (∀ o e : E, ‖e‖ = 1 →
        ((G.filter fun W : Tube δ' E ↦ W.carrier ⊆
            Metric.cthickening (5 * (δ' : ℝ)) (Set.range fun t : ℝ ↦ o + t • e)).card : ℝ)
          ≤ Tube.canonicalCoverEDConstant (Module.finrank ℝ E) (2 / 5 + (δ' : ℝ) / 4)) := by
  obtain ⟨G, ϖ, h1, h2, h3, h4, h5, h6, h7, -, -⟩ :=
    exists_centredRepresentatives_data hδ0 hδ s T hball
  exact ⟨G, ϖ, h1, h2, h3, h4, h5, h6, h7⟩

/-! ### The cardinality half of `eq:defect-centred-ledger` (l.6014) -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- **The fibre of the representative map is bounded by the input family's line-ED constant.**

If `ϖ i = ϖ j = W` then the dilated carriers of `T i` and `T j` both lie in `W`, hence — pulling
the similarity back by the factor `8` — both `T i` and `T j` lie in the `8δ`-neighbourhood of one
line, the `8`-fold dilate of `W`'s core line.  So the fibre is exactly a set counted by
`IsLineEssDistinctAt 8 A`, and the source's fibre charge `F₀ A` (l.5636) becomes the sharp
`A` at neighbourhood radius `8δ`. -/
theorem fibre_card_le_of_lineEDAt {δ : NNReal} {ι : Type*} {s : Finset ι} {T : ι → Tube δ E}
    {A : ℕ} (hED : IsLineEssDistinctAt 8 A s T)
    {W : Tube δ E} {ϖ : ι → Tube δ E}
    (hcov : ∀ i ∈ s, centringDilate '' (T i).carrier ⊆ (ϖ i).carrier) :
    (s.filter fun i ↦ ϖ i = W).card ≤ A := by
  classical
  set L : Set E := Set.range fun t : ℝ ↦ (8 : ℝ) • W.x + t • W.direction with hL
  refine le_trans (Finset.card_le_card ?_)
    (hED ((8 : ℝ) • W.x) W.direction W.norm_direction)
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  obtain ⟨his, hiW⟩ := hi
  refine ⟨his, ?_⟩
  intro z hz
  -- the dilated point lies in `W`, hence within `δ` of `W`'s core line
  have h1 : centringDilate z ∈ (ϖ i).carrier :=
    hcov i his ⟨z, hz, rfl⟩
  rw [hiW] at h1
  have h2 : centringDilate z
      ∈ Metric.cthickening (1 * (δ : ℝ)) (Set.range fun t : ℝ ↦ W.x + t • W.direction) :=
    W.carrier_subset_cthickening_line_self le_rfl h1
  have h3 : Tube.lineDist W.x W.direction (centringDilate z) ≤ (δ : ℝ) := by
    have := (Tube.mem_cthickening_line_iff W.norm_direction
      (by have := δ.coe_nonneg; linarith : (0:ℝ) ≤ 1 * (δ : ℝ))).mp h2
    linarith
  -- pull back by the factor 8
  have h4 : Tube.lineDist ((8 : ℝ) • W.x) W.direction z = 8 * Tube.lineDist W.x W.direction
      (centringDilate z) := by
    unfold Tube.lineDist centringDilate
    have he : z - (8 : ℝ) • W.x = (8 : ℝ) • ((8 : ℝ)⁻¹ • z - W.x) := by module
    rw [he, real_inner_smul_left, smul_sub, smul_smul, ← norm_smul_of_nonneg
      (by norm_num : (0:ℝ) ≤ 8)]
    congr 1
    module
  rw [Kakeya.VeryNotSticky.lineNbhd_eq_cthickening_range]
  refine (Tube.mem_cthickening_line_iff W.norm_direction ?_).mpr ?_
  · have := δ.coe_nonneg; linarith
  · rw [h4]; linarith

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- **`eq:defect-centred-ledger`, the cardinality clauses** (l.6014): `A^{-1} #𝔾 ≤ #𝔾^ ≤ #𝔾`.
The upper half is the surjectivity of `ϖ`; the lower half is the fibre bound. -/
theorem card_le_of_centredRepresentatives {δ : NNReal} {ι : Type*} {s : Finset ι}
    {T : ι → Tube δ E} {A : ℕ} (hED : IsLineEssDistinctAt 8 A s T)
    {G : Finset (Tube δ E)} {ϖ : ι → Tube δ E}
    (hmem : ∀ i ∈ s, ϖ i ∈ G)
    (hcov : ∀ i ∈ s, centringDilate '' (T i).carrier ⊆ (ϖ i).carrier) :
    s.card ≤ A * G.card := by
  classical
  calc s.card = ∑ W ∈ G, (s.filter fun i ↦ ϖ i = W).card :=
        Finset.card_eq_sum_card_fiberwise hmem
    _ ≤ ∑ _W ∈ G, A := Finset.sum_le_sum fun W _ ↦ fibre_card_le_of_lineEDAt hED hcov
    _ = A * G.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end Kakeya.VeryNotSticky

/-! # The density condition for the centred family

`CentredHandBack` requires its `dens` and `full` inputs at the loss exponent
`qc = gain ζ/100`; the available bounds use `ηd − cst` and `ηd`. The required
comparison is `ηd − cst ≤ qc`, proved by the three theorems below.

This comparison uses `Lemma91At`'s `ηd` and the fields of
`Kakeya.ML2Assembly.Lemma91ParamsAt`. It does not use the 7.7(B) window or
`ML2Reduction.IsKatzTaoDividingWindow.le_window_maxDensity`. -/

-- RELOCATED to `Reduction/SpineOuterTubes.lean`, beside `Lemma91At` itself:
-- `Kakeya.ML2Reduction.Lemma91At.mono_dens`.  Same namespace, so the fully qualified name
-- is unchanged and dot notation `h.mono_dens` resolves exactly as before.

namespace Kakeya.CentringDensity

/-- **The verdict, negative half.** -/
theorem not_dens_le_gain_div_hundred_of_pos :
    ¬ ∀ (gain dens : ℝ → ℝ), (∀ ζ : ℝ, 0 < ζ → 0 < gain ζ) →
        (∀ ζ : ℝ, 0 < ζ → 0 < dens ζ) → ∀ ζ : ℝ, 0 < ζ → dens ζ ≤ gain ζ / 100 := by
  intro h
  have := h (fun _ ↦ 1) (fun _ ↦ 1) (fun _ _ ↦ one_pos) (fun _ _ ↦ one_pos) 1 one_pos
  norm_num at this

end Kakeya.CentringDensity

namespace Kakeya.ML2Reduction

universe u

/-- **The condition fix,.**  Instantiating the site's `hL91` at the density exponent
`ηd := qc + cst` turns the blocking condition `ηd − cst ≤ qc` into the *identity* `qc ≤ qc`, so the
centring's `dens`/`full` inputs are exactly the site's own `hmax`/`hfull`.  Nothing of Lemma 9.1
moves: the step is `Lemma91At.mono_dens`, and what changes is only which density the **window
producer** must supply — the source's own move (l.5993 assumes `Δ_max ≤ δ^{-q}` *before* invoking
the very-not-sticky lemma at `η₀ ≥ 4q`, l.6089). -/
theorem lemma91At_at_centringExponent {β ϖ ζ ν ηd cst qc : ℝ} {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (h : Lemma91At.{u} β ϖ ζ ν ηd δ) (hqc : qc + cst ≤ ηd) :
    Lemma91At.{u} β ϖ ζ ν (qc + cst) δ ∧ (qc + cst) - cst = qc :=
  ⟨h.mono_dens hδ0 hδ1 hqc, by ring⟩

end Kakeya.ML2Reduction

namespace Kakeya.CentringDensity

open scoped NNReal ENNReal

/-- **What the condition reduces to, exactly.**  `cst` is only constrained by
`hloss : outerLoss R ≤ (δ')^{-cst}`, and `outerLoss R` is `δ'`-free, so any `cst > 0` is available
below an explicit threshold (this is `Kakeya.ML2Reduction.exists_threshold_const_le_rpow`, existing).
Hence the blocking condition `ηd − cst ≤ gain ζ/100` is available **iff**
`gain ζ/100 + cst ≤ dens ζ` for some admissible `cst`, i.e. iff `gain ζ/100 < dens ζ`. -/
theorem exists_threshold_cst {cst : ℝ} (hcst : 0 < cst) (Lam : ℝ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Lam ≤ ρ ^ (-cst) :=
  Kakeya.ML2Reduction.exists_threshold_const_le_rpow hcst

end Kakeya.CentringDensity


/-! # Round 2 — the  structures and the satisfiability witness -/

section Round2
open Kakeya.ML2Reduction

namespace Kakeya.VeryNotSticky

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A carrier point in midpoint–direction coordinates. -/
theorem _root_.Tube.exists_decomp_of_mem_carrier {δ : NNReal} (U : Tube δ E) {z : E}
    (hz : z ∈ U.carrier) :
    ∃ (t : ℝ) (g : E), |t| ≤ 1 / 2 ∧ ‖g‖ ≤ (δ : ℝ) ∧
      z = U.midpoint + t • U.direction + g := by
  rw [U.carrier_eq] at hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨t, ht, rfl⟩ := U.exists_param_of_mem_segment hw
  refine ⟨t, z - (U.midpoint + t • U.direction), ht, ?_, by abel⟩
  rw [← dist_eq_norm]
  exact Metric.mem_closedBall.mp hzw

/-- **The centred container at the origin.** -/
noncomputable def centredOrigin {δ : NNReal} (V : Tube δ E) : Tube δ E :=
  Tube.ofMidpointDirection δ 0 V.direction V.norm_direction

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem centredOrigin_isCentred {δ : NNReal} (V : Tube δ E) : (centredOrigin V).IsCentred := by
  unfold Tube.IsCentred centredOrigin
  rw [Tube.midpoint_ofMidpointDirection']
  simp

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem centredOrigin_subset_ball {δ : NNReal} (V : Tube δ E) (hδ : (δ : ℝ) ≤ 1 / 4) :
    (centredOrigin V).carrier ⊆ Metric.closedBall (0 : E) (3 / 4) := by
  intro z hz
  obtain ⟨t, g, ht, hg, rfl⟩ := (centredOrigin V).exists_decomp_of_mem_carrier hz
  have hmid : (centredOrigin V).midpoint = (0 : E) := by
    unfold centredOrigin; rw [Tube.midpoint_ofMidpointDirection']
  have hdir : ‖(centredOrigin V).direction‖ = 1 := (centredOrigin V).norm_direction
  simp only [Metric.mem_closedBall, dist_zero_right]
  have := abs_le.mp ht
  calc ‖(centredOrigin V).midpoint + t • (centredOrigin V).direction + g‖
      ≤ ‖(centredOrigin V).midpoint + t • (centredOrigin V).direction‖ + ‖g‖ := norm_add_le _ _
    _ ≤ (‖(centredOrigin V).midpoint‖ + ‖t • (centredOrigin V).direction‖) + ‖g‖ := by
        gcongr; exact norm_add_le _ _
    _ = (0 + |t|) + ‖g‖ := by rw [hmid, norm_zero, norm_smul, hdir, mul_one, Real.norm_eq_abs]
    _ ≤ (0 + 1 / 2) + (δ : ℝ) := by gcongr
    _ ≤ 3 / 4 := by linarith

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The `covers` clause, geometrically**: the normalised image of a tube — normalised about the
tube's own midpoint — lies inside the centred container at the origin, at the SAME radius.  The
image has core extent `1/8` and thickness `δ/8`; the container has a centred **unit** core and
radius `δ`, so there is a factor-`8` margin in each of the two parameters.  This is what defeats
the obstruction `Tube.abs_inner_midpoint_direction_le_of_subset_centred`, whose hypothesis is
that both sides are `Tube δ E`. -/
theorem normalise_image_subset_centredOrigin {δ : NNReal} (V : Tube δ E) :
    centringDilate '' ((fun x ↦ x - V.midpoint) '' V.carrier) ⊆ (centredOrigin V).carrier := by
  rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨t, g, ht, hg, hzeq⟩ := V.exists_decomp_of_mem_carrier hz
  have hmid : (centredOrigin V).midpoint = (0 : E) := by
    unfold centredOrigin; rw [Tube.midpoint_ofMidpointDirection']
  have hdir : (centredOrigin V).direction = V.direction := by
    unfold centredOrigin; rw [Tube.direction_ofMidpointDirection']
  have ht8 : |t / 8| ≤ 1 / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 8)]
    have := abs_le.mp ht; linarith
  refine (centredOrigin V).mem_carrier_of_dist_le
    ((centredOrigin V).midpoint_add_smul_mem_segment ht8) ?_
  have heq : centringDilate (z - V.midpoint)
      - ((centredOrigin V).midpoint + (t / 8) • (centredOrigin V).direction)
      = (8 : ℝ)⁻¹ • g := by
    rw [hmid, hdir, hzeq]
    unfold centringDilate
    module
  rw [dist_eq_norm, heq, norm_smul, norm_inv, Real.norm_ofNat, inv_mul_eq_div]
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  linarith

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

universe u

/-! ### Singleton evaluations of the three shading functionals -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*}

theorem fullness_singleton_eq_one (i₀ : ι) (V : ι → ShadedBody F)
    (hsh : (V i₀).shade = (V i₀).carrier) (hpos : volume (V i₀).carrier ≠ 0) :
    ShadedBody.fullness {i₀} V = 1 := by
  have htop : volume (V i₀).carrier ≠ ⊤ := (V i₀).isCompact.measure_ne_top
  have : (ShadedBody.fullness {i₀} V : ENNReal) = 1 := by
    rw [ShadedBody.fullness_def, Finset.sum_singleton, Finset.sum_singleton, hsh,
      ENNReal.div_self hpos htop]
  exact_mod_cast this

theorem multiplicity_singleton_eq_one (i₀ : ι) (V : ι → ShadedBody F)
    (hpos : volume (V i₀).shade ≠ 0) :
    ShadedBody.multiplicity {i₀} V = 1 := by
  have htop : volume (⋃ i ∈ ({i₀} : Finset ι), (V i).shade) ≠ ⊤ :=
    ShadedBody.volume_iUnion_shade_ne_top _ _
  rw [ShadedBody.multiplicity_eq_div, Finset.sum_singleton]
  have hun : (⋃ i ∈ ({i₀} : Finset ι), (V i).shade) = (V i₀).shade := by simp
  rw [hun] at htop ⊢
  exact ENNReal.div_self hpos htop

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky
universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- A tube shaded by the whole of itself. -/
def fullShadeTube {σ : NNReal} (T : Tube σ E) : ShadedTube σ E where
  toTube := T
  shade := T.carrier
  measurableSet_shade := T.toConvexSpaceBody.isCompact.isClosed.measurableSet
  shade_subset := subset_rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
@[simp] theorem fullShadeTube_toTube {σ : NNReal} (T : Tube σ E) :
    (fullShadeTube T).toTube = T := rfl
omit [FiniteDimensional ℝ E] [Nontrivial E] in
@[simp] theorem fullShadeTube_shade {σ : NNReal} (T : Tube σ E) :
    (fullShadeTube T).shade = T.carrier := rfl


omit [Nontrivial E] in
theorem fullness_singleton_fullShadeTube {ι : Type*} (i₀ : ι) {σ : NNReal}
    (T : Tube σ E) (hpos : volume T.carrier ≠ 0) :
    ShadedBody.fullness {i₀} (fun _ : ι ↦ (fullShadeTube T).toShadedBody) = 1 :=
  fullness_singleton_eq_one i₀ _ rfl hpos


omit [Nontrivial E] in
theorem multiplicity_singleton_fullShadeTube {ι : Type*} (i₀ : ι) {σ : NNReal}
    (T : Tube σ E) (hpos : volume T.carrier ≠ 0) :
    ShadedBody.multiplicity {i₀} (fun _ : ι ↦ (fullShadeTube T).toShadedBody) = 1 :=
  multiplicity_singleton_eq_one i₀ _ hpos

/-- **A concrete rescaling situation.**  `θ = 1`, `τ = 4δ'`, `σ = δ'`, `R = C_N(3)`. -/
theorem isRescalingSituation_witness {δ' : NNReal} (hδ0 : 0 < δ') (hδ4 : 4 * (δ' : ℝ) ≤ 1) :
    Tube.IsRescalingSituation (1 : NNReal) (4 * δ') δ' (Tube.normalization.C 3) 3 where
  pos_ambient := by norm_num
  inner_le_ambient := by
    have : (4 * δ' : ℝ) ≤ (1 : ℝ) := hδ4
    exact_mod_cast this
  ambient_le_one := le_rfl
  pos_out := hδ0
  out_le_quarter := by linarith [δ'.coe_nonneg]
  out_le_ratio := by
    push_cast
    rw [div_one]
    linarith [δ'.coe_nonneg]
  normalizationConst_le_radius := le_rfl

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

open MeasureTheory
open scoped NNReal ENNReal

theorem one_le_rpow_neg {δ : NNReal} (_hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {c : ℝ} (hc : 0 ≤ c) :
    (1 : ENNReal) ≤ (δ : ENNReal) ^ (-c) := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have := ENNReal.rpow_le_rpow_of_exponent_ge (x := (δ : ENNReal)) hδE1
    (show -c ≤ (0 : ℝ) by linarith)
  simpa using this

theorem rpow_le_one_of_nonneg {δ : NNReal} (hδ1 : δ ≤ 1) {c : ℝ} (hc : 0 ≤ c) :
    (δ : ENNReal) ^ c ≤ 1 := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have := ENNReal.rpow_le_rpow_of_exponent_ge (x := (δ : ENNReal)) hδE1 (show (0:ℝ) ≤ c from hc)
  simpa using this

/-- **THE SATISFIABILITY WITNESS for `CentredHandBack`**, at `qc = 1`. -/
theorem exists_centredHandBack_witness {δ' : NNReal} (hδ0 : 0 < δ') (hδ4 : 4 * (δ' : ℝ) ≤ 1)
    (hδ20 : (δ' : ℝ) ≤ 1 / 20)
    (hδloss : δ' ≤ (Kakeya.ML2Reduction.outerLoss (Tube.normalization.C 3))⁻¹)
    (u : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ = 1) :
    ∃ (m : EuclideanSpace ℝ (Fin 3))
      (Z' : Unit → ShadedTube (4 * δ') (EuclideanSpace ℝ (Fin 3)))
      (U' : Unit → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))),
      CentredHandBack (isRescalingSituation_witness hδ0 hδ4)
        (lt_of_lt_of_le zero_lt_one (Tube.normalization.one_le_C 3))
        (Tube.ofMidpointDirection 1 0 u hu) m 1 {()} {()} Z' U' := by
  classical
  have hR : (0 : ℝ) < Tube.normalization.C 3 :=
    lt_of_lt_of_le zero_lt_one (Tube.normalization.one_le_C 3)
  have hR1 : (1 : ℝ) ≤ Tube.normalization.C 3 := Tube.normalization.one_le_C 3
  have hδ1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by linarith [δ'.coe_nonneg]
    exact_mod_cast this
  have h4δ0 : 0 < 4 * δ' := by positivity
  have h4δ1 : 4 * δ' ≤ 1 := by exact_mod_cast hδ4
  set hsit := isRescalingSituation_witness hδ0 hδ4 with hsitdef
  set T₀ : Tube 1 (EuclideanSpace ℝ (Fin 3)) := Tube.ofMidpointDirection 1 0 u hu with hT₀
  set Zt : Tube (4 * δ') (EuclideanSpace ℝ (Fin 3)) :=
    Tube.ofMidpointDirection (4 * δ') 0 u hu with hZt
  set Z' : Unit → ShadedTube (4 * δ') (EuclideanSpace ℝ (Fin 3)) :=
    fun _ ↦ fullShadeTube Zt with hZ'
  -- the small tube sits inside the ambient one
  have hsub : ∀ i ∈ ({()} : Finset Unit), (Z' i).carrier ⊆ T₀.carrier := by
    intro i _ z hz
    obtain ⟨t, g, ht, hg, rfl⟩ := Zt.exists_decomp_of_mem_carrier hz
    have hzm : Zt.midpoint = 0 := by rw [hZt, Tube.midpoint_ofMidpointDirection']
    have hzd : Zt.direction = u := by rw [hZt, Tube.direction_ofMidpointDirection']
    have hTm : T₀.midpoint = 0 := by rw [hT₀, Tube.midpoint_ofMidpointDirection']
    have hTd : T₀.direction = u := by rw [hT₀, Tube.direction_ofMidpointDirection']
    refine T₀.mem_carrier_of_dist_le (T₀.midpoint_add_smul_mem_segment (t := t) ht) ?_
    rw [dist_eq_norm, hTm, hTd, hzm, hzd]
    have : (0 : EuclideanSpace ℝ (Fin 3)) + t • u + g - (0 + t • u) = g := by abel
    rw [this]
    have h4 : ‖g‖ ≤ 4 * (δ' : ℝ) := by
      have : ((4 * δ' : NNReal) : ℝ) = 4 * (δ' : ℝ) := by push_cast; ring
      rwa [this] at hg
    have : ((1 : NNReal) : ℝ) = 1 := by norm_num
    rw [this]; linarith
  set Ot : ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) :=
    Kakeya.ML2Reduction.outerFamily hsit.pos_ambient T₀ hR δ' Z' () with hOt
  -- positivity of the two carriers
  have hZvol : volume Zt.carrier ≠ 0 := (Tube.volume_pos_and_lt_top h4δ0 h4δ1 Zt).1.ne'
  have hUvol : volume (centredOrigin Ot.toTube).carrier ≠ 0 :=
    (Tube.volume_pos_and_lt_top hδ0 hδ1 _).1.ne'
  -- the fullness of the outer family
  have hZfull : ShadedBody.fullness ({()} : Finset Unit)
      (fun i ↦ (Z' i).toShadedBody) = 1 :=
    fullness_singleton_fullShadeTube () Zt hZvol
  have hOfull : (Kakeya.ML2Reduction.outerLoss (Tube.normalization.C 3))⁻¹
      ≤ ShadedBody.fullness ({()} : Finset Unit)
          (fun i ↦ (Kakeya.ML2Reduction.outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
      := by
    have h := Kakeya.ML2Reduction.outerFamily_le_fullness (E := EuclideanSpace ℝ (Fin 3))
      (s := ({()} : Finset Unit)) (𝕋 := Z') (T₀ := T₀) (by simp) hsit hR hR1
      (by push_cast; rw [div_one]) hsub
    rwa [hZfull, mul_one] at h
  refine ⟨Ot.midpoint, Z', fun _ ↦ fullShadeTube (centredOrigin Ot.toTube), ?_⟩
  refine
    { subset := subset_rfl
      small := hδ20
      dens := ?_
      full := ?_
      centred := ?_
      contained := ?_
      covers := ?_
      maxDensity_le := ?_
      fullness_ge := ?_
      card_le := le_rfl
      multiplicity_le := ?_ }
  · exact le_trans (Kakeya.ML2Squeeze.maxDensity_le_one_of_singleton () _)
      (one_le_rpow_neg hδ0 hδ1 zero_le_one)
  · rw [ENNReal.rpow_one]
    have : (δ' : NNReal) ≤ ShadedBody.fullness ({()} : Finset Unit)
        (fun i ↦ (Kakeya.ML2Reduction.outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) :=
      le_trans hδloss hOfull
    exact_mod_cast this
  · intro i _; exact centredOrigin_isCentred _
  · intro i _
    exact (centredOrigin_subset_ball _ (by linarith [δ'.coe_nonneg] : (δ' : ℝ) ≤ 1 / 4)).trans
      (Metric.closedBall_subset_closedBall (by norm_num))
  · intro i _
    rw [normalise_image_eq]
    exact normalise_image_subset_centredOrigin Ot.toTube
  · exact le_trans (Kakeya.ML2Squeeze.maxDensity_le_one_of_singleton () _)
      (one_le_rpow_neg hδ0 hδ1 (by norm_num))
  · rw [fullness_singleton_fullShadeTube () _ hUvol]
    have h1 : ((1 : NNReal) : ENNReal) = 1 := by norm_num
    rw [h1]
    exact rpow_le_one_of_nonneg hδ1 (by norm_num)
  · have hOne : ShadedBody.multiplicity ({()} : Finset Unit)
        (fun i ↦ (Kakeya.ML2Reduction.outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
        = 1 := by
      refine multiplicity_singleton_eq_one () _ ?_
      have hpos : 0 < ShadedBody.fullness ({()} : Finset Unit)
          (fun i ↦ (Kakeya.ML2Reduction.outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) :=
        lt_of_lt_of_le (by
          have := Kakeya.ML2Reduction.one_le_outerLoss hR1
          positivity) hOfull
      have := ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos _ _ hpos
      simpa using this
    rw [hOne, multiplicity_singleton_fullShadeTube () _ hUvol, mul_one]
    exact one_le_rpow_neg hδ0 hδ1 (by norm_num)

end Kakeya.VeryNotSticky

end Round2

/-! # Round 3 — `lemaffineinvariance` in the tree: the Jacobian, the two ledger
identities it settles, and the centred tube's Pythagorean reach -/

section Round3
open Pointwise

namespace Kakeya.VeryNotSticky
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem volume_image_sub_const (m : E) (A : Set E) :
    volume ((fun x ↦ x - m) '' A) = volume A := by
  have : (fun x : E ↦ x - m) '' A = (-m) +ᵥ A := by
    ext y; simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by abel⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by abel⟩
  rw [this, measure_vadd]

theorem volume_smul_image (r : ℝ) (A : Set E) :
    volume ((fun x : E ↦ r • x) '' A)
      = ENNReal.ofReal |r ^ Module.finrank ℝ E| * volume A := by
  rw [show (fun x : E ↦ r • x) '' A = r • A from rfl]
  exact MeasureTheory.Measure.addHaar_smul volume r A

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky
open MeasureTheory Pointwise
open scoped NNReal ENNReal

/-- **The similarity's Jacobian** (refined `lemaffineinvariance`, l.4739–4761): the normalising
map multiplies every volume by `8^{-n}`, and by nothing else. -/
theorem volume_normalise_image (m : EuclideanSpace ℝ (Fin 3))
    (A : Set (EuclideanSpace ℝ (Fin 3))) :
    volume (normalise m '' A) = ENNReal.ofReal (1 / 512) * volume A := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hcomp : normalise m '' A
      = (fun x : EuclideanSpace ℝ (Fin 3) ↦ (8 : ℝ)⁻¹ • x) '' ((fun x ↦ x - m) '' A) := by
    rw [Set.image_image]; rfl
  rw [hcomp, volume_smul_image, volume_image_sub_const, hfr]
  norm_num

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky
open MeasureTheory Pointwise
open scoped NNReal ENNReal

/-- **The multiplicity identity** — the similarity is loss-free (`lemaffineinvariance`, l.4747). -/
theorem multiplicity_pushforward {α : Type*} (s : Finset α) {δ' : NNReal}
    (O U : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (m : EuclideanSpace ℝ (Fin 3))
    (hsh : ∀ i ∈ s, (U i).shade = normalise m '' (O i).shade) :
    ShadedBody.multiplicity s (fun i ↦ (U i).toShadedBody)
      = ShadedBody.multiplicity s (fun i ↦ (O i).toShadedBody) := by
  have hc0 : ENNReal.ofReal (1 / 512) ≠ 0 := by simp
  have hct : ENNReal.ofReal (1 / 512) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnum : ∑ i ∈ s, volume (U i).shade
      = ENNReal.ofReal (1 / 512) * ∑ i ∈ s, volume (O i).shade := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [show (U i).shade = normalise m '' (O i).shade from hsh i hi, volume_normalise_image]
  have hunion : (⋃ i ∈ s, (U i).shade) = normalise m '' (⋃ i ∈ s, (O i).shade) := by
    rw [Set.image_iUnion₂]
    exact Set.iUnion₂_congr fun i hi ↦ hsh i hi
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hnum, hunion,
    volume_normalise_image, ENNReal.mul_div_mul_left _ _ hc0 hct]

/-- **The fullness identity**: the tree's `fullness` is a ratio of sums, and all `δ'`-tubes have
the same carrier volume, so the representatives' fullness is the represented family's times the
Jacobian `1/512` — **exactly**.  This is where the source's *second* power of `q` is spent
(l.6084–6086); the first is the fibre and the third the fixed numerals. -/
theorem fullness_pushforward {α : Type*} (s : Finset α) {δ' : NNReal}
    (O U : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (m : EuclideanSpace ℝ (Fin 3))
    (hsh : ∀ i ∈ s, (U i).shade = normalise m '' (O i).shade) :
    (ShadedBody.fullness s (fun i ↦ (U i).toShadedBody) : ENNReal)
      = ENNReal.ofReal (1 / 512)
        * (ShadedBody.fullness s (fun i ↦ (O i).toShadedBody) : ENNReal) := by
  have hnum : ∑ i ∈ s, volume (U i).shade
      = ENNReal.ofReal (1 / 512) * ∑ i ∈ s, volume (O i).shade := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [show (U i).shade = normalise m '' (O i).shade from hsh i hi, volume_normalise_image]
  have hden : ∑ i ∈ s, volume (U i).carrier = ∑ i ∈ s, volume (O i).carrier :=
    Finset.sum_congr rfl fun i _ ↦
      Tube.volume_carrier_eq_volume_carrier (U i).toTube (O i).toTube
  have hO : (ShadedBody.fullness s (fun i ↦ (O i).toShadedBody) : ENNReal)
      = (∑ i ∈ s, volume (O i).shade) / (∑ i ∈ s, volume (O i).carrier) :=
    ShadedBody.coe_fullness _ _
  have hU : (ShadedBody.fullness s (fun i ↦ (U i).toShadedBody) : ENNReal)
      = (∑ i ∈ s, volume (U i).shade) / (∑ i ∈ s, volume (U i).carrier) :=
    ShadedBody.coe_fullness _ _
  rw [hU, hO, hnum, hden, mul_div_assoc]

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky
open MeasureTheory Metric RealInnerProductSpace
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [ProperSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
/-- **A centred tube's reach, by Pythagoras** (the bound `lemcanonicalcover` l.4778 actually uses).

For a **centred** tube the core's midpoint is orthogonal to its direction, so a core point
`p + t·d` with `|t| ≤ 1/2` has `‖p + t·d‖ = √(‖p‖² + t²) ≤ √(‖p‖² + 1/4)` — *not* the triangle
bound `‖p‖ + 1/2`.  Hence the whole carrier lies in `B̄(0, √(‖p‖² + 1/4) + δ)`.

At the canonical cover's own parameter bound `‖p‖ ≤ 2/5 + r` and radius `4r`, `r ≤ 1/80`, this
gives `√((0.4125)² + 1/4) + 1/20 = 0.698195… < 3/4` — so the source's `𝓒_r ⊂ B(0,3/4)`
(l.4778) is correct as stated, and an earlier note of mine claiming an inconsistency with
l.4787/l.4791 was wrong: it used the triangle inequality and discarded `p ⊥ d`. -/
theorem _root_.Tube.carrier_subset_closedBall_of_isCentred {δ : NNReal} (W : Tube δ F)
    (hcen : W.IsCentred) :
    W.carrier ⊆ Metric.closedBall (0 : F)
      (Real.sqrt (‖W.midpoint‖ ^ 2 + 1 / 4) + (δ : ℝ)) := by
  intro z hz
  obtain ⟨t, g, ht, hg, rfl⟩ := W.exists_decomp_of_mem_carrier hz
  have hd : ‖W.direction‖ = 1 := W.norm_direction
  have hcen' : ⟪W.midpoint, W.direction⟫ = (0 : ℝ) := hcen
  have hsq : ‖W.midpoint + t • W.direction‖ ^ 2 = ‖W.midpoint‖ ^ 2 + t ^ 2 := by
    have h1 : ⟪W.midpoint, t • W.direction⟫ = (0 : ℝ) := by
      rw [real_inner_smul_right, hcen', mul_zero]
    have h2 : ‖t • W.direction‖ = |t| := by
      rw [norm_smul, hd, mul_one, Real.norm_eq_abs]
    rw [norm_add_sq_real, h1, h2, sq_abs]
    ring
  have hcore : ‖W.midpoint + t • W.direction‖ ≤ Real.sqrt (‖W.midpoint‖ ^ 2 + 1 / 4) := by
    have hnn : (0 : ℝ) ≤ ‖W.midpoint + t • W.direction‖ := norm_nonneg _
    rw [show ‖W.midpoint + t • W.direction‖
        = Real.sqrt (‖W.midpoint + t • W.direction‖ ^ 2) from (Real.sqrt_sq hnn).symm, hsq]
    refine Real.sqrt_le_sqrt ?_
    have := abs_le.mp ht
    nlinarith [sq_nonneg t, sq_abs t]
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖W.midpoint + t • W.direction + g‖
      ≤ ‖W.midpoint + t • W.direction‖ + ‖g‖ := norm_add_le _ _
    _ ≤ Real.sqrt (‖W.midpoint‖ ^ 2 + 1 / 4) + (δ : ℝ) := by gcongr

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky
open MeasureTheory Metric
open scoped NNReal ENNReal

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [ProperSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
/-- `contained` with no numeral in the producer: Pythagoras plus the parameter bound. -/
theorem carrier_subset_unitBall_of_isCentred {δ : NNReal} (W : Tube δ G) (hcen : W.IsCentred)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hmid : ‖W.midpoint‖ ≤ R₀)
    (h : Real.sqrt (R₀ ^ 2 + 1 / 4) + (δ : ℝ) ≤ 1) :
    W.carrier ⊆ Metric.closedBall (0 : G) 1 := by
  refine (W.carrier_subset_closedBall_of_isCentred hcen).trans
    (Metric.closedBall_subset_closedBall ?_)
  have hs : Real.sqrt (‖W.midpoint‖ ^ 2 + 1 / 4) ≤ Real.sqrt (R₀ ^ 2 + 1 / 4) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [norm_nonneg W.midpoint]
  linarith

/-- **The canonical cover's nodes really do sit in `B(0,3/4)`** (refined l.4778), by Pythagoras
and not by the triangle inequality: at the net's own `‖p‖ ≤ 2/5 + r` and radius `4r`, `r ≤ 1/80`,
the reach is `√((2/5+r)² + 1/4) + 4r`, which is `0.698195…` at `r = 1/80` and below `3/4`
throughout.  Compiled because an earlier note of mine asserted the opposite from a triangle
bound. -/
theorem canonicalCover_reach_lt {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 80) :
    Real.sqrt ((2 / 5 + r) ^ 2 + 1 / 4) + 4 * r < 3 / 4 := by
  have hy : (0 : ℝ) < 3 / 4 - 4 * r := by linarith
  have hsq : Real.sqrt ((2 / 5 + r) ^ 2 + 1 / 4) < 3 / 4 - 4 * r := by
    refine (Real.sqrt_lt' hy).mpr ?_
    nlinarith
  linarith

/-- **The two ledger clauses of `eq:defect-centred-ledger` that the similarity settles.** -/
theorem ledgerClauses_of_pushforward {α : Type*} (s : Finset α) {δ' : NNReal}
    (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1)
    (O U : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (m : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc : 0 ≤ qc)
    (hsh : ∀ i ∈ s, (U i).shade = normalise m '' (O i).shade)
    (hfull : (δ' : ENNReal) ^ qc ≤ (ShadedBody.fullness s (fun i ↦ (O i).toShadedBody) : ENNReal))
    (hthr : (δ' : ENNReal) ^ (2 * qc) ≤ ENNReal.ofReal (1 / 512)) :
    (δ' : ENNReal) ^ (3 * qc)
        ≤ (ShadedBody.fullness s (fun i ↦ (U i).toShadedBody) : ENNReal) ∧
      ShadedBody.multiplicity s (fun i ↦ (O i).toShadedBody)
        ≤ (δ' : ENNReal) ^ (-(3 * qc))
          * ShadedBody.multiplicity s (fun i ↦ (U i).toShadedBody) := by
  have hδE0 : (δ' : ENNReal) ≠ 0 := by simpa using ne_of_gt hδ0
  have hδEt : (δ' : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  constructor
  · have hadd : (δ' : ENNReal) ^ (3 * qc)
        = (δ' : ENNReal) ^ (2 * qc) * (δ' : ENNReal) ^ qc := by
      rw [← ENNReal.rpow_add _ _ hδE0 hδEt]; ring_nf
    rw [hadd, fullness_pushforward s O U m hsh]
    exact mul_le_mul' hthr hfull
  · rw [multiplicity_pushforward s O U m hsh]
    calc ShadedBody.multiplicity s (fun i ↦ (O i).toShadedBody)
        = 1 * ShadedBody.multiplicity s (fun i ↦ (O i).toShadedBody) := (one_mul _).symm
      _ ≤ (δ' : ENNReal) ^ (-(3 * qc)) * ShadedBody.multiplicity s (fun i ↦ (O i).toShadedBody) :=
          mul_le_mul' (one_le_rpow_neg hδ0 hδ1 (by linarith)) le_rfl

end Kakeya.VeryNotSticky

end Round3

end
