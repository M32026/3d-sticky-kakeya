/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Data.Finset.StoppingTime
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.Mathlib.Analysis.SubpolynomialGrowth
public import Kakeya.Mathlib.Data.Nat.Log
public import Kakeya.Multiplicity

/-!
# Plank typical-angle definitions and the stopping-time chain

This geometry layer, in namespace `Kakeya`, defines
the maximal plank angle `M`, the typical-angle predicates (`IsTypicalPlankAngle`), the stopping-time
scales `A`, `B`, the sub-polynomial growth lemmas, the abstract stopping-time chain, and the
per-fibre typical-angle lemma `typicalAngleFibre`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Kakeya

variable {ι : Type*}

/-- The maximal angle of a finite set `t` of indices under a pairwise angle `ang`:
`max_{i, j ∈ t} ang i j`. The supremum over the empty/singleton set is `0`. -/
def maxAngle (ang : ι → ι → ℝ≥0) (t : Finset ι) : ℝ≥0 :=
  (t ×ˢ t).sup fun p => ang p.1 p.2

theorem le_maxAngle {ang : ι → ι → ℝ≥0} {t : Finset ι} {i j : ι}
    (hi : i ∈ t) (hj : j ∈ t) : ang i j ≤ maxAngle ang t :=
  Finset.le_sup (f := fun p => ang p.1 p.2) (Finset.mk_mem_product hi hj)

theorem maxAngle_le {ang : ι → ι → ℝ≥0} {t : Finset ι} {c : ℝ≥0}
    (h : ∀ i ∈ t, ∀ j ∈ t, ang i j ≤ c) : maxAngle ang t ≤ c :=
  Finset.sup_le fun p hp =>
    h p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2

/-- The *effective angle scale* between two `a × b × 1` planks: the raw dihedral angle
`P.planeAngleNN Q` floored at `a / b` and capped at `1`. The angle between two `a × b × 1`
planks is only meaningful up to additive error `a / b` (GWZ §6), so `a / b` is the natural
smallest scale, while `1` is the largest meaningful scale (the raw radian angle lives in
`[0, π/2]`, which exceeds `1`). Flooring makes the lower endpoint `θ ≥ a / b` structural (and
handles singleton or nearly-parallel fibres, where the raw angle may be `0`); capping makes the
upper endpoint `θ ≤ 1` structural, so a stopping-time output `θ = M(𝒫ₖ)` automatically lies in
`[a / b, 1]`. -/
def effectivePlankAngle {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P Q : Plank a b hab hb1) : ℝ≥0 :=
  (1 : ℝ≥0) ⊓ ((a / b) ⊔ P.planeAngleNN Q)

theorem div_le_one_of_le {a b : ℝ≥0} (hab : a ≤ b) : a / b ≤ 1 :=
  div_le_one_of_le₀ hab (by positivity)

theorem effectivePlankAngle_le_one {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P Q : Plank a b hab hb1) : effectivePlankAngle P Q ≤ 1 :=
  inf_le_left

theorem le_effectivePlankAngle {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P Q : Plank a b hab hb1) : a / b ≤ effectivePlankAngle P Q :=
  le_inf (div_le_one_of_le hab) le_sup_left

/-- The blueprint's `M(𝒫')`: the maximal plank-intersection angle
`max_{i, j ∈ t} ∠(TPᵢ, TPⱼ)` over a finite index set `t`, using the `effectivePlankAngle`
(the dihedral angle `Prism3D.planeAngleNN` floored at `a / b`). -/
def maxPlankAngle {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ι → Plank a b hab hb1) (t : Finset ι) : ℝ≥0 :=
  maxAngle (fun i j => effectivePlankAngle (P i) (P j)) t

/-! ### Plank typical-angle predicates -/

/-- `ComparableScalarsWith C₁ C₂ x y` is the scalar analogue of `Kakeya.ComparableWith`:
`x` and `y` are comparable with named one-sided constants.  Unlike `ComparableWith`, this is for
single `ℝ≥0` quantities rather than scale-dependent functions. -/
def ComparableScalarsWith (C₁ C₂ x y : ℝ≥0) : Prop :=
  x ≤ C₁ * y ∧ y ≤ C₂ * x

/-- Symmetric scalar comparability with the same constant in both directions. -/
abbrev ComparableScalars (C x y : ℝ≥0) : Prop :=
  ComparableScalarsWith C C x y

/-- A single fibre has typical plank angle `theta`, with constant `C` and stability scale `A`.
This is the fibre-level core of GWZ Definition 6.12: the maximal plank angle of the whole fibre
is comparable to `theta`, and every subfibre keeping an `A⁻¹` fraction of the fibre still has
comparable maximal angle. -/
def IsTypicalPlankFibre {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ι → Plank a b hab hb1) (theta C A : ℝ≥0) (F : Finset ι) : Prop :=
  ComparableScalars C theta (maxPlankAngle P F) ∧
    ∀ t ⊆ F, A⁻¹ * (F.card : ℝ≥0) ≤ (t.card : ℝ≥0) →
      ComparableScalars C theta (maxPlankAngle P t)

/-- The plank version of GWZ Definition 6.12. A family has typical angle `theta` if every
shaded point fibre `𝒫_Y(x)` is a typical plank fibre. -/
def IsTypicalPlankAngle {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) (theta C A : ℝ≥0) : Prop :=
  ∀ x ∈ ⋃ i ∈ s, (Y i).shade,
    IsTypicalPlankFibre P theta C A (shadeFibre s Y x)

/-- **The one-sided angle hypothesis actually consumed by the slab layer.** Every shade fibre has
maximal plank angle at most `C · theta`.

This is strictly weaker than `IsTypicalPlankAngle`: it drops both the lower bound
`theta ≤ C · M(fibre)` and the stability clause, and consequently carries no stability scale `A`.
Isolating it matters, because it is *monotone* under shrinking the family
(`HasMaxPlankAngleBound.mono`), whereas the two-sided predicate is not: the lower bound can be
destroyed by deleting planks, and restoring it needs a pointwise fibre-retention hypothesis. Every
consumer in the slab-mass chain (`usedSlab_normals_confined_cap`,
`inSlabFamilyC_normal_and_center_confined`, and hence `slab_pointwise_overlap_le` and
`slabMassDecomposition`) uses only this bound, via `angularClustering`. -/
def HasMaxPlankAngleBound {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) (theta C : ℝ≥0) : Prop :=
  ∀ x ∈ ⋃ i ∈ s, (Y i).shade, maxPlankAngle P (shadeFibre s Y x) ≤ C * theta

/-- A typical plank angle bounds the maximal plank angle: the second half of the fibre-level
`ComparableScalars`. -/
theorem IsTypicalPlankAngle.hasMaxPlankAngleBound {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {P : ι → Plank a b hab hb1} {theta C A : ℝ≥0}
    (h : IsTypicalPlankAngle s Y P theta C A) : HasMaxPlankAngleBound s Y P theta C :=
  fun x hx => (h x hx).1.2

/-- **The stability scale of a typical fibre is antitone: the larger scale is the stronger
predicate (extra69, `note:typicalPlankScaleMono`).**

The scale `A` occurs in `Kakeya.IsTypicalPlankFibre` in exactly one place, inversely, in the
sub-fibre threshold `A⁻¹ * F.card ≤ t.card`.  A larger `A` therefore has a *smaller* threshold and
constrains *more* sub-fibres `t`, so the predicate at `A₂` implies the one at `A₁` whenever
`A₁ ≤ A₂`.

The positivity hypothesis is not cosmetic.  Inversion in `ℝ≥0` sends `0` to `0`, so at `A₁ = 0` the
threshold would collapse to `0 ≤ t.card`, admitting `t = ∅`, and `maxPlankAngle P ∅ = 0` would force
`theta = 0`.

This is what lets a construction produce stability at a convenient *reserve* scale — for instance a
fixed multiple of `plankAngleScaleA a ^ 2` — spend part of it on a deletion, and still deliver the
public conclusion at the smaller scale for free. -/
theorem IsTypicalPlankFibre.mono_scale {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {P : ι → Plank a b hab hb1} {theta C A₁ A₂ : ℝ≥0} {F : Finset ι}
    (hA₁ : 0 < A₁) (hA : A₁ ≤ A₂) (h : IsTypicalPlankFibre P theta C A₂ F) :
    IsTypicalPlankFibre P theta C A₁ F := by
  refine ⟨h.1, ?_⟩
  intro t ht hcard
  have hA₂_inv_le_A₁_inv : A₂⁻¹ ≤ A₁⁻¹ := inv_anti₀ hA₁ hA
  have hcard' : A₂⁻¹ * (F.card : ℝ≥0) ≤ (t.card : ℝ≥0) :=
    calc
      A₂⁻¹ * (F.card : ℝ≥0) ≤ A₁⁻¹ * (F.card : ℝ≥0) :=
        mul_le_mul_of_nonneg_right hA₂_inv_le_A₁_inv (by positivity)
      _ ≤ (t.card : ℝ≥0) := hcard
  exact h.2 t ht hcard'

/-- **The stability scale of a typical angle is antitone (extra69,
`note:typicalPlankScaleMono`).**  The family-level form of `Kakeya.IsTypicalPlankFibre.mono_scale`,
applied at every point of the shading union. -/
theorem IsTypicalPlankAngle.mono_scale {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {P : ι → Plank a b hab hb1} {theta C A₁ A₂ : ℝ≥0}
    (hA₁ : 0 < A₁) (hA : A₁ ≤ A₂) (h : IsTypicalPlankAngle s Y P theta C A₂) :
    IsTypicalPlankAngle s Y P theta C A₁ := by
  intro x hx
  exact (h x hx).mono_scale hA₁ hA

/-- The fibre level set `{x | 𝒫_Y(x) = F}` is measurable: for `F ⊆ s` it is a finite
intersection of shadings and complements; otherwise it is empty. -/
theorem measurableSet_shadeFibre_eq {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E]
    [MeasureSpace E] (s : Finset ι) (Y : ι → ShadedBody E) (F : Finset ι) :
    MeasurableSet {x : E | shadeFibre s Y x = F} := by
  classical
  by_cases hFs : F ⊆ s
  · have heq : {x : E | shadeFibre s Y x = F}
        = ⋂ j ∈ s, (if j ∈ F then (Y j).shade else (Y j).shadeᶜ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hx j hj
        split_ifs with hjF
        · exact ((mem_shadeFibre s Y x j).mp (hx ▸ hjF)).2
        · intro hxs; exact hjF (hx ▸ (mem_shadeFibre s Y x j).mpr ⟨hj, hxs⟩)
      · intro hx
        ext j
        rw [mem_shadeFibre]
        constructor
        · rintro ⟨hjs, hxs⟩
          by_contra hjF
          have := hx j hjs; rw [if_neg hjF] at this; exact this hxs
        · intro hjF
          exact ⟨hFs hjF, by have := hx j (hFs hjF); rwa [if_pos hjF] at this⟩
    rw [heq]
    refine MeasurableSet.biInter s.countable_toSet fun j _ => ?_
    split_ifs
    · exact (Y j).measurableSet_shade
    · exact (Y j).measurableSet_shade.compl
  · have heq : {x : E | shadeFibre s Y x = F} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx; exact hFs (hx ▸ Finset.filter_subset _ _)
    rw [heq]; exact MeasurableSet.empty

/-- Any function of the fibre `x ↦ g (𝒫_Y(x))` into a countable space is measurable, since the
fibre map takes finitely many values (`F ⊆ s`) with measurable level sets. -/
theorem measurable_fibreComp {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E]
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (s : Finset ι) (Y : ι → ShadedBody E) (g : Finset ι → α) :
    Measurable (fun x => g (shadeFibre s Y x)) := by
  classical
  refine measurable_to_countable' fun y => ?_
  have heq : (fun x => g (shadeFibre s Y x)) ⁻¹' {y}
      = ⋃ F ∈ s.powerset.filter (fun F => g F = y), {x : E | shadeFibre s Y x = F} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq,
      Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro hx; exact ⟨shadeFibre s Y x, ⟨Finset.filter_subset _ _, hx⟩, rfl⟩
    · rintro ⟨F, ⟨_, hgF⟩, hxF⟩; rw [hxF]; exact hgF
  rw [heq]
  exact MeasurableSet.biUnion (Finset.countable_toSet _)
    fun F _ => measurableSet_shadeFibre_eq s Y F

/-- The stopping-time *step scale* `A = exp(√(log a⁻¹))` of GWZ §6 (`extra6.tex`). For `0 < a < 1`
one has `log a⁻¹ > 0`, hence `A > 1`. -/
def plankAngleScaleA (a : ℝ≥0) : ℝ := Real.exp (Real.sqrt (Real.log (a : ℝ)⁻¹))

/-- The stopping-time *stop scale* `B = exp((log a⁻¹) ^ (3/4))` of GWZ §6 (`extra6.tex`). For
`0 < a < 1` one has `log a⁻¹ > 0`, hence `B > 1`, and moreover `Aᴺ ≪ B` and `Bᴺ ≪ a⁻¹` for every
fixed `N`. -/
def plankAngleScaleB (a : ℝ≥0) : ℝ := Real.exp ((Real.log (a : ℝ)⁻¹) ^ (3 / 4 : ℝ))

theorem one_lt_plankAngleScaleA {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) :
    1 < plankAngleScaleA a := by
  rw [plankAngleScaleA, Real.one_lt_exp_iff]
  exact Real.sqrt_pos.mpr (log_inv_pos ha ha1)

theorem one_lt_plankAngleScaleB {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) :
    1 < plankAngleScaleB a := by
  rw [plankAngleScaleB, Real.one_lt_exp_iff]
  exact Real.rpow_pos_of_pos (log_inv_pos ha ha1) _

/-- **Monotonicity of `M` (extra6, `lem:maxPlankAngleMono`).**
If `t ⊆ t'`, then `M(t) = maxPlankAngle P t ≤ maxPlankAngle P t' = M(t')`: the maximal effective
plank angle is monotone under inclusion of the index set. -/
theorem maxPlankAngle_mono {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ι → Plank a b hab hb1) {t t' : Finset ι} (h : t ⊆ t') :
    maxPlankAngle P t ≤ maxPlankAngle P t' :=
  Finset.sup_mono (Finset.product_subset_product h h)

open scoped Classical in
/-- **The angle bound survives any refinement.** Shrinking the index set and the shadings shrinks
every shade fibre, and `maxPlankAngle` is monotone, so the upper bound is inherited for free. This
is what lets the slab layer be applied after an arbitrary deletion, with no pointwise
fibre-retention hypothesis; the two-sided `IsTypicalPlankAngle` has no such property. -/
theorem HasMaxPlankAngleBound.mono {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s s₂ : Finset ι} {Y Y₂ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {P : ι → Plank a b hab hb1} {theta C : ℝ≥0}
    (hs₂ : s₂ ⊆ s) (hY₂ : ∀ i ∈ s₂, (Y₂ i).shade ⊆ (Y i).shade)
    (h : HasMaxPlankAngleBound s Y P theta C) : HasMaxPlankAngleBound s₂ Y₂ P theta C := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have hxU : x ∈ ⋃ i ∈ s, (Y i).shade :=
    Set.mem_iUnion₂.mpr ⟨i, hs₂ hi, hY₂ i hi hxi⟩
  refine le_trans (maxPlankAngle_mono P ?_) (h x hxU)
  intro j hj
  rw [mem_shadeFibre] at hj ⊢
  exact ⟨hs₂ hj.1, hY₂ j hj.1 hj.2⟩

/-- **Range of `M` (extra6, `lem:maxPlankAngleBounds`).**
If `t` is nonempty, then `a / b ≤ M(t) ≤ 1`: the maximal effective plank angle of a nonempty
fibre lies in `[a/b, 1]` (the effective angle is floored at `a/b` and capped at `1`). -/
theorem maxPlankAngle_mem_Icc {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : ι → Plank a b hab hb1) {t : Finset ι} (ht : t.Nonempty) :
    a / b ≤ maxPlankAngle P t ∧ maxPlankAngle P t ≤ 1 := by
  obtain ⟨i, hi⟩ := ht
  exact ⟨(le_effectivePlankAngle (P i) (P i)).trans
      (le_maxAngle (ang := fun i j => effectivePlankAngle (P i) (P j)) hi hi),
    maxAngle_le fun i _ j _ => effectivePlankAngle_le_one (P i) (P j)⟩

/-- **Angular clustering** (`lem:angularClustering`).
If the maximal pairwise `effectivePlankAngle` over a finite set `t` of planks is at most `C₀θ`,
then every pair of indices in `t` has `effectivePlankAngle ≤ C₀θ`. Equivalently, the unit normals
to the long planes of all planks in `t` lie within a single spherical cap of radius `C₀θ` about
the normal of any chosen reference plank.

This is the formal counterpart of `\ref{lem:angularClustering}`:
given a point `x` with `maxPlankAngle P (shadeFibre s Y x) ≤ C₀θ`, for any two planks `i, j`
through `x` we have `effectivePlankAngle (P i) (P j) ≤ C₀θ`. -/
theorem angularClustering {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {P : ι → Plank a b hab hb1} {t : Finset ι} {C₀θ : ℝ≥0}
    (hmax : maxPlankAngle P t ≤ C₀θ) {i j : ι} (hi : i ∈ t) (hj : j ∈ t) :
    effectivePlankAngle (P i) (P j) ≤ C₀θ :=
  le_trans (le_maxAngle (ang := fun i j => effectivePlankAngle (P i) (P j)) hi hj) hmax

/-- **Step-count estimate (extra6, `lem:stepCount`).**
Let `0 < a < 1` and `k : ℕ`. If `B ^ (-k) ≥ a` (equivalently `(B ^ k)⁻¹ ≥ a`), then `A ^ k ≤ B`,
where `A = plankAngleScaleA a` and `B = plankAngleScaleB a`. This bounds the number of
stopping-time steps. -/
theorem stepCount {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) (k : ℕ)
    (hk : (a : ℝ) ≤ (plankAngleScaleB a ^ k)⁻¹) :
    plankAngleScaleA a ^ k ≤ plankAngleScaleB a := by
  have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have ha1' : (a:ℝ) < 1 := by exact_mod_cast ha1
  simp only [plankAngleScaleA, plankAngleScaleB] at hk ⊢
  set t : ℝ := Real.log (a:ℝ)⁻¹ with ht
  have htpos : 0 < t := by
    rw [ht, Real.log_inv]
    have : Real.log (a:ℝ) < 0 := Real.log_neg hapos ha1'
    linarith
  have hloga : Real.log (a:ℝ) = -t := by rw [ht, Real.log_inv]; ring
  have hae : (a:ℝ) = Real.exp (-t) := by rw [← hloga, Real.exp_log hapos]
  -- Convert the hypothesis to the exponent inequality `k · t^(3/4) ≤ t`.
  rw [hae, ← Real.exp_nat_mul, ← Real.exp_neg, Real.exp_le_exp] at hk
  have hcore : (k:ℝ) * t ^ (3/4:ℝ) ≤ t := by linarith
  -- Reduce the goal to `k · t^(1/2) ≤ t^(3/4)`.
  rw [← Real.exp_nat_mul, Real.exp_le_exp, Real.sqrt_eq_rpow]
  -- Algebra on rpow exponents.
  have t_eq : t ^ (3/4:ℝ) * t ^ (1/4:ℝ) = t := by
    rw [← Real.rpow_add htpos]; norm_num
  have p_eq : t ^ (1/4:ℝ) * t ^ (1/2:ℝ) = t ^ (3/4:ℝ) := by
    rw [← Real.rpow_add htpos]; norm_num
  have p34pos : 0 < t ^ (3/4:ℝ) := Real.rpow_pos_of_pos htpos _
  have h2 : (k:ℝ) * t ^ (3/4:ℝ) ≤ t ^ (1/4:ℝ) * t ^ (3/4:ℝ) := by
    rw [mul_comm (t ^ (1/4:ℝ)) (t ^ (3/4:ℝ)), t_eq]; exact hcore
  have hk14 : (k:ℝ) ≤ t ^ (1/4:ℝ) := le_of_mul_le_mul_right h2 p34pos
  calc (k:ℝ) * t ^ (1/2:ℝ)
      ≤ t ^ (1/4:ℝ) * t ^ (1/2:ℝ) :=
        mul_le_mul_of_nonneg_right hk14 (Real.rpow_pos_of_pos htpos _).le
    _ = t ^ (3/4:ℝ) := p_eq

/-- **`log a⁻¹` is dominated by the first angle scale, with no smallness threshold (extra69,
`note:reserveScaleConstant`).**

With `t = log a⁻¹` and `u = √t`, the quadratic lower bound for the exponential at `u` gives
`u ^ 2 / 2 ≤ exp u`, that is `t ≤ 2 * plankAngleScaleA a`.  No hypothesis on `a` is needed at all:
where `t ≤ 0` the left side is nonpositive and the right side is a positive exponential, since
`Real.sqrt` of a negative number is `0`.

This is the threshold-free replacement for the route through `Kakeya.logloss_ge_Ainv`, whose
existential `a₀` was one of the absolute smallness hypotheses on the live path of GWZ Lemma 6.13. -/
theorem log_inv_le_two_mul_plankAngleScaleA (a : ℝ≥0) :
    Real.log (a : ℝ)⁻¹ ≤ 2 * plankAngleScaleA a := by
  set t := Real.log (a : ℝ)⁻¹ with ht
  set u := Real.sqrt t with hu
  have hA : plankAngleScaleA a = Real.exp u := by
    rw [plankAngleScaleA, hu, ht]
  by_cases ht_nonpos : t ≤ 0
  · -- Case 1: `t ≤ 0`. Then `Real.log (a:ℝ)⁻¹ = t ≤ 0`, and `2 * plankAngleScaleA a > 0`, done.
    have hpos : 0 < 2 * plankAngleScaleA a := by
      have : 0 < plankAngleScaleA a := Real.exp_pos _
      nlinarith
    linarith
  · -- Case 2: `0 ≤ t`. Then `u = √t ≥ 0` and `u ^ 2 = t`.
    have ht_nonneg : 0 ≤ t := by linarith
    have hu_nonneg : 0 ≤ u := Real.sqrt_nonneg _
    have h_sq : u ^ 2 = t := Real.sq_sqrt ht_nonneg
    -- Using `Real.quadratic_le_exp_of_nonneg`: `1 + u + u^2/2 ≤ exp u`.
    have h_quad : 1 + u + u ^ 2 / 2 ≤ Real.exp u :=
      Real.quadratic_le_exp_of_nonneg hu_nonneg
    have h_ineq : t / 2 ≤ Real.exp u := by
      -- From `1 + u + u^2/2 ≤ exp u`, we have `u^2/2 ≤ exp u`.
      nlinarith
    calc
      t = t := rfl
      _ = 2 * (t / 2) := by ring
      _ ≤ 2 * Real.exp u := by
        nlinarith
      _ = 2 * plankAngleScaleA a := by rw [hA]

/-- **The dyadic pigeonhole length is dominated by the first angle scale, at every scale (extra69,
`note:reserveScaleConstant`).**

Fix packing data `(Cpack, D)` before `a` and `K`.  Then there is `Cres > 0`, depending only on
`(Cpack, D)`, such that for *every* `0 < a < 1` and every `K` with `K ≤ Cpack · a ^ (-D)` one has
`⌊log₂ K⌋ + 1 ≤ Cres · plankAngleScaleA a`.

There is no smallness threshold `a < a₀` anywhere in the statement, in contrast to
`Kakeya.logloss_ge_Ainv`.  The proof is the composition of the affine bound
`Kakeya.natLog_succ_le_affine_log_inv_of_cap` with the threshold-free
`Kakeya.log_inv_le_two_mul_plankAngleScaleA`, taking `Cres = α + 2β` with
`α = log (max Cpack 1) / log 2 + 1` and `β = D / log 2`; the constants are deliberately crude. -/
theorem exists_natLog_succ_le_mul_plankAngleScaleA (Cpack : ℝ) (D : ℕ) :
    ∃ Cres : ℝ, 0 < Cres ∧ ∀ {a : ℝ≥0}, 0 < a → a < 1 → ∀ K : ℕ,
      (K : ℝ) ≤ Cpack * (a : ℝ) ^ (-(D : ℝ)) →
        (Nat.log 2 K : ℝ) + 1 ≤ Cres * plankAngleScaleA a := by
  set C1 := max Cpack 1 with hC1
  have hC1pos : 1 ≤ C1 := le_max_right _ _
  have hCpack_le : Cpack ≤ C1 := le_max_left _ _
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogC1_nonneg : 0 ≤ Real.log C1 := Real.log_nonneg hC1pos
  set α := Real.log C1 / Real.log 2 + 1 with hα
  set β := (D : ℝ) / Real.log 2 with hβ
  have hα_nonneg : 0 ≤ α := by
    have hdiv_nonneg : 0 ≤ Real.log C1 / Real.log 2 :=
      div_nonneg hlogC1_nonneg hlog2pos.le
    nlinarith
  have hα_ge_one : 1 ≤ α := by
    have hdiv_nonneg : 0 ≤ Real.log C1 / Real.log 2 :=
      div_nonneg hlogC1_nonneg hlog2pos.le
    nlinarith
  have hβ_nonneg : 0 ≤ β :=
    div_nonneg (by exact_mod_cast Nat.zero_le D) hlog2pos.le
  refine ⟨α + 2 * β, by nlinarith, ?_⟩
  intro a ha ha1 K hK
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha1' : (a : ℝ) < 1 := by exact_mod_cast ha1
  -- weaken the cap to C1
  have hK_cap : (K : ℝ) ≤ C1 * (a : ℝ) ^ (-(D : ℝ)) := by
    have hpos : 0 ≤ (a : ℝ) ^ (-(D : ℝ)) := (Real.rpow_nonneg ha_pos.le _)
    calc
      (K : ℝ) ≤ Cpack * (a : ℝ) ^ (-(D : ℝ)) := hK
      _ ≤ C1 * (a : ℝ) ^ (-(D : ℝ)) := mul_le_mul_of_nonneg_right hCpack_le hpos
  -- apply the affine bound
  have h_affine : (Nat.log 2 K : ℝ) + 1 ≤ α + β * Real.log (a : ℝ)⁻¹ := by
    have htemp := natLog_succ_le_affine_log_inv_of_cap hC1pos D ha_pos ha1' hK_cap
    simpa [hα, hβ] using htemp
  -- apply log_inv_le_two_mul_plankAngleScaleA
  have h_log_inv : Real.log (a : ℝ)⁻¹ ≤ 2 * plankAngleScaleA a :=
    log_inv_le_two_mul_plankAngleScaleA a
  have hA_ge_one : 1 ≤ plankAngleScaleA a := by
    have h := one_lt_plankAngleScaleA ha ha1
    exact h.le
  -- final arithmetic
  calc
    (Nat.log 2 K : ℝ) + 1 ≤ α + β * Real.log (a : ℝ)⁻¹ := h_affine
    _ ≤ α + β * (2 * plankAngleScaleA a) := by
      nlinarith
    _ = α + (2 * β) * plankAngleScaleA a := by ring
    _ ≤ α * plankAngleScaleA a + (2 * β) * plankAngleScaleA a := by
      nlinarith
    _ = (α + 2 * β) * plankAngleScaleA a := by ring

/-- **Typical angle on one fibre (extra6, `lem:typicalAngleFibre`).**
Let `0 < a < 1`, `a ≤ b ≤ 1`, and let `F` be a nonempty fibre of `a × b × 1` planks. With
`A = plankAngleScaleA a`, `B = plankAngleScaleB a`, and `M = maxPlankAngle P`, there are a typical
angle `θ ∈ [a/b, 1]` and a subset `G ⊆ F` such that:
(i) `|G| ≥ B⁻¹ |F|` (hence `|G| ⪆ |F|`);
(ii) `M(G) = θ`;
(iii) every `H ⊆ G` with `|H| ≥ A⁻¹ |G|` satisfies `B⁻¹ θ ≤ M(H) ≤ θ` (hence `M(H) ≈ θ`). -/
theorem typicalAngleFibre {a b : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
    (P : ι → Plank a b hab hb1) (F : Finset ι) (hF : F.Nonempty) :
    ∃ (θ : ℝ≥0) (G : Finset ι), G ⊆ F ∧ G.Nonempty ∧
      a / b ≤ θ ∧ θ ≤ 1 ∧
      (plankAngleScaleB a)⁻¹ * (F.card : ℝ) ≤ (G.card : ℝ) ∧
      maxPlankAngle P G = θ ∧
      (∀ ⦃H : Finset ι⦄, H ⊆ G →
        (plankAngleScaleA a)⁻¹ * (G.card : ℝ) ≤ (H.card : ℝ) →
          (plankAngleScaleB a)⁻¹ * (θ : ℝ) ≤ (maxPlankAngle P H : ℝ) ∧
            (maxPlankAngle P H : ℝ) ≤ (θ : ℝ)) := by
  set A := plankAngleScaleA a with hA_def
  set B := plankAngleScaleB a with hB_def
  have hA : 1 < A := one_lt_plankAngleScaleA ha ha1
  have hB : 1 < B := one_lt_plankAngleScaleB ha ha1
  have hApos : (0:ℝ) < A := by linarith
  have hBpos : (0:ℝ) < B := by linarith
  set M : Finset ι → ℝ := fun S => (maxPlankAngle P S : ℝ) with hM_def
  have hbpos : (0:ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hbpos
  -- Lower bound `m₀ = a/b > 0`.
  have hm₀ : (0:ℝ) < ((a / b : ℝ≥0) : ℝ) := by
    have : (0:ℝ≥0) < a / b := div_pos ha hbpos
    exact_mod_cast this
  have hMlb : ∀ ⦃S : Finset ι⦄, S ⊆ F → S.Nonempty → ((a / b : ℝ≥0) : ℝ) ≤ M S :=
    fun S _ hSne => by exact_mod_cast (maxPlankAngle_mem_Icc P hSne).1
  obtain ⟨k, G, hGF, hGne, hcardF, hMchain, hterm⟩ :=
    stoppingTimeChain F hF hA hB M hm₀ hMlb
  have hIcc := maxPlankAngle_mem_Icc P hGne
  refine ⟨maxPlankAngle P G, G, hGF, hGne, hIcc.1, hIcc.2, ?_, rfl, ?_⟩
  · -- `B⁻¹ |F| ≤ |G|`, via `A^k ≤ B` (stepCount) and `|G| ≥ A⁻ᵏ |F|`.
    have hb1R : (b:ℝ) ≤ 1 := by exact_mod_cast hb1
    have haR : (0:ℝ) ≤ (a:ℝ) := a.coe_nonneg
    have ha_le_div : (a:ℝ) ≤ (a:ℝ) / (b:ℝ) := by
      rw [le_div_iff₀ hbR]; exact mul_le_of_le_one_right haR hb1R
    have hm0_le : (a:ℝ) ≤ M G := by
      have h1 := hMlb hGF hGne
      have hcast : ((a / b : ℝ≥0) : ℝ) = (a:ℝ) / (b:ℝ) := by push_cast; ring
      rw [hcast] at h1; linarith [ha_le_div, h1]
    have hMF_le : M F ≤ 1 := by exact_mod_cast (maxPlankAngle_mem_Icc P hF).2
    have hBk_pos : (0:ℝ) < (B ^ k)⁻¹ := by positivity
    have ha_le : (a:ℝ) ≤ (B ^ k)⁻¹ := by
      have h2 : (B ^ k)⁻¹ * M F ≤ (B ^ k)⁻¹ * 1 := mul_le_mul_of_nonneg_left hMF_le hBk_pos.le
      rw [mul_one] at h2; linarith [hm0_le, hMchain, h2]
    have hstep : A ^ k ≤ B := stepCount ha ha1 k ha_le
    have hAk : (0:ℝ) < A ^ k := by positivity
    have hBinv_le : B⁻¹ ≤ (A ^ k)⁻¹ := by rw [inv_le_inv₀ hBpos hAk]; exact hstep
    calc B⁻¹ * (F.card : ℝ)
        ≤ (A ^ k)⁻¹ * (F.card : ℝ) := mul_le_mul_of_nonneg_right hBinv_le (by positivity)
      _ ≤ (G.card : ℝ) := hcardF
  · intro H hHG hHcard
    exact ⟨hterm hHG hHcard, by exact_mod_cast maxPlankAngle_mono P hHG⟩

/-! ### The reserve stability scale `κ · A(a)²` (extra69) -/

/-- **A priori bound on the stopping time (extra69, `rem:stepCountLe`).**
The step-count bound behind `Kakeya.stepCount`, isolated so that it can be used for scales other
than `plankAngleScaleA a`.  If `k` steps have been taken and the angle spent is still at least `a`,
i.e. `(a : ℝ) ≤ (plankAngleScaleB a ^ k)⁻¹`, then `k ≤ (log a⁻¹) ^ (1/4)`.

The hypothesis involves *only* the stop scale `plankAngleScaleB a`, never the step scale.  That is
what makes the bound non-circular: the stopping-time chain's angle clause
`M G ≤ (B ^ k)⁻¹ * M F` together with `a ≤ M G` and `M F ≤ 1` supplies it, so `k` is bounded before
any statement about the step scale is made. -/
theorem stepCount_le {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) (k : ℕ)
    (hk : (a : ℝ) ≤ (plankAngleScaleB a ^ k)⁻¹) :
    (k : ℝ) ≤ (Real.log (a : ℝ)⁻¹) ^ (1/4 : ℝ) := by
  have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have ha1' : (a:ℝ) < 1 := by exact_mod_cast ha1
  simp only [plankAngleScaleB] at hk
  set t : ℝ := Real.log (a:ℝ)⁻¹ with ht
  have htpos : 0 < t := by
    rw [ht, Real.log_inv]
    have : Real.log (a:ℝ) < 0 := Real.log_neg hapos ha1'
    linarith
  have hae : (a:ℝ) = Real.exp (-t) := by
    have hloga : Real.log (a:ℝ) = -t := by rw [ht, Real.log_inv]; ring
    rw [← hloga, Real.exp_log hapos]
  rw [hae, ← Real.exp_nat_mul, ← Real.exp_neg, Real.exp_le_exp] at hk
  have hcore : (k:ℝ) * t ^ (3/4:ℝ) ≤ t := by linarith
  have t_eq : t ^ (3/4:ℝ) * t ^ (1/4:ℝ) = t := by
    rw [← Real.rpow_add htpos]; norm_num
  have p34pos : 0 < t ^ (3/4:ℝ) := Real.rpow_pos_of_pos htpos _
  have h2 : (k:ℝ) * t ^ (3/4:ℝ) ≤ t ^ (1/4:ℝ) * t ^ (3/4:ℝ) := by
    rw [mul_comm (t ^ (1/4:ℝ)) (t ^ (3/4:ℝ)), t_eq]; exact hcore
  have hk14 : (k:ℝ) ≤ t ^ (1/4:ℝ) := le_of_mul_le_mul_right h2 p34pos
  simpa [ht] using hk14

/-- The **reserve stability scale** `R(a) = κ · A(a)²` of extra69, with `A = plankAngleScaleA`.
For a fixed `κ ≥ 1` chosen before every geometric datum, this is the scale at which the sub-fibre
stability clause is *produced*, so that one factor of `A(a)` may be spent on a lossy fibre deletion
and the public conclusion still be delivered at `A(a)`
(see `Kakeya.IsTypicalPlankAngle.mono_scale`).
Taking `κ = C_res` from `Kakeya.exists_natLog_succ_le_mul_plankAngleScaleA` makes the deletion
affordable with no smallness hypothesis on `a`. -/
def plankReserveScale (kappa : ℝ) (a : ℝ≥0) : ℝ :=
  kappa * (plankAngleScaleA a * plankAngleScaleA a)

/-- The **extra retention loss** paid for running the stopping-time chain at the reserve scale
`Kakeya.plankReserveScale kappa a` rather than at `plankAngleScaleA a`.

Running the chain at the pair `(R, B)` retains an `(R ^ k)⁻¹`-fraction, and the a priori step bound
`k ≤ (log a⁻¹) ^ (1/4)` of `Kakeya.stepCount_le` gives
`R ^ k = κ ^ k · (A ^ k) ^ 2 ≤ B · (exp((log κ)² / 2) · A · B)`.  So the full retained fraction is
`(plankAngleScaleB a * plankReserveLoss kappa a)⁻¹`, and this definition names the second factor:
the `B` already present in the unsquared selection is kept separate so that the absorption of the
loss into an `a ^ ε` budget reuses `Kakeya.refineConst_bound_uniform` verbatim on the first factor.

The constant `exp((log κ)² / 2)` comes from `log κ · (log a⁻¹) ^ (1/4) ≤ (log κ)²/2 + √(log a⁻¹)/2`,
which is why no comparison between `A(a)` and `B(a)` — and hence no smallness threshold on `a` — is
needed anywhere. -/
def plankReserveLoss (kappa : ℝ) (a : ℝ≥0) : ℝ :=
  Real.exp ((Real.log kappa) ^ 2 / 2) * (plankAngleScaleA a * plankAngleScaleB a)

/-- The reserve scale exceeds `1`, for every `κ ≥ 1` and every `0 < a < 1`. -/
theorem one_lt_plankReserveScale {kappa : ℝ} (hkappa : 1 ≤ kappa) {a : ℝ≥0}
    (ha : 0 < a) (ha1 : a < 1) : 1 < plankReserveScale kappa a := by
  rw [plankReserveScale]
  have hA : 1 < plankAngleScaleA a := one_lt_plankAngleScaleA ha ha1
  have hA_sq : 1 < plankAngleScaleA a * plankAngleScaleA a := by nlinarith
  nlinarith

/-- **The reserve threshold is below the plain angular threshold** (extra69).

`(plankReserveScale kappa a)⁻¹ ≤ (plankAngleScaleA a)⁻¹` for every `κ ≥ 1` and every `0 < a < 1`,
since `plankReserveScale kappa a = κ · A(a) ²` and `A(a) > 1` give `A(a) ≤ κ · A(a) ²`.

This is the threshold bridge that lets the reserve-scale form of GWZ Lemma 6.11
(`Kakeya.findingTypicalAngleOfIntersection_stable_reserve`) imply the plain form
(`Kakeya.findingTypicalAngleOfIntersection`): a sub-fibre retaining an `A(a)⁻¹`-fraction of its
fibre retains a fortiori a `(plankReserveScale kappa a)⁻¹`-fraction, so the reserve stability clause
constrains strictly more sub-fibres than the plain clause asserts about.  Compare
`Plank.max_two_plankAngleScaleA_le_plankReserveScale`, which is the same comparison for the output
scale `max 2 (plankAngleScaleA a)` and therefore needs `κ ≥ 2`. -/
theorem plankReserveScale_inv_le_plankAngleScaleA_inv {kappa : ℝ} (hkappa : 1 ≤ kappa) {a : ℝ≥0}
    (ha : 0 < a) (ha1 : a < 1) :
    (plankReserveScale kappa a)⁻¹ ≤ (plankAngleScaleA a)⁻¹ := by
  have hA : 1 < plankAngleScaleA a := one_lt_plankAngleScaleA ha ha1
  have hApos : 0 < plankAngleScaleA a := by linarith
  have hRpos : 0 < plankReserveScale kappa a := by
    have h := one_lt_plankReserveScale hkappa ha ha1
    linarith
  apply (inv_le_inv₀ hRpos hApos).2
  rw [plankReserveScale]
  nlinarith

/-- The reserve loss is positive, with no hypothesis on `κ` or `a`. -/
theorem plankReserveLoss_pos (kappa : ℝ) (a : ℝ≥0) : 0 < plankReserveLoss kappa a := by
  rw [plankReserveLoss, plankAngleScaleA, plankAngleScaleB]
  positivity

/-- The reserve loss is at least `1`, for every `κ ≥ 1` and every `0 < a < 1`. -/
theorem one_le_plankReserveLoss {kappa : ℝ} (_hkappa : 1 ≤ kappa) {a : ℝ≥0}
    (ha : 0 < a) (ha1 : a < 1) : 1 ≤ plankReserveLoss kappa a := by
  rw [plankReserveLoss]
  have h_exp : 1 ≤ Real.exp ((Real.log kappa) ^ 2 / 2) := by
    refine Real.one_le_exp ?_
    positivity
  have hA : 1 < plankAngleScaleA a := one_lt_plankAngleScaleA ha ha1
  have hB : 1 < plankAngleScaleB a := one_lt_plankAngleScaleB ha ha1
  have hAB : 1 ≤ plankAngleScaleA a * plankAngleScaleB a := by nlinarith
  calc
    (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ Real.exp ((Real.log kappa) ^ 2 / 2) * (plankAngleScaleA a * plankAngleScaleB a) :=
      mul_le_mul h_exp hAB (by norm_num) (by positivity)

/-- **The reserve multiplier costs only one factor of `A(a)` (extra69, `rem:powLeMulScaleA`).**
For `κ ≥ 1` and `k ≤ (log a⁻¹) ^ (1/4)`, one has `κ ^ k ≤ exp((log κ)² / 2) · plankAngleScaleA a`.

Proof: `κ ^ k = exp(k · log κ)` and `k · log κ ≤ s · log κ ≤ (log κ)²/2 + s²/2` with
`s = (log a⁻¹) ^ (1/4)`, by `xy ≤ (x² + y²)/2`; and `s² = √(log a⁻¹)`, so
`exp(s²/2) ≤ exp(√(log a⁻¹)) = plankAngleScaleA a`.  This is the step where a naive bound would
have compared `A(a)` with `B(a)` and picked up a smallness threshold. -/
theorem pow_le_mul_plankAngleScaleA {kappa : ℝ} (hkappa : 1 ≤ kappa) {a : ℝ≥0}
    (ha : 0 < a) (ha1 : a < 1) {k : ℕ} (hk : (k : ℝ) ≤ (Real.log (a : ℝ)⁻¹) ^ (1 / 4 : ℝ)) :
    kappa ^ k ≤ Real.exp ((Real.log kappa) ^ 2 / 2) * plankAngleScaleA a := by
  set t := Real.log (a : ℝ)⁻¹ with ht
  set s := t ^ (1/4 : ℝ) with hs
  set c := Real.log kappa with hc
  have htpos : 0 < t := log_inv_pos ha ha1
  have hs_nonneg : 0 ≤ s := Real.rpow_nonneg htpos.le _
  have hc_nonneg : 0 ≤ c := Real.log_nonneg hkappa
  have hkappa_pos : 0 < kappa := by linarith
  have hkapow_pos : 0 < kappa ^ k := pow_pos hkappa_pos k
  have hkapow_exp : kappa ^ k = Real.exp ((k : ℝ) * c) := by
    calc
      kappa ^ k = Real.exp (Real.log (kappa ^ k)) := (Real.exp_log hkapow_pos).symm
      _ = Real.exp ((k : ℝ) * Real.log kappa) := by rw [Real.log_pow kappa k]
      _ = Real.exp ((k : ℝ) * c) := by rw [hc]
  have hk_s : (k : ℝ) ≤ s := by
    rw [hs, ht]
    exact hk
  have hkc : (k : ℝ) * c ≤ s * c :=
    mul_le_mul_of_nonneg_right hk_s hc_nonneg
  have h_amgm : s * c ≤ c ^ 2 / 2 + s ^ 2 / 2 := by
    have h_sq_nonneg : 0 ≤ (s - c) ^ 2 := sq_nonneg _
    nlinarith
  have h_sq_eq_sqrt : s ^ 2 = Real.sqrt t := by
    calc
      s ^ 2 = s ^ (2 : ℝ) := by norm_num
      _ = (t ^ (1/4 : ℝ)) ^ (2 : ℝ) := by rw [hs]
      _ = t ^ ((1/4 : ℝ) * (2 : ℝ)) := by rw [Real.rpow_mul htpos.le]
      _ = t ^ (1/2 : ℝ) := by ring_nf
      _ = Real.sqrt t := by rw [Real.sqrt_eq_rpow]
  have h_sqrt_nonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have h_total : (k : ℝ) * c ≤ c ^ 2 / 2 + Real.sqrt t := by
    calc
      (k : ℝ) * c ≤ s * c := hkc
      _ ≤ c ^ 2 / 2 + s ^ 2 / 2 := h_amgm
      _ = c ^ 2 / 2 + (Real.sqrt t) / 2 := by rw [h_sq_eq_sqrt]
      _ ≤ c ^ 2 / 2 + Real.sqrt t := by nlinarith
  calc
    kappa ^ k = Real.exp ((k : ℝ) * c) := hkapow_exp
    _ ≤ Real.exp (c ^ 2 / 2 + Real.sqrt t) := Real.exp_le_exp.mpr h_total
    _ = Real.exp (c ^ 2 / 2) * Real.exp (Real.sqrt t) := by rw [Real.exp_add]
    _ = Real.exp ((Real.log kappa) ^ 2 / 2) * Real.exp (Real.sqrt t) := by rw [hc]
    _ = Real.exp ((Real.log kappa) ^ 2 / 2) * plankAngleScaleA a := by
      rw [plankAngleScaleA, ht]

/-- **Step-count estimate at the reserve scale (extra69, `rem:plankReserveScalePowLe`).**
For `κ ≥ 1`, `0 < a < 1` and `k` with `(a : ℝ) ≤ (plankAngleScaleB a ^ k)⁻¹`,
`plankReserveScale kappa a ^ k ≤ plankAngleScaleB a * plankReserveLoss kappa a`.

This is the reserve-scale analogue of `Kakeya.stepCount`: `R ^ k = κ ^ k · (A ^ k) ^ 2`, and
`A ^ k ≤ B` by `Kakeya.stepCount` while `κ ^ k ≤ exp((log κ)²/2) · A` by
`Kakeya.pow_le_mul_plankAngleScaleA` and `Kakeya.stepCount_le`. -/
theorem plankReserveScale_pow_le {kappa : ℝ} (hkappa : 1 ≤ kappa) {a : ℝ≥0}
    (ha : 0 < a) (ha1 : a < 1) (k : ℕ) (hk : (a : ℝ) ≤ (plankAngleScaleB a ^ k)⁻¹) :
    plankReserveScale kappa a ^ k ≤ plankAngleScaleB a * plankReserveLoss kappa a := by
  set A := plankAngleScaleA a with hA
  set B := plankAngleScaleB a with hB
  set E := Real.exp ((Real.log kappa) ^ 2 / 2) with hE
  have hApos : 0 < A := Real.exp_pos _
  have hBpos : 0 < B := Real.exp_pos _
  have hA_nonneg : 0 ≤ A := hApos.le
  have hB_nonneg : 0 ≤ B := hBpos.le
  have hA_pow_nonneg : 0 ≤ A ^ k := pow_nonneg hA_nonneg k
  have hkappa_nonneg : 0 ≤ kappa := by linarith
  have hkappa_pow_nonneg : 0 ≤ kappa ^ k := pow_nonneg hkappa_nonneg k
  have hE_nonneg : 0 ≤ E := Real.exp_pos _ |>.le
  have hA_pow_sq_nonneg : 0 ≤ A ^ k * A ^ k := mul_nonneg hA_pow_nonneg hA_pow_nonneg
  have hEA_nonneg : 0 ≤ E * A := mul_nonneg hE_nonneg hA_nonneg
  have hstep : A ^ k ≤ B := stepCount ha ha1 k hk
  have hstepCount_le : (k : ℝ) ≤ (Real.log (a : ℝ)⁻¹) ^ (1/4 : ℝ) := stepCount_le ha ha1 k hk
  have hkappa_pow : kappa ^ k ≤ E * A := pow_le_mul_plankAngleScaleA hkappa ha ha1 hstepCount_le
  have hA_pow_sq : A ^ k * A ^ k ≤ B * B :=
    mul_le_mul hstep hstep hA_pow_nonneg hB_nonneg
  calc
    plankReserveScale kappa a ^ k = (kappa * (A * A)) ^ k := rfl
    _ = kappa ^ k * (A * A) ^ k := by rw [mul_pow]
    _ = kappa ^ k * (A ^ k * A ^ k) := by rw [mul_pow]
    _ ≤ (E * A) * (B * B) := by
      apply mul_le_mul hkappa_pow hA_pow_sq hA_pow_sq_nonneg hEA_nonneg
    _ = B * (E * (A * B)) := by ring
    _ = B * plankReserveLoss kappa a := by
      rw [plankReserveLoss, hA, hB, hE]
    _ = plankAngleScaleB a * plankReserveLoss kappa a := by rfl

/-- **The reserve loss is sub-polynomial (extra69, `rem:plankReserveLossLeRpow`).**
For every `κ` and every `ε > 0` there is `C > 0`, depending only on `(κ, ε)`, with
`plankReserveLoss kappa a ≤ C * a ^ (-ε)` for every `0 < a < 1`.

Proof: `Kakeya.subpolyExp` at `α = 1/2` and `α = 3/4`, each with `ε / 2`, bounds the two factors
`plankAngleScaleA a` and `plankAngleScaleB a`; the `κ`-dependent constant is inert, which is why no
hypothesis on `κ` is needed here (the reserve route uses this at `κ ≥ 1`). -/
theorem plankReserveLoss_le_rpow (kappa : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ≥0, 0 < a → a < 1 →
      plankReserveLoss kappa a ≤ C * (a : ℝ) ^ (-ε) := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨C1, hC1pos, hC1⟩ := subpolyExp (α := 1/2) (by norm_num) (by norm_num) hε2
  obtain ⟨C2, hC2pos, hC2⟩ := subpolyExp (α := 3/4) (by norm_num) (by norm_num) hε2
  set C := Real.exp ((Real.log kappa) ^ 2 / 2) * (C1 * C2) with hC_def
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro a ha ha1
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha1R : (a : ℝ) < 1 := by exact_mod_cast ha1
  have hA : plankAngleScaleA a ≤ C1 * (a : ℝ) ^ (-(ε / 2)) := by
    rw [plankAngleScaleA, Real.sqrt_eq_rpow]
    exact hC1 (a : ℝ) haR ha1R
  have hB : plankAngleScaleB a ≤ C2 * (a : ℝ) ^ (-(ε / 2)) := by
    rw [plankAngleScaleB]
    exact hC2 (a : ℝ) haR ha1R
  have hprod : (plankAngleScaleA a : ℝ) * (plankAngleScaleB a : ℝ)
      ≤ (C1 * (a : ℝ) ^ (-(ε / 2))) * (C2 * (a : ℝ) ^ (-(ε / 2))) := by
    have hposB : 0 ≤ plankAngleScaleB a := (Real.exp_pos _).le
    have hposC1 : 0 ≤ C1 * (a : ℝ) ^ (-(ε / 2)) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg haR.le _)
    refine mul_le_mul hA hB hposB hposC1
  have h_rpow_add : (a : ℝ) ^ (-(ε / 2)) * (a : ℝ) ^ (-(ε / 2)) = (a : ℝ) ^ (-ε) := by
    calc
      (a : ℝ) ^ (-(ε / 2)) * (a : ℝ) ^ (-(ε / 2)) = (a : ℝ) ^ (-(ε / 2) + (-(ε / 2))) := by
        rw [Real.rpow_add haR (-(ε / 2)) (-(ε / 2))]
      _ = (a : ℝ) ^ (-ε) := by ring_nf
  have hcomb : (C1 * (a : ℝ) ^ (-(ε / 2))) * (C2 * (a : ℝ) ^ (-(ε / 2))) = (C1 * C2) * (a : ℝ) ^
      (-ε) := by
    calc
      (C1 * (a : ℝ) ^ (-(ε / 2))) * (C2 * (a : ℝ) ^ (-(ε / 2))) = (C1 * C2) * ((a : ℝ) ^ (-(ε /
          2)) * (a : ℝ) ^ (-(ε / 2))) := by ring
      _ = (C1 * C2) * (a : ℝ) ^ (-ε) := by rw [h_rpow_add]
  calc
    plankReserveLoss kappa a = Real.exp ((Real.log kappa) ^ 2 / 2) * (plankAngleScaleA a *
        plankAngleScaleB a) := rfl
    _ ≤ Real.exp ((Real.log kappa) ^ 2 / 2) * ((C1 * (a : ℝ) ^ (-(ε / 2))) * (C2 * (a : ℝ) ^
        (-(ε / 2)))) := by
      refine mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = Real.exp ((Real.log kappa) ^ 2 / 2) * ((C1 * C2) * (a : ℝ) ^ (-ε)) := by rw [hcomb]
    _ = (Real.exp ((Real.log kappa) ^ 2 / 2) * (C1 * C2)) * (a : ℝ) ^ (-ε) := by ring
    _ = C * (a : ℝ) ^ (-ε) := rfl

/-- **Typical angle on one fibre at the reserve scale (extra69, `rem:typicalAngleFibreReserve`).**

The variant of `Kakeya.typicalAngleFibre` whose stability clause (iii) is asked at the *reserve*
threshold `(plankReserveScale kappa a)⁻¹ = (κ · A(a)²)⁻¹`, for a `κ ≥ 1` fixed before the fibre.
Since the threshold is smaller than `(plankAngleScaleA a)⁻¹` and than `(A(a) · A(a))⁻¹`, strictly
more sub-fibres `H ⊆ G` are constrained: this is a strengthening of `Kakeya.typicalAngleFibre`, and
it is *not* obtainable from it by monotonicity, which runs the other way.

There is no smallness hypothesis on `a`.  `Kakeya.stoppingTimeChain` takes both of its scales as
arguments and requires no relation between them, so it is run at the pair
`(plankReserveScale kappa a, plankAngleScaleB a)`.  Only the retained fraction of clause (i) pays:
it degrades from `B⁻¹` to `(B · plankReserveLoss kappa a)⁻¹`, by
`Kakeya.plankReserveScale_pow_le`.  The comparability constant of clause (iii) is still
`B = plankAngleScaleB a`, unchanged.

The step count is bounded a priori and without circularity by `Kakeya.stepCount_le`, whose only
input is the chain's angle clause `M G ≤ (B ^ k)⁻¹ * M F` together with `a / b ≤ M G` and
`M F ≤ 1` — none of which mentions the step scale. -/
theorem typicalAngleFibre_reserve {kappa : ℝ} (hkappa : 1 ≤ kappa)
    {a b : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
    (P : ι → Plank a b hab hb1) (F : Finset ι) (hF : F.Nonempty) :
    ∃ (θ : ℝ≥0) (G : Finset ι), G ⊆ F ∧ G.Nonempty ∧
      a / b ≤ θ ∧ θ ≤ 1 ∧
      (plankAngleScaleB a * plankReserveLoss kappa a)⁻¹ * (F.card : ℝ) ≤ (G.card : ℝ) ∧
      maxPlankAngle P G = θ ∧
      (∀ ⦃H : Finset ι⦄, H ⊆ G →
        (plankReserveScale kappa a)⁻¹ * (G.card : ℝ) ≤ (H.card : ℝ) →
          (plankAngleScaleB a)⁻¹ * (θ : ℝ) ≤ (maxPlankAngle P H : ℝ) ∧
            (maxPlankAngle P H : ℝ) ≤ (θ : ℝ)) := by
  set A := plankAngleScaleA a with hA_def
  set B := plankAngleScaleB a with hB_def
  set R := plankReserveScale kappa a with hR_def
  set L := plankReserveLoss kappa a with hL_def
  have hA : 1 < A := one_lt_plankAngleScaleA ha ha1
  have hB : 1 < B := one_lt_plankAngleScaleB ha ha1
  have hApos : (0:ℝ) < A := by linarith
  have hBpos : (0:ℝ) < B := by linarith
  have hR : 1 < R := one_lt_plankReserveScale hkappa ha ha1
  set M : Finset ι → ℝ := fun S => (maxPlankAngle P S : ℝ) with hM_def
  have hbpos : (0:ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hbpos
  -- Lower bound `m₀ = a/b > 0`.
  have hm₀ : (0:ℝ) < ((a / b : ℝ≥0) : ℝ) := by
    have : (0:ℝ≥0) < a / b := div_pos ha hbpos
    exact_mod_cast this
  have hMlb : ∀ ⦃S : Finset ι⦄, S ⊆ F → S.Nonempty → ((a / b : ℝ≥0) : ℝ) ≤ M S :=
    fun S _ hSne => by exact_mod_cast (maxPlankAngle_mem_Icc P hSne).1
  obtain ⟨k, G, hGF, hGne, hcardF, hMchain, hterm⟩ :=
    stoppingTimeChain F hF hR hB M hm₀ hMlb
  have hIcc := maxPlankAngle_mem_Icc P hGne
  refine ⟨maxPlankAngle P G, G, hGF, hGne, hIcc.1, hIcc.2, ?_, rfl, ?_⟩
  · -- `(B * L)⁻¹ * (F.card : ℝ) ≤ (G.card : ℝ)`, via `R ^ k ≤ B * L` (plankReserveScale_pow_le)
    -- and `|G| ≥ (R ^ k)⁻¹ * |F|` (from stoppingTimeChain at scale pair (R, B)).
    have hb1R : (b:ℝ) ≤ 1 := by exact_mod_cast hb1
    have haR : (0:ℝ) ≤ (a:ℝ) := a.coe_nonneg
    have ha_le_div : (a:ℝ) ≤ (a:ℝ) / (b:ℝ) := by
      rw [le_div_iff₀ hbR]; exact mul_le_of_le_one_right haR hb1R
    have hm0_le : (a:ℝ) ≤ M G := by
      have h1 := hMlb hGF hGne
      have hcast : ((a / b : ℝ≥0) : ℝ) = (a:ℝ) / (b:ℝ) := by push_cast; ring
      rw [hcast] at h1; linarith [ha_le_div, h1]
    have hMF_le : M F ≤ 1 := by exact_mod_cast (maxPlankAngle_mem_Icc P hF).2
    have hBk_pos : (0:ℝ) < (B ^ k)⁻¹ := by positivity
    have ha_le : (a:ℝ) ≤ (B ^ k)⁻¹ := by
      have h2 : (B ^ k)⁻¹ * M F ≤ (B ^ k)⁻¹ * 1 := mul_le_mul_of_nonneg_left hMF_le hBk_pos.le
      rw [mul_one] at h2; linarith [hm0_le, hMchain, h2]
    have hRk : R ^ k ≤ B * L := plankReserveScale_pow_le hkappa ha ha1 k ha_le
    have hBLpos : (0:ℝ) < B * L := mul_pos hBpos (plankReserveLoss_pos kappa a)
    have hRk_pos : (0:ℝ) < R ^ k := by
      have hRpos : 0 < R := by linarith
      positivity
    have hBLinv_le : (B * L)⁻¹ ≤ (R ^ k)⁻¹ := by
      rw [inv_le_inv₀ hBLpos hRk_pos]
      exact hRk
    calc
      (B * L)⁻¹ * (F.card : ℝ) ≤ (R ^ k)⁻¹ * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_right hBLinv_le (by positivity)
      _ ≤ (G.card : ℝ) := hcardF
  · intro H hHG hHcard
    exact ⟨hterm hHG hHcard, by exact_mod_cast maxPlankAngle_mono P hHG⟩

end Kakeya

end
