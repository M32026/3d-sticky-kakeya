/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.Sticky
public import Kakeya.Tube.Basic
public import Kakeya.Uniform
public import Kakeya.MultiScaleFac.Bridge
public import Kakeya.MultiScaleLoss -- for the `_root_.StickyKakeya` namespace below

/-!
# Transport across one grid gap

Comparing a quantity at a real scale with the same quantity at the neighbouring grid scale.  Half
(A) pays a volume ratio for it, half (B) gets it for free, and the two are put side by side here
because that contrast is the point: the Frostman constant is a ratio whose denominator moves with
the container, while `Kakeya.maxDensity` is an absolute functional of the index set.

Sliced out of the former `DividingScalesA` and `DividingScalesKT`, together with the algebra of
`Kakeya.MultiScaleFac.scaleGapLoss` that both sides charge the transport to.
-/

@[expose] public section

open MeasureTheory Real Metric
open scoped Topology

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Transport of a Frostman constant across one grid gap

The stopping time of GWZ p. 28--29 descends to arbitrary *real* scales `ρ`, while the hierarchy
carried by the amended Lemma 7.7(A) lives on the grid `σ k = gridScale δ (ssfGridLen δ) k`.  Moving
a Frostman constant between a real scale and the grid scales bracketing it is what the following
lemmas do.  Two facts make the move cheap, and both are specific to the `⌈log log 1/δ⌉` grid:

* the containers at the two scales have comparable volumes, the ratio being at most
  `(σ k / σ (k+1)) ^ (n - 1) = δ ^ (-(n-1)/⌈log log 1/δ⌉)`, that is
  `Kakeya.MultiScaleFac.scaleGapLoss (n - 1) δ`, which is subpolynomial;
* the *family* need not change, so no count ratio is paid: the transports below compare the
  Frostman constants of one and the same family of nodes in two containers.

`Kakeya.MultiScaleFac.card_mul_frostmanConstant_nodesIn_le` is the remaining, genuinely
family-changing half of GWZ's chain estimate, and there the count ratio is displayed rather than
estimated, because across a container *inclusion* it is not bounded by geometry alone.

The container at the real scale is an arbitrary `ρ`-tube, not a dilate of a node.  That is
legitimate because a `Tube` carries `dist_eq_one`: a `ρ`-tube containing a node lies inside the
`4ρ`-dilate of that node (`Tube.rescale_le_of_le`), and a dilation by a dimensional factor costs
only a dimensional constant here, since the transports pay a *volume ratio* and not a count. -/

section ScaleGapTransport

variable {ι : Type*}

/-- **The dimensional constant of the scale-gap transports.**  A tube of radius `r ≤ 4` has volume
between `Tube.le_volume.c n * r ^ (n - 1)` and `5 * Tube.volume_le.C n * r ^ (n - 1)`; this is the
ratio of the two bounds.  Allowing `r ≤ 4` is what lets a container be the `4ρ`-dilate of a node. -/
noncomputable def scaleGapVolConst (n : ℕ) : NNReal :=
  5 * Tube.volume_le.C n / Tube.le_volume.c n

omit [Nontrivial E] in
/-- **A subfamily in a smaller container has the smaller `maxDensity`,** read through
`ConvexSpaceBody.frostmanConstant_eq_maxDensity_div`: both sides of the conclusion are the
`Kakeya.maxDensity` of the respective family whenever the corresponding density is positive, and
both vanish when it is not. -/
private theorem frostmanConstant_mul_densityIn_le_of_subset {t u : Finset ι}
    {W : ι → ConvexSpaceBody E} {K₁ K₂ : ConvexSpaceBody E} (htu : t ⊆ u)
    (h₁ : ∀ i ∈ t, W i ≤ K₁) (h₂ : ∀ i ∈ u, W i ≤ K₂) :
    ConvexSpaceBody.frostmanConstant t W K₁ * Kakeya.densityIn t W K₁
      ≤ ConvexSpaceBody.frostmanConstant u W K₂ * Kakeya.densityIn u W K₂ := by
  rcases eq_or_ne (Kakeya.densityIn t W K₁) 0 with hd | hd
  · simp [hd]
  · calc
      ConvexSpaceBody.frostmanConstant t W K₁ * Kakeya.densityIn t W K₁
          = Kakeya.maxDensity t W := by
        rw [ConvexSpaceBody.frostmanConstant_eq_maxDensity_div (pos_iff_ne_zero.mpr hd) h₁,
          ENNReal.div_mul_cancel hd (Kakeya.densityIn_ne_top t W K₁)]
      _ ≤ Kakeya.maxDensity u W := Kakeya.maxDensity_mono W htu
      _ ≤ _ := (ConvexSpaceBody.isFrostmanIn_frostmanConstant).maxDensity_le_of_carrier_subset h₂

/-- Every level-`b` node is a tube of the exact radius `σ b`, so the total volume of the nodes
inside a container is at least the count times the lower tube-volume bound. -/
private theorem card_mul_le_sum_volume_nodesIn {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (b : ℕ) (K : ConvexSpaceBody E) :
    ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
        * ((𝒰.nodesIn b K).card : ENNReal)
      ≤ ∑ j' ∈ 𝒰.nodesIn b K, volume (𝒰.cover.tube b j').carrier := by
  classical
  have hconst : ∀ j' ∈ 𝒰.nodesIn b K,
      ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
        ≤ volume (𝒰.cover.tube b j').carrier := fun j' _ => by
    rw [← ENNReal.coe_pow, ← ENNReal.coe_mul]
    exact Tube.le_volume (𝒰.cover.tube b j')
  rw [mul_comm _ ((𝒰.nodesIn b K).card : ENNReal), ← nsmul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ hconst

/-- The companion upper bound of `Kakeya.MultiScaleFac.card_mul_le_sum_volume_nodesIn`. -/
private theorem sum_volume_nodesIn_le_card_mul {δ : NNReal} (hδ1 : δ ≤ 1) {s : Finset ι}
    {T : ι → Tube δ E} {Cu : NNReal} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (b : ℕ)
    (K : ConvexSpaceBody E) :
    ∑ j' ∈ 𝒰.nodesIn b K, volume (𝒰.cover.tube b j').carrier
      ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
        * ((𝒰.nodesIn b K).card : ENNReal) := by
  classical
  have hconst : ∀ j' ∈ 𝒰.nodesIn b K, volume (𝒰.cover.tube b j').carrier
      ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) :=
    fun j' _ => by
      simpa [ENNReal.coe_mul, ENNReal.coe_pow] using
        Tube.volume_le (gridScale_le_one hδ1 (ssfGridLen δ) b) (𝒰.cover.tube b j')
  rw [mul_comm _ ((𝒰.nodesIn b K).card : ENNReal), ← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ hconst

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Members of `𝒰.nodesIn b K` lie in `K` by definition. -/
private theorem nodesIn_le_container {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (b : ℕ) (K : ConvexSpaceBody E) :
    ∀ j' ∈ 𝒰.nodesIn b K, (𝒰.cover.tube b j').toConvexSpaceBody ≤ K :=
  fun j' hj' => ((𝒰.mem_nodesIn_iff b K j').mp hj').2

/-- The count form of the density in a container, lower half. -/
private theorem card_mul_le_densityIn_mul_volume {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (b : ℕ) (K : ConvexSpaceBody E) :
    ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
        * ((𝒰.nodesIn b K).card : ENNReal)
      ≤ Kakeya.densityIn (𝒰.nodesIn b K) (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K
          * volume K.carrier := by
  rw [← Kakeya.sum_volume_eq_densityIn_mul_volume' (nodesIn_le_container 𝒰 b K)]
  exact card_mul_le_sum_volume_nodesIn 𝒰 b K

/-- The count form of the density in a container, upper half. -/
private theorem densityIn_mul_volume_le_card_mul_nodes {δ : NNReal} (hδ1 : δ ≤ 1) {s : Finset ι}
    {T : ι → Tube δ E} {Cu : NNReal} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (b : ℕ)
    (K : ConvexSpaceBody E) :
    Kakeya.densityIn (𝒰.nodesIn b K) (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K
        * volume K.carrier
      ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
        * ((𝒰.nodesIn b K).card : ENNReal) := by
  rw [← Kakeya.sum_volume_eq_densityIn_mul_volume' (nodesIn_le_container 𝒰 b K)]
  exact sum_volume_nodesIn_le_card_mul hδ1 𝒰 b K

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Nodes inside a container are nodes inside any larger container**
(blueprint `lem:ktNodesInMono`). -/
theorem nodesIn_subset_of_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T N Cu) (b : ℕ) {K₁ K₂ : ConvexSpaceBody E}
    (hK : K₁ ≤ K₂) : 𝒰.nodesIn b K₁ ⊆ 𝒰.nodesIn b K₂ := fun j' hj' =>
  (𝒰.mem_nodesIn_iff b K₂ j').mpr
    (((𝒰.mem_nodesIn_iff b K₁ j').mp hj').imp_right (·.trans hK))

/-- The shape of GWZ's chain estimate, as pure `ENNReal` arithmetic: a lower bound for the small
family's count against its density, the Frostman-times-density comparison, and an upper bound for
the large family's density against its count compose without any cancellation. -/
private theorem mul_le_mul_of_densityIn_chain {a₁ a₂ d₁ d₂ F₁ F₂ v : ENNReal}
    (h₁ : a₁ ≤ d₁ * v) (h₂ : F₁ * d₁ ≤ F₂ * d₂) (h₃ : d₂ * v ≤ a₂) : a₁ * F₁ ≤ a₂ * F₂ := by
  calc a₁ * F₁ ≤ d₁ * v * F₁ := mul_le_mul_left h₁ F₁
    _ = F₁ * d₁ * v := (mul_comm _ _).trans (mul_assoc _ _ _).symm
    _ ≤ F₂ * d₂ * v := mul_le_mul_left h₂ v
    _ ≤ a₂ * F₂ := by rw [mul_comm a₂, mul_assoc]; exact mul_le_mul_right h₃ F₂

/-- **GWZ's chain estimate across a container inclusion** (p. 29), the family-changing half.  For
`K₁ ≤ K₂` the level-`b` nodes inside `K₁` form a subfamily of those inside `K₂`, and the two
Frostman constants are compared with the *count* ratio displayed, division-free.  The count ratio is
displayed rather than estimated because geometry alone does not bound it. -/
theorem card_mul_frostmanConstant_nodesIn_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) {b : ℕ} {K₁ K₂ : ConvexSpaceBody E}
    (hK : K₁ ≤ K₂) :
    ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((𝒰.nodesIn b K₁).card : ENNReal)
        * ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K₁)
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K₁
      ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((𝒰.nodesIn b K₂).card : ENNReal)
        * ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K₂)
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K₂ := by
  classical
  have hp0 : ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal)
      ^ (Module.finrank ℝ E - 1) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (gridScale_pos hδ (ssfGridLen δ) b).ne')
  have hptop : ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal)
      ^ (Module.finrank ℝ E - 1) ≠ ⊤ := by
    rw [← ENNReal.coe_pow]; exact ENNReal.coe_ne_top
  set W : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube b j').toConvexSpaceBody
  set p : ENNReal :=
    ((gridScale δ (ssfGridLen δ) b : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
  set cv : ENNReal := ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
  set Cv : ENNReal := ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
  set card₁ : ENNReal := ((𝒰.nodesIn b K₁).card : ENNReal)
  set card₂ : ENNReal := ((𝒰.nodesIn b K₂).card : ENNReal)
  set d₁ : ENNReal := Kakeya.densityIn (𝒰.nodesIn b K₁) W K₁
  set d₂ : ENNReal := Kakeya.densityIn (𝒰.nodesIn b K₂) W K₂
  set F₁ : ENNReal := ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K₁) W K₁
  set F₂ : ENNReal := ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K₂) W K₂
  have h₁ : cv * p * card₁ ≤ d₁ * volume K₂.carrier :=
    (card_mul_le_densityIn_mul_volume 𝒰 b K₁).trans
      (mul_le_mul_right (measure_mono hK) d₁)
  have h₂ : F₁ * d₁ ≤ F₂ * d₂ :=
    frostmanConstant_mul_densityIn_le_of_subset (nodesIn_subset_of_le 𝒰 b hK)
      (nodesIn_le_container 𝒰 b K₁) (nodesIn_le_container 𝒰 b K₂)
  have h₃ : d₂ * volume K₂.carrier ≤ Cv * p * card₂ :=
    densityIn_mul_volume_le_card_mul_nodes hδ1 𝒰 b K₂
  refine (ENNReal.mul_le_mul_iff_right hp0 hptop).mp ?_
  calc
    p * (cv * card₁ * F₁) = (cv * p * card₁) * F₁ := by ring
    _ ≤ (Cv * p * card₂) * F₂ := mul_le_mul_of_densityIn_chain h₁ h₂ h₃
    _ = p * (Cv * card₂ * F₂) := by ring

end ScaleGapTransport

/-! ### Node maximal density against node counts inside a container -/

/-! ### Transport across one grid gap

Half (A) pays a ratio of volumes whenever it changes the container of a Frostman constant, because
that container sits in the denominator.  Half (B) pays nothing: a container enters a
`Kakeya.maxDensity` statement only by selecting which indices are counted, and `Kakeya.maxDensity`
is monotone in the index set.  So every transport below holds with the factor `1`, and
`Kakeya.MultiScaleFac.scaleGapLoss` appears in none of them; in half (B) that factor is consumed
only by the node-count ratio, never by a change of container.  See
`blueprint/src/GWZAdapted/section9.tex`, `subsec:ktScaleGapTransport`. -/

/-! ### Transporting a coarse node density to a fine node density at a real scale

The third bullet of GWZ 7.7(B) wants its lower bound on `Kakeya.maxDensity` at the *fine* grid index
`b` and at an arbitrary real radius `ρ`, whereas the stopping time supplies one at the *coarse*
index `c`.  The transport below carries a lower bound that way at the price of one grid gap.

It is *not* the count comparison recorded as missing in blueprint
`note:nodeCountRatioAcrossContainer`, and it avoids that route deliberately.  Comparing the number
of level-`b` nodes in a container with the number of level-`c` nodes in it costs a power of `δ`
and needs a branching-ratio bound the hierarchy does not carry.  Here no count in the container is
ever mentioned.  Instead, inside a *single test body*, one level-`b` child is selected for each
level-`c` node the test body counts; the selection is injective, so the two families have the same
cardinality, and the comparison is term by term:

* a level-`c` node has volume at most `C_n σ_c^{n-1}`, a fattened level-`b` child at least
  `c_n ρ^{n-1}`, and `σ_c ≤ scaleGapLoss 1 δ · ρ` by
  `Kakeya.MultiScaleFac.gridScale_le_scaleGapLoss_mul`, which is where the one grid gap is paid;
* the test body has to be thickened by `σ_c` to hold the fattened children, and that costs only the
  dimensional factor `2^n`, because a test body counting a level-`c` node already contains a
  `σ_c`-ball; this is `Kakeya.MultiScaleFac.volume_cthickening_le_of_tube_le`.

So the whole constant is dimensional times `scaleGapLoss (n-1) δ`, with no further power of `δ`. -/

section GapDensityTransportKT

variable {ι : Type*}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Every level-`c` node of a hierarchy carries a level-`b` node inside it**, for `c ≤ b ≤ N`.
`Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent` produces a member of `s` assigned to the
coarse node, and `Kakeya.MultiScaleFac.assign_mem_nodesUnder` reads that member's level-`b` node as
one lying under it.  The member is returned too, since it makes the selection below injective. -/
private theorem exists_child_node_nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) (hs : s.Nonempty) {c b : ℕ} (hcb : c ≤ b)
    (hbN : b ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet c) :
    ∃ i ∈ s, 𝒰.cover.assign c i = j ∧ 𝒰.cover.assign b i ∈ 𝒰.nodesUnder b c j := by
  classical
  obtain ⟨i, hi⟩ := coverClass_nonempty_of_mem_parent 𝒰 (hcb.trans hbN) hs hj
  obtain ⟨his, hci⟩ : i ∈ s ∧ 𝒰.cover.assign c i = j := by simpa [coverClass] using hi
  exact ⟨i, his, hci, assign_mem_nodesUnder 𝒰 hcb hbN hi⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **One level-`b` child per level-`c` node, chosen injectively.**  The children of distinct coarse
nodes are distinct: a shared child is the level-`b` node of two members whose level-`b` assignments
agree, and iterated nestedness forces their level-`c` assignments to agree too.  Injectivity is what
lets the density comparison keep the cardinality of the coarse family. -/
theorem exists_child_selection {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) (hs : s.Nonempty) {c b : ℕ} (hcb : c ≤ b)
    (hbN : b ≤ N) (t : Finset ι) (ht : ∀ j ∈ t, j ∈ 𝒰.cover.indexSet c) :
    ∃ f : ι → ι, Set.InjOn f t ∧ ∀ j ∈ t, f j ∈ 𝒰.nodesUnder b c j := by
  classical
  have hex : ∀ j : ι, ∃ i : ι, j ∈ t →
      (i ∈ s ∧ 𝒰.cover.assign c i = j ∧ 𝒰.cover.assign b i ∈ 𝒰.nodesUnder b c j) := fun j => by
    by_cases hjt : j ∈ t
    · obtain ⟨i, his, hci, hbi⟩ := exists_child_node_nodesUnder 𝒰 hs hcb hbN (ht j hjt)
      exact ⟨i, fun _ => ⟨his, hci, hbi⟩⟩
    · exact ⟨j, fun hj => absurd hj hjt⟩
  choose g hg using hex
  refine ⟨fun j => 𝒰.cover.assign b (g j), fun j₁ hj₁ j₂ hj₂ h => ?_,
    fun j hj => (hg j hj).2.2⟩
  have hg₁ := hg j₁ (Finset.mem_coe.mp hj₁)
  have hg₂ := hg j₂ (Finset.mem_coe.mp hj₂)
  rw [← hg₁.2.1, ← hg₂.2.1]
  exact 𝒰.cover.assign_eq_of_le hcb hbN hg₁.1 hg₂.1 h

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A fattened tube sits in a thickened container.**

A `ρ`-rescale of a tube contained in `K` lies in the `r`-thickening of `K` whenever `ρ ≤ r`, and no
relation between `ρ` and the tube's own radius is needed: the rescale is the `ρ`-thickening of the
tube's core, and the core lies in `K`. -/
theorem tube_rescale_le_cthickening {σ ρ : NNReal} (P : Tube σ E) {r : ℝ} (hρr : (ρ : ℝ) ≤ r)
    {K : ConvexSpaceBody E} (hPK : P.toConvexSpaceBody ≤ K) :
    (P.rescale ρ).toConvexSpaceBody ≤ K.cthickening r := by
  have hsegP : segment ℝ P.x P.y ⊆ P.carrier := by
    rw [P.carrier_eq_cthickening]
    exact Metric.self_subset_cthickening _
  change (P.rescale ρ).carrier ⊆ Metric.cthickening r K.carrier
  rw [(P.rescale ρ).carrier_eq_cthickening]
  exact (Metric.cthickening_subset_of_subset (ρ : ℝ)
      (hsegP.trans (SetLike.coe_subset_coe.mpr hPK))).trans
    (Metric.cthickening_mono hρr K.carrier)

omit [Nontrivial E] in
/-- **The density comparison behind the transport, with all geometry abstracted away.**  `t` is the
subfamily counted on the left and `t'` a family at least as large counted on the right; the left
bodies are individually small (`vhi`), the right ones large (`vlo`), and `K''` has volume at most
`q` times that of `K'`.  Then the left density is at most `D` times the right maximal density
whenever `vhi * q ≤ D * vlo`. -/
theorem densityIn_le_mul_maxDensity_of_selection {ι' : Type*} {t t' s' : Finset ι'}
    {W W' : ι' → ConvexSpaceBody E} {K' K'' : ConvexSpaceBody E} {vlo vhi q D : ENNReal}
    (hvlo0 : vlo ≠ 0) (hvloTop : vlo ≠ ⊤)
    (hhi : ∀ j ∈ t, MeasureTheory.volume (W j).carrier ≤ vhi)
    (hlo : ∀ j' ∈ t', vlo ≤ MeasureTheory.volume (W' j').carrier)
    (hcard : t.card ≤ t'.card) (ht's' : t' ⊆ s')
    (hmem' : ∀ j' ∈ t', W' j' ≤ K'')
    (hKq : MeasureTheory.volume K''.carrier ≤ q * MeasureTheory.volume K'.carrier)
    (hD : vhi * q ≤ D * vlo) :
    Kakeya.densityIn t W K' ≤ D * Kakeya.maxDensity s' W' := by
  set M := Kakeya.maxDensity s' W'
  set V := MeasureTheory.volume K'.carrier
  have hA : (∑ j ∈ t with W j ≤ K', MeasureTheory.volume (W j).carrier) ≤
      (t.card : ENNReal) * vhi :=
    calc
      ∑ j ∈ t with W j ≤ K', MeasureTheory.volume (W j).carrier
          ≤ ∑ j ∈ t with W j ≤ K', vhi :=
            Finset.sum_le_sum fun j hj => hhi j (Finset.mem_filter.mp hj).1
      _ ≤ (t.card : ENNReal) * vhi := by
            rw [Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) vhi
  have hB : (t.card : ENNReal) * vlo ≤ M * (q * V) :=
    calc
      (t.card : ENNReal) * vlo ≤ (t'.card : ENNReal) * vlo :=
            mul_le_mul_left (Nat.cast_le.mpr hcard) vlo
      _ = ∑ _j' ∈ t', vlo := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j' ∈ t', MeasureTheory.volume (W' j').carrier := Finset.sum_le_sum hlo
      _ ≤ Kakeya.maxDensity t' W' * MeasureTheory.volume K''.carrier :=
            Kakeya.sum_volume_le_maxDensity_mul_volume' hmem'
      _ ≤ M * MeasureTheory.volume K''.carrier :=
            mul_le_mul_left (Kakeya.maxDensity_mono W' ht's') _
      _ ≤ M * (q * V) := mul_le_mul_right hKq M
  have hC : ((t.card : ENNReal) * vhi) * vlo ≤ ((D * M) * V) * vlo :=
    calc
      ((t.card : ENNReal) * vhi) * vlo = ((t.card : ENNReal) * vlo) * vhi := by ring
      _ ≤ (M * (q * V)) * vhi := mul_le_mul_left hB vhi
      _ = (vhi * q) * (M * V) := by ring
      _ ≤ (D * vlo) * (M * V) := mul_le_mul_left hD (M * V)
      _ = ((D * M) * V) * vlo := by ring
  rw [Kakeya.densityIn_le_iff]
  exact hA.trans ((ENNReal.mul_le_mul_iff_left hvlo0 hvloTop).mp hC)

end GapDensityTransportKT

end MultiScaleFac

end Kakeya

end
