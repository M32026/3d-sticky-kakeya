import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64AffineMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.RawGlobalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.GenericHierarchyAlgorithms

/-!
# The short vertical slab in Proposition 6.4

After Proposition 5.7 supplies the raw `C²` slope, Proposition 6.4 sets
`h = delta^(3 / N)` and restricts the final hierarchy shading to one exact
vertical slab of height `h`.  The pigeonhole below is performed on indexed
shaded mass, exactly as in the paper, rather than on union volume or on a
cell-padded height window.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

/-- The half-height used by the centered affine parametrization of the
paper's slab of total height `delta^(3/N)`. -/
def pureWZ2Proposition64HalfHeight (delta : ℝ) (N : ℕ) : ℝ :=
  Real.rpow delta (3 / (N : ℝ)) / 2

theorem pureWZ2Proposition64HalfHeight_pos
    {delta : ℝ} {N : ℕ} (hdelta : 0 < delta) :
    0 < pureWZ2Proposition64HalfHeight delta N := by
  unfold pureWZ2Proposition64HalfHeight
  exact div_pos (Real.rpow_pos_of_pos hdelta _) (by norm_num)

theorem pureWZ2Proposition64HalfHeight_le_one
    {delta : ℝ} {N : ℕ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    pureWZ2Proposition64HalfHeight delta N ≤ 1 := by
  unfold pureWZ2Proposition64HalfHeight
  by_cases hN : N = 0
  · simp [hN]
    norm_num
  · have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hexp : 0 ≤ (3 : ℝ) / N := by positivity
    have hpow : Real.rpow delta ((3 : ℝ) / N) ≤ 1 :=
      Real.rpow_le_one hdelta.le hdeltaOne hexp
    linarith

/-- Indexed shaded mass in an exact horizontal slab, for the paper's cropped
tube family. -/
def pureWZ2PaperMassInSlab
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) (a b : ℝ) : ENNReal :=
  ∑ index : Fin family.card,
    volume (shading.carrier index ∩ horizontalSlab a b)

/-- Finite exact-width pigeonhole on indexed paper-shading mass.  The
constant `3` is the harmless endpoint cost from covering `[-1,1]` by at most
`2/L + 1` intervals of length exactly `L`. -/
private theorem pureWZ2_exists_exact_mass_slab
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {L : ℝ} (hLpos : 0 < L) (hLone : L ≤ 1)
    (hsupport : ∀ index,
      shading.carrier index ⊆ horizontalSlab (-1 : ℝ) 1) :
    ∃ a b : ℝ,
      -1 ≤ a ∧ a < b ∧ b ≤ 1 ∧ b - a = L ∧
      ENNReal.ofReal L * shading.mass ≤
        3 * pureWZ2PaperMassInSlab shading a b := by
  let N : ℕ := Nat.floor (2 / L)
  have hNpos : 0 < N := by
    dsimp only [N]
    apply Nat.floor_pos.mpr
    have hLtwo : L ≤ 2 := hLone.trans (by norm_num)
    calc
      (1 : ℝ) = 2 / 2 := by norm_num
      _ ≤ 2 / L := by gcongr
  have hNle : (N : ℝ) ≤ 2 / L := by
    dsimp only [N]
    exact Nat.floor_le (by positivity)
  let a : ℕ → ℝ := fun k =>
    if k < N then -1 + (k : ℝ) * L else 1 - L
  let b : ℕ → ℝ := fun k =>
    if k < N then -1 + ((k : ℝ) + 1) * L else 1
  let bins : Finset ℕ := Finset.range (N + 1)
  have hbins : bins.Nonempty := by simp [bins]
  have hwindow : ∀ k ∈ bins, -1 ≤ a k ∧ b k ≤ 1 := by
    intro k hk
    have hkN : k ≤ N := by
      have : k < N + 1 := Finset.mem_range.mp hk
      omega
    by_cases h : k < N
    · have ha : a k = -1 + (k : ℝ) * L := by simp [a, h]
      have hb : b k = -1 + ((k : ℝ) + 1) * L := by simp [b, h]
      have hkp1 : (k : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast (show k + 1 ≤ N by omega)
      have hmul : ((k : ℝ) + 1) * L ≤ 2 := by
        calc
          ((k : ℝ) + 1) * L ≤ (N : ℝ) * L := by gcongr
          _ ≤ (2 / L) * L := by gcongr
          _ = 2 := by field_simp [hLpos.ne']
      rw [ha, hb]
      constructor
      · have : 0 ≤ (k : ℝ) * L := by positivity
        linarith
      · linarith
    · have hkEq : k = N := by omega
      simp [a, b, hkEq]
      linarith
  have hlength : ∀ k ∈ bins, b k - a k = L := by
    intro k hk
    have hkN : k ≤ N := by
      have : k < N + 1 := Finset.mem_range.mp hk
      omega
    by_cases h : k < N
    · simp [a, b, h]
      ring
    · have hkEq : k = N := by omega
      simp [a, b, hkEq]
  have hcover : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      ∃ k ∈ bins, z ∈ Set.Icc (a k) (b k) := by
    intro z hz
    by_cases hleft : z ≤ -1 + (N : ℝ) * L
    · by_cases heq : (z + 1) / L = (N : ℝ)
      · let k := N - 1
        have hklt : k < N := by dsimp only [k]; omega
        have hkmem : k ∈ bins := by simp [bins]; omega
        have hzEq : z = -1 + (N : ℝ) * L := by
          field_simp [hLpos.ne'] at heq ⊢
          linarith
        have hkcast : (k : ℝ) = (N : ℝ) - 1 := by
          dsimp only [k]
          rw [Nat.cast_sub (by omega : 1 ≤ N)]
          norm_num
        refine ⟨k, hkmem, ?_⟩
        simp only [a, b, if_pos hklt]
        rw [hkcast, hzEq]
        constructor <;> nlinarith [hLpos]
      · have hquotNonneg : 0 ≤ (z + 1) / L := by
          exact div_nonneg (by linarith [hz.1]) hLpos.le
        have hquotLt : (z + 1) / L < (N : ℝ) := by
          have hquotLe : (z + 1) / L ≤ (N : ℝ) := by
            apply (div_le_iff₀ hLpos).2
            linarith
          exact lt_of_le_of_ne hquotLe heq
        let k := Nat.floor ((z + 1) / L)
        have hklt : k < N := by
          have hkLe : (k : ℝ) ≤ (z + 1) / L :=
            Nat.floor_le hquotNonneg
          exact_mod_cast hkLe.trans_lt hquotLt
        have hkmem : k ∈ bins := by simp [bins]; omega
        have hkLower : (k : ℝ) * L ≤ z + 1 := by
          have := Nat.floor_le hquotNonneg
          calc
            (k : ℝ) * L ≤ ((z + 1) / L) * L := by gcongr
            _ = z + 1 := by field_simp [hLpos.ne']
        have hkUpper : z + 1 < ((k : ℝ) + 1) * L := by
          have hfloor := Nat.lt_floor_add_one ((z + 1) / L)
          calc
            z + 1 = ((z + 1) / L) * L := by field_simp [hLpos.ne']
            _ < ((k : ℝ) + 1) * L := by gcongr
        refine ⟨k, hkmem, ?_⟩
        simp only [a, b, if_pos hklt]
        constructor <;> linarith
    · have hNnot : ¬ N < N := by omega
      refine ⟨N, by simp [bins], ?_⟩
      simp only [a, b, if_neg hNnot]
      constructor
      · have hfloor : 2 / L < (N : ℝ) + 1 := by
          simpa [N] using Nat.lt_floor_add_one (2 / L)
        have hfloor' : 2 / L - 1 < (N : ℝ) := by
          linarith only [hfloor]
        have hmul : 2 - L < (N : ℝ) * L := by
          have : (2 / L - 1) * L < (N : ℝ) * L := by
            exact mul_lt_mul_of_pos_right hfloor' hLpos
          calc
            2 - L = (2 / L - 1) * L := by field_simp [hLpos.ne']
            _ < (N : ℝ) * L := this
        linarith
      · exact hz.2
  have hsumCover : shading.mass ≤
      ∑ k ∈ bins, pureWZ2PaperMassInSlab shading (a k) (b k) := by
    have hcarrier : ∀ index, volume (shading.carrier index) ≤
        ∑ k ∈ bins,
          volume (shading.carrier index ∩ horizontalSlab (a k) (b k)) := by
      intro index
      have hsubset : shading.carrier index ⊆
          ⋃ k ∈ bins, shading.carrier index ∩ horizontalSlab (a k) (b k) := by
        intro point hpoint
        have hz := hsupport index hpoint
        rcases hcover (point 2) hz with ⟨k, hk, hkslab⟩
        exact Set.mem_iUnion₂.mpr ⟨k, hk, hpoint, hkslab⟩
      exact (measure_mono hsubset).trans
        (MeasureTheory.measure_biUnion_finset_le bins _)
    calc
      shading.mass = ∑ index : Fin family.card,
          volume (shading.carrier index) := rfl
      _ ≤ ∑ index : Fin family.card, ∑ k ∈ bins,
          volume (shading.carrier index ∩ horizontalSlab (a k) (b k)) :=
        Finset.sum_le_sum fun index _ => hcarrier index
      _ = ∑ k ∈ bins, ∑ index : Fin family.card,
          volume (shading.carrier index ∩ horizontalSlab (a k) (b k)) := by
        rw [Finset.sum_comm]
      _ = ∑ k ∈ bins, pureWZ2PaperMassInSlab shading (a k) (b k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rfl
  let slabMass : ℕ → ENNReal := fun k =>
    pureWZ2PaperMassInSlab shading (a k) (b k)
  rcases Finset.exists_max_image bins slabMass hbins with
    ⟨chosen, hchosen, hmax⟩
  have hsumMax :
      ∑ k ∈ bins, pureWZ2PaperMassInSlab shading (a k) (b k) ≤
        (bins.card : ENNReal) * slabMass chosen := by
    calc
      ∑ k ∈ bins, pureWZ2PaperMassInSlab shading (a k) (b k)
          ≤ ∑ k ∈ bins, slabMass chosen := by
            apply Finset.sum_le_sum
            intro k hk
            exact hmax k hk
      _ = (bins.card : ENNReal) * slabMass chosen := by
        simp [Finset.sum_const]
  have hcardL : (bins.card : ENNReal) * ENNReal.ofReal L ≤ 3 := by
    have hcardReal : (bins.card : ℝ) = (N + 1 : ℝ) := by
      simp [bins]
    have hcardBound : (bins.card : ℝ) ≤ 3 / L := by
      rw [hcardReal]
      have hOneDiv : (1 : ℝ) ≤ 1 / L := by
        apply (le_div_iff₀ hLpos).2
        simpa using hLone
      calc
        (N + 1 : ℝ) = (N : ℝ) + 1 := by norm_num
        _ ≤ 2 / L + 1 := by linarith
        _ ≤ 2 / L + 1 / L := by linarith
        _ = 3 / L := by field_simp [hLpos.ne']; ring
    have hcardENN : (bins.card : ENNReal) ≤ ENNReal.ofReal (3 / L) := by
      rw [show (bins.card : ENNReal) =
          ENNReal.ofReal (bins.card : ℝ) by norm_cast]
      exact ENNReal.ofReal_mono hcardBound
    calc
      (bins.card : ENNReal) * ENNReal.ofReal L
          ≤ ENNReal.ofReal (3 / L) * ENNReal.ofReal L := by gcongr
      _ = ENNReal.ofReal ((3 / L) * L) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 / L)]
      _ = 3 := by
        rw [show (3 / L) * L = 3 by field_simp [hLpos.ne']]
        norm_num
  have hmass : ENNReal.ofReal L * shading.mass ≤
      3 * slabMass chosen := by
    calc
      ENNReal.ofReal L * shading.mass
          ≤ ENNReal.ofReal L * ((bins.card : ENNReal) * slabMass chosen) := by
            gcongr
            exact hsumCover.trans hsumMax
      _ = ((bins.card : ENNReal) * ENNReal.ofReal L) * slabMass chosen := by
        ring
      _ ≤ 3 * slabMass chosen := by gcongr
  exact ⟨a chosen, b chosen, (hwindow chosen hchosen).1,
    sub_pos.mp (hlength chosen hchosen ▸ hLpos),
    (hwindow chosen hchosen).2, hlength chosen hchosen, hmass⟩

/-- One slab of the exact paper height `h = delta^(3/N)`, represented by its
center and half-height. -/
structure PureWZ2Proposition64ShortSlab
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss) where
  center : ℝ
  halfHeight : ℝ :=
    pureWZ2Proposition64HalfHeight delta hierarchy.hierarchy.levelCount
  halfHeight_eq : halfHeight =
    pureWZ2Proposition64HalfHeight delta hierarchy.hierarchy.levelCount
  halfHeight_pos : 0 < halfHeight
  halfHeight_le_one : halfHeight ≤ 1
  totalHeight_eq : 2 * halfHeight =
    Real.rpow delta (3 / (hierarchy.hierarchy.levelCount : ℝ))
  source_window : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
    center + halfHeight * t ∈ Set.Icc (-1 : ℝ) 1
  slab : Set Point3 :=
    horizontalSlab (center - halfHeight) (center + halfHeight)
  slab_eq : slab =
    horizontalSlab (center - halfHeight) (center + halfHeight)
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    hierarchy.shading.carrier index ∩ slab
  subshading : PureWZ2PaperIsSubshading shading hierarchy.shading
  mass_fraction :
    ENNReal.ofReal (2 * halfHeight) * hierarchy.shading.mass ≤
      3 * shading.mass
  anchorPoint : Point3
  anchorPoint_mem : anchorPoint ∈ shading.union
  anchorHeight : ℝ := anchorPoint 2
  anchorHeight_eq : anchorHeight = anchorPoint 2
  anchorHeight_mem : anchorHeight ∈
    Set.Icc (center - halfHeight) (center + halfHeight)

namespace PureWZ2LocallyLinearHierarchyData

/-- Select the mass-heavy exact short slab used in Proposition 6.4. -/
theorem selectProposition64ShortSlab
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss) :
    Nonempty (PureWZ2Proposition64ShortSlab hierarchy) := by
  let halfHeight :=
    pureWZ2Proposition64HalfHeight delta hierarchy.hierarchy.levelCount
  let totalHeight := Real.rpow delta
    (3 / (hierarchy.hierarchy.levelCount : ℝ))
  have hhalfPos : 0 < halfHeight :=
    pureWZ2Proposition64HalfHeight_pos hierarchy.delta_pos
  have hhalfOne : halfHeight ≤ 1 :=
    pureWZ2Proposition64HalfHeight_le_one
      hierarchy.delta_pos hierarchy.delta_le_one
  have htotalEq : 2 * halfHeight = totalHeight := by
    dsimp only [halfHeight, totalHeight, pureWZ2Proposition64HalfHeight]
    ring
  have htotalPos : 0 < totalHeight := by
    exact Real.rpow_pos_of_pos hierarchy.delta_pos _
  have htotalOne : totalHeight ≤ 1 := by
    dsimp only [totalHeight]
    apply Real.rpow_le_one hierarchy.delta_pos.le hierarchy.delta_le_one
    have hNpos : 0 < (hierarchy.hierarchy.levelCount : ℝ) := by
      have hNnat : 0 < hierarchy.hierarchy.levelCount :=
        lt_of_lt_of_le (by norm_num) hierarchy.hierarchy.levelCount_two
      exact_mod_cast hNnat
    positivity
  have hsupport : ∀ index, hierarchy.shading.carrier index ⊆
      horizontalSlab (-1 : ℝ) 1 := by
    intro index point hpoint
    have hbox := paperShading_subset_axisBox
      (Z := hierarchy.shading) (show point ∈ hierarchy.shading.union from
        ⟨index, hpoint⟩)
    change -1 ≤ point 2 ∧ point 2 ≤ 1
    have hzabs : |point 2| ≤ 1 := by
      simpa using hbox.2.2
    exact abs_le.mp hzabs
  rcases pureWZ2_exists_exact_mass_slab hierarchy.shading
      htotalPos htotalOne hsupport with
    ⟨a, b, ha, hab, hb, hlength, hmass⟩
  let center := (a + b) / 2
  have haCenter : center - halfHeight = a := by
    dsimp only [center]
    rw [← htotalEq] at hlength
    linarith
  have hbCenter : center + halfHeight = b := by
    dsimp only [center]
    rw [← htotalEq] at hlength
    linarith
  let slab : Set Point3 :=
    horizontalSlab (center - halfHeight) (center + halfHeight)
  let selected : WZ1PaperTubeShading source.family :=
    { carrier := fun index => hierarchy.shading.carrier index ∩ slab
      measurable_carrier := fun index =>
        (hierarchy.shading.measurable_carrier index).inter
          (measurableSet_horizontalSlab _ _)
      subset_body := fun index => Set.inter_subset_left.trans
        (hierarchy.shading.subset_body index) }
  have hselectedMass : selected.mass =
      pureWZ2PaperMassInSlab hierarchy.shading a b := by
    dsimp only [Kakeya.Streamlined.Shading.mass, selected, slab]
    rw [haCenter, hbCenter]
    rfl
  have hsourceWindow : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      center + halfHeight * t ∈ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    have ha' : -1 ≤ center - halfHeight := by simpa [haCenter] using ha
    have hb' : center + halfHeight ≤ 1 := by simpa [hbCenter] using hb
    have hlower : -halfHeight ≤ halfHeight * t := by
      have := mul_le_mul_of_nonneg_left ht.1 hhalfPos.le
      simpa using this
    have hupper : halfHeight * t ≤ halfHeight := by
      simpa using mul_le_mul_of_nonneg_left ht.2 hhalfPos.le
    constructor <;> linarith
  have hhierarchyMassPos : 0 < hierarchy.shading.mass := by
    have hvolumePos : 0 < volume hierarchy.shading.union :=
      (show 0 < Kakeya.realRpowENN delta (sigma + finalLoss) by
        simp [Kakeya.realRpowENN, ENNReal.ofReal_pos,
          Real.rpow_pos_of_pos hierarchy.delta_pos]).trans_le
        hierarchy.volume_lower
    have hunionMass : volume hierarchy.shading.union ≤
        hierarchy.shading.mass := by
      have hunion : hierarchy.shading.union =
          ⋃ index : Fin source.family.card,
            hierarchy.shading.carrier index := by
        ext point
        change (∃ index, point ∈ hierarchy.shading.carrier index) ↔
          point ∈ ⋃ index, hierarchy.shading.carrier index
        simp
      rw [hunion]
      exact MeasureTheory.measure_iUnion_fintype_le
        volume hierarchy.shading.carrier
    exact hvolumePos.trans_le hunionMass
  have hselectedMassPos : 0 < selected.mass := by
    have hleftPos : 0 < ENNReal.ofReal (2 * halfHeight) *
        hierarchy.shading.mass :=
      ENNReal.mul_pos
        (ENNReal.ofReal_pos.mpr (by positivity)).ne'
        hhierarchyMassPos.ne'
    have hrightPos : 0 < 3 * selected.mass :=
      hleftPos.trans_le (by
        rw [htotalEq, hselectedMass]
        exact hmass)
    have hcomm : selected.mass * 3 = 3 * selected.mass := by ring
    rw [← hcomm] at hrightPos
    exact pos_of_mul_pos_left hrightPos (by norm_num : (0 : ENNReal) ≤ 3)
  have hcarrierPos : ∃ index, 0 < volume (selected.carrier index) := by
    rw [show selected.mass = ∑ index : Fin source.family.card,
      volume (selected.carrier index) from rfl] at hselectedMassPos
    rcases Finset.sum_pos_iff.mp hselectedMassPos with
      ⟨index, _hindex, hindexPos⟩
    exact ⟨index, hindexPos⟩
  rcases hcarrierPos with ⟨anchorIndex, hanchorMass⟩
  have hanchorNonempty : (selected.carrier anchorIndex).Nonempty :=
    nonempty_of_measure_ne_zero hanchorMass.ne'
  rcases hanchorNonempty with ⟨anchorPoint, hanchorPoint⟩
  have hanchorUnion : anchorPoint ∈ selected.union :=
    ⟨anchorIndex, hanchorPoint⟩
  have hanchorSlab : anchorPoint 2 ∈
      Set.Icc (center - halfHeight) (center + halfHeight) := by
    exact hanchorPoint.2
  refine ⟨{
    center := center
    halfHeight := halfHeight
    halfHeight_eq := rfl
    halfHeight_pos := hhalfPos
    halfHeight_le_one := hhalfOne
    totalHeight_eq := htotalEq
    source_window := hsourceWindow
    slab := slab
    slab_eq := rfl
    shading := selected
    carrier_eq := fun _ => rfl
    subshading := fun _ => Set.inter_subset_left
    mass_fraction := by
      rw [htotalEq, hselectedMass]
      exact hmass
    anchorPoint := anchorPoint
    anchorPoint_mem := hanchorUnion
    anchorHeight := anchorPoint 2
    anchorHeight_eq := rfl
    anchorHeight_mem := hanchorSlab }⟩

end PureWZ2LocallyLinearHierarchyData

end Kakeya.Assouad

end
