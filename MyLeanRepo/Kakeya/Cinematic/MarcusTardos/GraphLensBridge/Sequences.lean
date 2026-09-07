import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GraphLensBridge.CyclicLists
import Mathlib.Order.Interval.Set.Infinite

/-!
# Intersection-reverse moon-face sequences

This file instantiates the six-point chord argument for the graph lenses in
the PYZ closure.  The lens-face and inverse-face families are empty; all
graph-strip lenses are moon-faces.
-/

noncomputable section

namespace Kakeya.Cinematic.GraphLensBridge

open Kakeya.Cinematic

local instance : DecidableEq C2Function := Classical.decEq _
local instance : DecidableEq GraphLens := Classical.decEq _

/-- The unique host-fiber lens representing a symbol in the moon sequence. -/
def lensForSymbol (lenses : Finset GraphLens) (host symbol : C2Function)
    (hsymbol : symbol ∈ moonSequence lenses host) : GraphLens :=
  (hostedList lenses host).get
    ⟨(moonSequence lenses host).idxOf symbol, by
      rw [← List.length_map lower]
      exact List.idxOf_lt_length_of_mem hsymbol⟩

theorem lensForSymbol_mem_hosted
    (lenses : Finset GraphLens) (host symbol : C2Function)
    (hsymbol : symbol ∈ moonSequence lenses host) :
    lensForSymbol lenses host symbol hsymbol ∈ hostedLenses lenses host := by
  letI := graphLensOrder
  exact (Finset.mem_sort (· ≤ ·)).mp
    (List.get_mem (hostedList lenses host)
      ⟨(moonSequence lenses host).idxOf symbol, by
        rw [← List.length_map lower]
        exact List.idxOf_lt_length_of_mem hsymbol⟩)

theorem upper_lensForSymbol
    (lenses : Finset GraphLens) (host symbol : C2Function)
    (hsymbol : symbol ∈ moonSequence lenses host) :
    upper (lensForSymbol lenses host symbol hsymbol) = host := by
  classical
  exact (Finset.mem_filter.mp
    (lensForSymbol_mem_hosted lenses host symbol hsymbol)).2

theorem lower_lensForSymbol
    (lenses : Finset GraphLens) (host symbol : C2Function)
    (hsymbol : symbol ∈ moonSequence lenses host) :
    lower (lensForSymbol lenses host symbol hsymbol) = symbol := by
  unfold lensForSymbol
  let index : Fin (hostedList lenses host).length :=
    ⟨(moonSequence lenses host).idxOf symbol, by
      simpa [moonSequence] using List.idxOf_lt_length_of_mem hsymbol⟩
  have hmap :
      (moonSequence lenses host).get
          ⟨index, by simp [moonSequence]⟩ =
        lower ((hostedList lenses host).get index) := by
    simp [moonSequence]
  calc
    lower ((hostedList lenses host).get
        ⟨(moonSequence lenses host).idxOf symbol, by
          rw [← List.length_map lower]
          exact List.idxOf_lt_length_of_mem hsymbol⟩) =
        lower ((hostedList lenses host).get index) := by
          congr
    _ = (moonSequence lenses host).get
          ⟨(moonSequence lenses host).idxOf symbol,
            List.idxOf_lt_length_of_mem hsymbol⟩ := hmap.symm
    _ = symbol := List.idxOf_get (List.idxOf_lt_length_of_mem hsymbol)

theorem lensForSymbol_mem_lenses
    (lenses : Finset GraphLens) (host symbol : C2Function)
    (hsymbol : symbol ∈ moonSequence lenses host) :
    lensForSymbol lenses host symbol hsymbol ∈ lenses :=
  (Finset.mem_filter.mp
    (lensForSymbol_mem_hosted lenses host symbol hsymbol)).1

theorem lensForSymbol_ne_of_symbol_ne
    (lenses : Finset GraphLens) (host first second : C2Function)
    (hfirst : first ∈ moonSequence lenses host)
    (hsecond : second ∈ moonSequence lenses host)
    (hne : first ≠ second) :
    lensForSymbol lenses host first hfirst ≠
      lensForSymbol lenses host second hsecond := by
  intro h
  apply hne
  rw [← lower_lensForSymbol lenses host first hfirst,
    ← lower_lensForSymbol lenses host second hsecond, h]

theorem midpoint_lt_of_idxOf_lt
    {lenses : Finset GraphLens}
    (hnonoverlap : ∀ first ∈ lenses, ∀ second ∈ lenses,
      first ≠ second → first.Nonoverlap second)
    (host first second : C2Function)
    (hfirst : first ∈ moonSequence lenses host)
    (hsecond : second ∈ moonSequence lenses host)
    (hne : first ≠ second)
    (hidx : (moonSequence lenses host).idxOf first <
      (moonSequence lenses host).idxOf second) :
    (midpoint (lensForSymbol lenses host first hfirst) : ℝ) <
      midpoint (lensForSymbol lenses host second hsecond) := by
  letI := graphLensOrder
  let firstLens := lensForSymbol lenses host first hfirst
  let secondLens := lensForSymbol lenses host second hsecond
  have hfirstIdx :
      (moonSequence lenses host).idxOf first <
        (hostedList lenses host).length := by
    rw [← List.length_map lower]
    exact List.idxOf_lt_length_of_mem hfirst
  have hsecondIdx :
      (moonSequence lenses host).idxOf second <
        (hostedList lenses host).length := by
    rw [← List.length_map lower]
    exact List.idxOf_lt_length_of_mem hsecond
  have hsort :
      @LT.lt GraphLens graphLensOrder.toLT firstLens secondLens := by
    apply (Finset.sortedLT_sort (hostedLenses lenses host)).getElem_lt_getElem_of_lt
    exact hidx
  have hmidLe : (midpoint firstLens : ℝ) ≤ midpoint secondLens :=
    midpoint_le_of_graphLensOrder_lt hsort
  refine lt_of_le_of_ne hmidLe ?_
  intro hmid
  have hfirstMem := lensForSymbol_mem_lenses lenses host first hfirst
  have hsecondMem := lensForSymbol_mem_lenses lenses host second hsecond
  have hlensNe : firstLens ≠ secondLens :=
    lensForSymbol_ne_of_symbol_ne lenses host first second hfirst hsecond hne
  have hnon := hnonoverlap firstLens hfirstMem secondLens hsecondMem hlensNe
  apply hnon
  refine ⟨shares_upper firstLens secondLens ?_, ?_⟩
  · rw [upper_lensForSymbol lenses host first hfirst,
      upper_lensForSymbol lenses host second hsecond]
  · have hfirstLeft := left_lt_midpoint firstLens
    have hfirstRight := midpoint_lt_right firstLens
    have hsecondLeft := left_lt_midpoint secondLens
    have hsecondRight := midpoint_lt_right secondLens
    simp only [max_lt_iff, lt_min_iff]
    constructor <;> constructor <;> linarith

theorem cyclic_midpoints_of_cyclic_indices
    {lenses : Finset GraphLens}
    (hnonoverlap : ∀ first ∈ lenses, ∀ second ∈ lenses,
      first ≠ second → first.Nonoverlap second)
    (host pivot first second : C2Function)
    (hpivot : pivot ∈ moonSequence lenses host)
    (hfirst : first ∈ moonSequence lenses host)
    (hsecond : second ∈ moonSequence lenses host)
    (hpf : pivot ≠ first) (hps : pivot ≠ second)
    (hfs : first ≠ second)
    (hcyclic : CyclicLT
      ((moonSequence lenses host).idxOf pivot)
      ((moonSequence lenses host).idxOf first)
      ((moonSequence lenses host).idxOf second)) :
    CyclicLT
      (midpoint (lensForSymbol lenses host pivot hpivot) : ℝ)
      (midpoint (lensForSymbol lenses host first hfirst) : ℝ)
      (midpoint (lensForSymbol lenses host second hsecond) : ℝ) := by
  rcases hcyclic with h | h | h
  · exact Or.inl ⟨
      midpoint_lt_of_idxOf_lt hnonoverlap host pivot first hpivot hfirst hpf h.1,
      midpoint_lt_of_idxOf_lt hnonoverlap host first second hfirst hsecond hfs h.2⟩
  · exact Or.inr (Or.inl ⟨
      midpoint_lt_of_idxOf_lt hnonoverlap host first second hfirst hsecond hfs h.1,
      midpoint_lt_of_idxOf_lt hnonoverlap host second pivot hsecond hpivot
        (Ne.symm hps) h.2⟩)
  · exact Or.inr (Or.inr ⟨
      midpoint_lt_of_idxOf_lt hnonoverlap host second pivot hsecond hpivot
        (Ne.symm hps) h.1,
      midpoint_lt_of_idxOf_lt hnonoverlap host pivot first hpivot hfirst hpf h.2⟩)

/-- A point strictly inside a lens interval and outside a prescribed finite set. -/
def freshPoint (lens : GraphLens) (forbidden : Finset ℝ) : UnitPoint :=
  let witness := Classical.choose
    ((Set.Ioo_infinite lens.left_lt_right).exists_notMem_finset forbidden)
  ⟨witness, by
    have hw := (Classical.choose_spec
      ((Set.Ioo_infinite lens.left_lt_right).exists_notMem_finset forbidden)).1
    exact ⟨lens.left.property.1.trans hw.1.le,
      hw.2.le.trans lens.right.property.2⟩⟩

theorem left_lt_freshPoint (lens : GraphLens) (forbidden : Finset ℝ) :
    (lens.left : ℝ) < freshPoint lens forbidden :=
  (Classical.choose_spec
    ((Set.Ioo_infinite lens.left_lt_right).exists_notMem_finset forbidden)).1.1

theorem freshPoint_lt_right (lens : GraphLens) (forbidden : Finset ℝ) :
    (freshPoint lens forbidden : ℝ) < lens.right :=
  (Classical.choose_spec
    ((Set.Ioo_infinite lens.left_lt_right).exists_notMem_finset forbidden)).1.2

theorem freshPoint_not_mem (lens : GraphLens) (forbidden : Finset ℝ) :
    (freshPoint lens forbidden : ℝ) ∉ forbidden :=
  (Classical.choose_spec
    ((Set.Ioo_infinite lens.left_lt_right).exists_notMem_finset forbidden)).2

theorem three_intersections_of_alternates
    {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves)
    {u v : C2Function} (hu : u ∈ curves) (hv : v ∈ curves)
    (huv : u ≠ v)
    {x₁ y₁ x₂ y₂ : UnitPoint}
    (halternates : Alternates (x₁ : ℝ) y₁ x₂ y₂)
    (hx₁ : u x₁ < v x₁) (hy₁ : u y₁ < v y₁)
    (hx₂ : v x₂ < u x₂) (hy₂ : v y₂ < u y₂) : False := by
  have hthree := hfamily.1 u hu v hv huv
  rcases halternates with h | h | h | h | h | h | h | h
  all_goals
    first
    | rcases strict_zero_between h.1 (by assumption) (by assumption) with
        ⟨z₁, hz₁l, hz₁r, hz₁⟩
      rcases strict_zero_between h.2.1 (by assumption) (by assumption) with
        ⟨z₂, hz₂l, hz₂r, hz₂⟩
      rcases strict_zero_between h.2.2 (by assumption) (by assumption) with
        ⟨z₃, hz₃l, hz₃r, hz₃⟩
      have hz₁' : u z₁ = v z₁ := by simpa [eq_comm] using hz₁
      have hz₂' : u z₂ = v z₂ := by simpa [eq_comm] using hz₂
      have hz₃' : u z₃ = v z₃ := by simpa [eq_comm] using hz₃
      exact hthree z₁ z₂ z₃ (hz₁r.trans hz₂l) (hz₂r.trans hz₃l)
        hz₁' hz₂' hz₃'
    | rcases strict_zero_between h.1 (by assumption) (by assumption) with
        ⟨z₁, hz₁l, hz₁r, hz₁⟩
      rcases strict_zero_between h.2.1 (by assumption) (by assumption) with
        ⟨z₂, hz₂l, hz₂r, hz₂⟩
      rcases strict_zero_between h.2.2 (by assumption) (by assumption) with
        ⟨z₃, hz₃l, hz₃r, hz₃⟩
      have hz₁' : u z₁ = v z₁ := by simpa [eq_comm] using hz₁
      have hz₂' : u z₂ = v z₂ := by simpa [eq_comm] using hz₂
      have hz₃' : u z₃ = v z₃ := by simpa [eq_comm] using hz₃
      exact hthree z₁ z₂ z₃ (hz₁r.trans hz₂l) (hz₂r.trans hz₃l)
        hz₁' hz₂' hz₃'

private theorem point_lt_of_midpoint_lt_of_disjoint
    {first second : GraphLens} {x y : UnitPoint}
    (hmid : (midpoint first : ℝ) < midpoint second)
    (hdisjoint :
      (first.right : ℝ) ≤ second.left ∨
        (second.right : ℝ) ≤ first.left)
    (hxleft : (first.left : ℝ) < x)
    (hxright : (x : ℝ) < first.right)
    (hyleft : (second.left : ℝ) < y)
    (hyright : (y : ℝ) < second.right) :
    (x : ℝ) < y := by
  rcases hdisjoint with horder | horder
  · exact hxright.trans_le horder |>.trans hyleft
  · exfalso
    have : (midpoint second : ℝ) < midpoint first :=
      (midpoint_lt_right second).trans_le horder |>.trans
        (left_lt_midpoint first)
    linarith

private theorem upper_lt_lower_at_disjoint_lens_point
    {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves)
    {first second : GraphLens}
    (hsecondSides : second.f ∈ curves ∧ second.g ∈ curves)
    (hdisjoint :
      (first.right : ℝ) ≤ second.left ∨
        (second.right : ℝ) ≤ first.left)
    (x : UnitPoint)
    (hxleft : (first.left : ℝ) < x)
    (hxright : (x : ℝ) < first.right) :
    upper second x < lower second x := by
  rcases hdisjoint with horder | horder
  · exact upper_lt_lower_left hfamily hsecondSides x
      (hxright.trans_le horder)
  · exact upper_lt_lower_right hfamily hsecondSides x
      (horder.trans_lt hxleft)

private theorem cyclic_points_of_cyclic_midpoints
    {first second third : GraphLens}
    {x y z : UnitPoint}
    (hfirst : (first.left : ℝ) < x ∧ (x : ℝ) < first.right)
    (hsecond : (second.left : ℝ) < y ∧ (y : ℝ) < second.right)
    (hthird : (third.left : ℝ) < z ∧ (z : ℝ) < third.right)
    (hfirstSecond :
      (first.right : ℝ) ≤ second.left ∨
        (second.right : ℝ) ≤ first.left)
    (hfirstThird :
      (first.right : ℝ) ≤ third.left ∨
        (third.right : ℝ) ≤ first.left)
    (hsecondThird :
      (second.right : ℝ) ≤ third.left ∨
        (third.right : ℝ) ≤ second.left)
    (hcyclic :
      CyclicLT (midpoint first : ℝ)
        (midpoint second : ℝ) (midpoint third : ℝ)) :
    CyclicLT (x : ℝ) y z := by
  rcases hcyclic with h | h | h
  · exact Or.inl ⟨
      point_lt_of_midpoint_lt_of_disjoint h.1 hfirstSecond
        hfirst.1 hfirst.2 hsecond.1 hsecond.2,
      point_lt_of_midpoint_lt_of_disjoint h.2 hsecondThird
        hsecond.1 hsecond.2 hthird.1 hthird.2⟩
  · exact Or.inr (Or.inl ⟨
      point_lt_of_midpoint_lt_of_disjoint h.1 hsecondThird
        hsecond.1 hsecond.2 hthird.1 hthird.2,
      point_lt_of_midpoint_lt_of_disjoint h.2
        (by simpa [or_comm] using hfirstThird)
        hthird.1 hthird.2 hfirst.1 hfirst.2⟩)
  · exact Or.inr (Or.inr ⟨
      point_lt_of_midpoint_lt_of_disjoint h.1
        (by simpa [or_comm] using hfirstThird)
        hthird.1 hthird.2 hfirst.1 hfirst.2,
      point_lt_of_midpoint_lt_of_disjoint h.2 hfirstSecond
        hfirst.1 hfirst.2 hsecond.1 hsecond.2⟩)

private theorem badPair_impossible
    {curves : Finset C2Function} {lenses : Finset GraphLens}
    (hfamily : IsGraphPseudoCircleFamily curves)
    (hsides : ∀ lens ∈ lenses, lens.f ∈ curves ∧ lens.g ∈ curves)
    (hnonoverlap : ∀ first ∈ lenses, ∀ second ∈ lenses,
      first ≠ second → first.Nonoverlap second)
    {hostA hostB symbolI symbolJ : C2Function}
    (hhost : hostA ≠ hostB) (hsymbol : symbolI ≠ symbolJ)
    {ai aj bi bj : GraphLens}
    (hai : ai ∈ lenses) (haj : aj ∈ lenses)
    (hbi : bi ∈ lenses) (hbj : bj ∈ lenses)
    (huai : upper ai = hostA) (huaj : upper aj = hostA)
    (hubi : upper bi = hostB) (hubj : upper bj = hostB)
    (hlai : lower ai = symbolI) (hlaj : lower aj = symbolJ)
    (hlbi : lower bi = symbolI) (hlbj : lower bj = symbolJ)
    {xai xaj xbi xbj : UnitPoint}
    (hxai : (ai.left : ℝ) < xai ∧ (xai : ℝ) < ai.right)
    (hxaj : (aj.left : ℝ) < xaj ∧ (xaj : ℝ) < aj.right)
    (hxbi : (bi.left : ℝ) < xbi ∧ (xbi : ℝ) < bi.right)
    (hxbj : (bj.left : ℝ) < xbj ∧ (xbj : ℝ) < bj.right)
    (hbad : BadPair (xai : ℝ) xaj xbi xbj) : False := by
  have haiNeAj : ai ≠ aj := by
    intro h
    exact hsymbol (hlai.symm.trans (h ▸ hlaj))
  have hbiNeBj : bi ≠ bj := by
    intro h
    exact hsymbol (hlbi.symm.trans (h ▸ hlbj))
  have haiNeBi : ai ≠ bi := by
    intro h
    exact hhost (huai.symm.trans (h ▸ hubi))
  have hajNeBj : aj ≠ bj := by
    intro h
    exact hhost (huaj.symm.trans (h ▸ hubj))
  have hrowA := disjoint_intervals_of_nonoverlap_of_upper_eq
    (huai.trans huaj.symm) (hnonoverlap ai hai aj haj haiNeAj)
  have hrowB := disjoint_intervals_of_nonoverlap_of_upper_eq
    (hubi.trans hubj.symm) (hnonoverlap bi hbi bj hbj hbiNeBj)
  have hcolI := disjoint_intervals_of_nonoverlap_of_lower_eq
    (hlai.trans hlbi.symm) (hnonoverlap ai hai bi hbi haiNeBi)
  have hcolJ := disjoint_intervals_of_nonoverlap_of_lower_eq
    (hlaj.trans hlbj.symm) (hnonoverlap aj haj bj hbj hajNeBj)
  have hAiAboveI : symbolI xai < hostA xai := by
    simpa [huai, hlai] using lower_lt_upper_inside ai xai hxai.1 hxai.2
  have hAjAboveJ : symbolJ xaj < hostA xaj := by
    simpa [huaj, hlaj] using lower_lt_upper_inside aj xaj hxaj.1 hxaj.2
  have hBiAboveI : symbolI xbi < hostB xbi := by
    simpa [hubi, hlbi] using lower_lt_upper_inside bi xbi hxbi.1 hxbi.2
  have hBjAboveJ : symbolJ xbj < hostB xbj := by
    simpa [hubj, hlbj] using lower_lt_upper_inside bj xbj hxbj.1 hxbj.2
  have hBbelowIai : hostB xai < symbolI xai := by
    simpa [hubi, hlbi] using
      upper_lt_lower_at_disjoint_lens_point hfamily (hsides bi hbi)
        hcolI xai hxai.1 hxai.2
  have hBbelowJaj : hostB xaj < symbolJ xaj := by
    simpa [hubj, hlbj] using
      upper_lt_lower_at_disjoint_lens_point hfamily (hsides bj hbj)
        hcolJ xaj hxaj.1 hxaj.2
  have hAbelowIbi : hostA xbi < symbolI xbi := by
    simpa [huai, hlai] using
      upper_lt_lower_at_disjoint_lens_point hfamily (hsides ai hai)
        (by simpa [or_comm] using hcolI) xbi hxbi.1 hxbi.2
  have hAbelowJbj : hostA xbj < symbolJ xbj := by
    simpa [huaj, hlaj] using
      upper_lt_lower_at_disjoint_lens_point hfamily (hsides aj haj)
        (by simpa [or_comm] using hcolJ) xbj hxbj.1 hxbj.2
  rcases hbad with hhosts | hsymbols
  · exact three_intersections_of_alternates (u := hostB) (v := hostA) hfamily
      (by simpa [hubi] using upper_mem_curves (hsides bi hbi))
      (by simpa [huai] using upper_mem_curves (hsides ai hai))
      (Ne.symm hhost) hhosts
      (hBbelowIai.trans hAiAboveI)
      (hBbelowJaj.trans hAjAboveJ)
      (hAbelowIbi.trans hBiAboveI)
      (hAbelowJbj.trans hBjAboveJ)
  · have hJaboveIai : symbolI xai < symbolJ xai := by
      have hAbelowJai : hostA xai < symbolJ xai := by
        simpa [huaj, hlaj] using
          upper_lt_lower_at_disjoint_lens_point hfamily (hsides aj haj)
            hrowA xai hxai.1 hxai.2
      exact hAiAboveI.trans hAbelowJai
    have hJaboveIbi : symbolI xbi < symbolJ xbi := by
      have hBbelowJbi : hostB xbi < symbolJ xbi := by
        simpa [hubj, hlbj] using
          upper_lt_lower_at_disjoint_lens_point hfamily (hsides bj hbj)
            hrowB xbi hxbi.1 hxbi.2
      exact hBiAboveI.trans hBbelowJbi
    have hIaboveJaj : symbolJ xaj < symbolI xaj := by
      have hAbelowIaj : hostA xaj < symbolI xaj := by
        simpa [huai, hlai] using
          upper_lt_lower_at_disjoint_lens_point hfamily (hsides ai hai)
            (by simpa [or_comm] using hrowA) xaj hxaj.1 hxaj.2
      exact hAjAboveJ.trans hAbelowIaj
    have hIaboveJbj : symbolJ xbj < symbolI xbj := by
      have hBbelowIbj : hostB xbj < symbolI xbj := by
        simpa [hubi, hlbi] using
          upper_lt_lower_at_disjoint_lens_point hfamily (hsides bi hbi)
            (by simpa [or_comm] using hrowB) xbj hxbj.1 hxbj.2
      exact hBjAboveJ.trans hBbelowIbj
    exact three_intersections_of_alternates (u := symbolI) (v := symbolJ) hfamily
      (by simpa [hlai] using lower_mem_curves (hsides ai hai))
      (by simpa [hlaj] using lower_mem_curves (hsides aj haj))
      hsymbol hsymbols
      hJaboveIai hJaboveIbi hIaboveJaj hIaboveJbj

theorem moonSequences_intersection_reverse
    {curves : Finset C2Function} {lenses : Finset GraphLens}
    (hfamily : IsGraphPseudoCircleFamily curves)
    (hsides : ∀ lens ∈ lenses, lens.f ∈ curves ∧ lens.g ∈ curves)
    (hnonoverlap : ∀ first ∈ lenses, ∀ second ∈ lenses,
      first ≠ second → first.Nonoverlap second)
    {hostA hostB : C2Function} (hhost : hostA ≠ hostB) :
    MarcusTardos.IsCyclicIntersectionReverse
      (moonSequence lenses hostA) (moonSequence lenses hostB) := by
  apply cyclicIntersectionReverse_of_no_common_cyclic_triple
    (moonSequence lenses hostA) (moonSequence lenses hostB)
    (moonSequence_nodup hfamily hsides hnonoverlap hostA)
    (moonSequence_nodup hfamily hsides hnonoverlap hostB)
  intro symbolP symbolI symbolJ
    hpA hpB hiA hiB hjA hjB hpI hpJ hIJ hcyclicA hcyclicB
  let ap := lensForSymbol lenses hostA symbolP hpA
  let ai := lensForSymbol lenses hostA symbolI hiA
  let aj := lensForSymbol lenses hostA symbolJ hjA
  let bp := lensForSymbol lenses hostB symbolP hpB
  let bi := lensForSymbol lenses hostB symbolI hiB
  let bj := lensForSymbol lenses hostB symbolJ hjB
  have hap : ap ∈ lenses := lensForSymbol_mem_lenses lenses hostA symbolP hpA
  have hai : ai ∈ lenses := lensForSymbol_mem_lenses lenses hostA symbolI hiA
  have haj : aj ∈ lenses := lensForSymbol_mem_lenses lenses hostA symbolJ hjA
  have hbp : bp ∈ lenses := lensForSymbol_mem_lenses lenses hostB symbolP hpB
  have hbi : bi ∈ lenses := lensForSymbol_mem_lenses lenses hostB symbolI hiB
  have hbj : bj ∈ lenses := lensForSymbol_mem_lenses lenses hostB symbolJ hjB
  have huap : upper ap = hostA := upper_lensForSymbol lenses hostA symbolP hpA
  have huai : upper ai = hostA := upper_lensForSymbol lenses hostA symbolI hiA
  have huaj : upper aj = hostA := upper_lensForSymbol lenses hostA symbolJ hjA
  have hubp : upper bp = hostB := upper_lensForSymbol lenses hostB symbolP hpB
  have hubi : upper bi = hostB := upper_lensForSymbol lenses hostB symbolI hiB
  have hubj : upper bj = hostB := upper_lensForSymbol lenses hostB symbolJ hjB
  have hlap : lower ap = symbolP := lower_lensForSymbol lenses hostA symbolP hpA
  have hlai : lower ai = symbolI := lower_lensForSymbol lenses hostA symbolI hiA
  have hlaj : lower aj = symbolJ := lower_lensForSymbol lenses hostA symbolJ hjA
  have hlbp : lower bp = symbolP := lower_lensForSymbol lenses hostB symbolP hpB
  have hlbi : lower bi = symbolI := lower_lensForSymbol lenses hostB symbolI hiB
  have hlbj : lower bj = symbolJ := lower_lensForSymbol lenses hostB symbolJ hjB
  have hapNeAi : ap ≠ ai :=
    lensForSymbol_ne_of_symbol_ne lenses hostA symbolP symbolI hpA hiA hpI
  have hapNeAj : ap ≠ aj :=
    lensForSymbol_ne_of_symbol_ne lenses hostA symbolP symbolJ hpA hjA hpJ
  have haiNeAj : ai ≠ aj :=
    lensForSymbol_ne_of_symbol_ne lenses hostA symbolI symbolJ hiA hjA hIJ
  have hbpNeBi : bp ≠ bi :=
    lensForSymbol_ne_of_symbol_ne lenses hostB symbolP symbolI hpB hiB hpI
  have hbpNeBj : bp ≠ bj :=
    lensForSymbol_ne_of_symbol_ne lenses hostB symbolP symbolJ hpB hjB hpJ
  have hbiNeBj : bi ≠ bj :=
    lensForSymbol_ne_of_symbol_ne lenses hostB symbolI symbolJ hiB hjB hIJ
  have hrowAPi := disjoint_intervals_of_nonoverlap_of_upper_eq
    (huap.trans huai.symm) (hnonoverlap ap hap ai hai hapNeAi)
  have hrowAPj := disjoint_intervals_of_nonoverlap_of_upper_eq
    (huap.trans huaj.symm) (hnonoverlap ap hap aj haj hapNeAj)
  have hrowAIj := disjoint_intervals_of_nonoverlap_of_upper_eq
    (huai.trans huaj.symm) (hnonoverlap ai hai aj haj haiNeAj)
  have hrowBPi := disjoint_intervals_of_nonoverlap_of_upper_eq
    (hubp.trans hubi.symm) (hnonoverlap bp hbp bi hbi hbpNeBi)
  have hrowBPj := disjoint_intervals_of_nonoverlap_of_upper_eq
    (hubp.trans hubj.symm) (hnonoverlap bp hbp bj hbj hbpNeBj)
  have hrowBIj := disjoint_intervals_of_nonoverlap_of_upper_eq
    (hubi.trans hubj.symm) (hnonoverlap bi hbi bj hbj hbiNeBj)
  let xap := freshPoint ap ∅
  let xai := freshPoint ai {(xap : ℝ)}
  let xaj := freshPoint aj {(xap : ℝ), (xai : ℝ)}
  let xbp := freshPoint bp {(xap : ℝ), (xai : ℝ), (xaj : ℝ)}
  let xbi := freshPoint bi {(xap : ℝ), (xai : ℝ), (xaj : ℝ), (xbp : ℝ)}
  let xbj := freshPoint bj
    {(xap : ℝ), (xai : ℝ), (xaj : ℝ), (xbp : ℝ), (xbi : ℝ)}
  have hxap : (ap.left : ℝ) < xap ∧ (xap : ℝ) < ap.right :=
    ⟨left_lt_freshPoint ap ∅, freshPoint_lt_right ap ∅⟩
  have hxai : (ai.left : ℝ) < xai ∧ (xai : ℝ) < ai.right :=
    ⟨left_lt_freshPoint ai {(xap : ℝ)},
      freshPoint_lt_right ai {(xap : ℝ)}⟩
  have hxaj : (aj.left : ℝ) < xaj ∧ (xaj : ℝ) < aj.right :=
    ⟨left_lt_freshPoint aj {(xap : ℝ), (xai : ℝ)},
      freshPoint_lt_right aj {(xap : ℝ), (xai : ℝ)}⟩
  have hxbp : (bp.left : ℝ) < xbp ∧ (xbp : ℝ) < bp.right :=
    ⟨left_lt_freshPoint bp {(xap : ℝ), (xai : ℝ), (xaj : ℝ)},
      freshPoint_lt_right bp {(xap : ℝ), (xai : ℝ), (xaj : ℝ)}⟩
  have hxbi : (bi.left : ℝ) < xbi ∧ (xbi : ℝ) < bi.right :=
    ⟨left_lt_freshPoint bi {(xap : ℝ), (xai : ℝ), (xaj : ℝ), (xbp : ℝ)},
      freshPoint_lt_right bi {(xap : ℝ), (xai : ℝ), (xaj : ℝ), (xbp : ℝ)}⟩
  have hxbj : (bj.left : ℝ) < xbj ∧ (xbj : ℝ) < bj.right :=
    ⟨left_lt_freshPoint bj
        {(xap : ℝ), (xai : ℝ), (xaj : ℝ), (xbp : ℝ), (xbi : ℝ)},
      freshPoint_lt_right bj
        {(xap : ℝ), (xai : ℝ), (xaj : ℝ), (xbp : ℝ), (xbi : ℝ)}⟩
  have hdistinct :
      List.Pairwise (fun x y : ℝ => x ≠ y)
        [(xap : ℝ), xai, xaj, xbp, xbi, xbj] := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]
    have haiFresh := freshPoint_not_mem ai {(xap : ℝ)}
    have hajFresh := freshPoint_not_mem aj {(xap : ℝ), (xai : ℝ)}
    have hbpFresh := freshPoint_not_mem bp {(xap : ℝ), (xai : ℝ), (xaj : ℝ)}
    have hbiFresh := freshPoint_not_mem bi
      {(xap : ℝ), (xai : ℝ), (xaj : ℝ), (xbp : ℝ)}
    have hbjFresh := freshPoint_not_mem bj
      {(xap : ℝ), (xai : ℝ), (xaj : ℝ), (xbp : ℝ), (xbi : ℝ)}
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or,
      not_false_eq_true] at haiFresh hajFresh hbpFresh hbiFresh hbjFresh
    constructor
    · exact ⟨Ne.symm haiFresh, Ne.symm hajFresh.1,
        Ne.symm hbpFresh.1, Ne.symm hbiFresh.1, Ne.symm hbjFresh.1⟩
    · constructor
      · exact ⟨Ne.symm hajFresh.2, Ne.symm hbpFresh.2.1,
          Ne.symm hbiFresh.2.1, Ne.symm hbjFresh.2.1⟩
      · constructor
        · exact ⟨Ne.symm hbpFresh.2.2, Ne.symm hbiFresh.2.2.1,
            Ne.symm hbjFresh.2.2.1⟩
        · constructor
          · exact ⟨Ne.symm hbiFresh.2.2.2,
              Ne.symm hbjFresh.2.2.2.1⟩
          · constructor
            · exact Ne.symm hbjFresh.2.2.2.2
            · exact ⟨fun _ h => h.elim, List.Pairwise.nil⟩
  have hmidA := cyclic_midpoints_of_cyclic_indices hnonoverlap
    hostA symbolP symbolI symbolJ hpA hiA hjA hpI hpJ hIJ hcyclicA
  have hmidB := cyclic_midpoints_of_cyclic_indices hnonoverlap
    hostB symbolP symbolI symbolJ hpB hiB hjB hpI hpJ hIJ hcyclicB
  have hpointsA : CyclicLT (xap : ℝ) xai xaj :=
    cyclic_points_of_cyclic_midpoints hxap hxai hxaj
      hrowAPi hrowAPj hrowAIj hmidA
  have hpointsB : CyclicLT (xbp : ℝ) xbi xbj :=
    cyclic_points_of_cyclic_midpoints hxbp hxbi hxbj
      hrowBPi hrowBPj hrowBIj hmidB
  rcases chord_order hdistinct hpointsA hpointsB with hPI | hPJ | hIJbad
  · exact badPair_impossible hfamily hsides hnonoverlap hhost hpI
      hap hai hbp hbi huap huai hubp hubi hlap hlai hlbp hlbi
      hxap hxai hxbp hxbi hPI
  · exact badPair_impossible hfamily hsides hnonoverlap hhost hpJ
      hap haj hbp hbj huap huaj hubp hubj hlap hlaj hlbp hlbj
      hxap hxaj hxbp hxbj hPJ
  · exact badPair_impossible hfamily hsides hnonoverlap hhost hIJ
      hai haj hbi hbj huai huaj hubi hubj hlai hlaj hlbi hlbj
      hxai hxaj hxbi hxbj hIJbad

end Kakeya.Cinematic.GraphLensBridge
