import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointRawLocalization

/-!
# The two paper similarities for a localized common-endpoint graph

The first coordinate class is normalized by an origin-centered homothety.
Both endpoint classes are normalized by one common midpoint-centered
homothety, so endpoint differences and affine-line geometry are preserved.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

/-- Apply separate first-coordinate and common endpoint similarities to one
tripartite edge. -/
def wz1CommonEndpointAffineEdge
    (mapF mapG : Point2 → Point2)
    (edge : Point2 × Point2 × Point2) :
    Point2 × Point2 × Point2 :=
  (mapF edge.1, mapG edge.2.1, mapG edge.2.2)

/-- Geometric normalization of one raw paper block. -/
structure WZ1CommonEndpointAffineNormalization
    {rho eta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho eta unitBall}
    (raw : WZ1CommonEndpointRawLocalization ready) where
  anchor : Point2 × Point2 × Point2
  anchor_mem : anchor ∈ raw.localized.block
  midpointG : Point2 := (2 : ℝ)⁻¹ • (anchor.2.1 + anchor.2.2)
  scaleF : ℝ := (dist anchor.1 0 + 2 * raw.gridScale)⁻¹
  scaleG : ℝ :=
    (dist anchor.2.1 anchor.2.2 / 2 + 2 * raw.gridScale)⁻¹
  scaleF_eq : scaleF = (dist anchor.1 0 + 2 * raw.gridScale)⁻¹
  scaleG_eq : scaleG =
    (dist anchor.2.1 anchor.2.2 / 2 + 2 * raw.gridScale)⁻¹
  scaleF_pos : 0 < scaleF
  scaleG_pos : 0 < scaleG
  scaleF_half : 1 / 2 ≤ scaleF
  scaleG_half : 1 / 2 ≤ scaleG
  mapF : Point2 → Point2 := wz1PositiveSimilarity 0 scaleF
  mapG : Point2 → Point2 := wz1PositiveSimilarity midpointG scaleG
  mapF_eq : mapF = wz1PositiveSimilarity 0 scaleF
  mapG_eq : mapG = wz1PositiveSimilarity midpointG scaleG
  F : DiscreteSet 2 := raw.localized.selectedF.image mapF
  G₁ : DiscreteSet 2 := raw.localized.selectedG₁.image mapG
  G₂ : DiscreteSet 2 := raw.localized.selectedG₂.image mapG
  H : Finset (Point2 × Point2 × Point2) :=
    raw.localized.block.image (wz1CommonEndpointAffineEdge mapF mapG)
  F_eq : F = raw.localized.selectedF.image mapF
  G₁_eq : G₁ = raw.localized.selectedG₁.image mapG
  G₂_eq : G₂ = raw.localized.selectedG₂.image mapG
  H_eq : H =
    raw.localized.block.image (wz1CommonEndpointAffineEdge mapF mapG)
  edge_support :
    ∀ edge ∈ H, edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂
  edge_card : H.card = raw.localized.block.card
  F_nonempty : F.Nonempty
  G₁_nonempty : G₁.Nonempty
  G₂_nonempty : G₂.Nonempty
  F_unit : F.IsInUnitBall
  G₁_unit : G₁.IsInUnitBall
  G₂_unit : G₂.IsInUnitBall
  F_separated : F.IsDeltaSeparated (ready.deltaGraph / 2)
  G₁_separated : G₁.IsDeltaSeparated (ready.deltaGraph / 2)
  G₂_separated : G₂.IsDeltaSeparated (ready.deltaGraph / 2)
  standardSeparation : WZ1StandardSeparation F G₁ G₂
  dotScale : ℝ := scaleF * scaleG
  dotScale_eq : dotScale = scaleF * scaleG
  dotScale_pos : 0 < dotScale
  dot_image :
    wz1DotDifferenceSet H =
      (fun value : ℝ => dotScale * value) ''
        wz1DotDifferenceSet raw.localized.block

/-- The paper geometry budget constructs the two explicit similarities. -/
theorem WZ1CommonEndpointRawLocalization.toAffineNormalization
    {rho eta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho eta unitBall}
    (raw : WZ1CommonEndpointRawLocalization ready)
    (heta : 0 < eta)
    (budget : WZ1CommonEndpointParameterBudget eta ready.deltaGraph) :
    Nonempty (WZ1CommonEndpointAffineNormalization raw) := by
  let block := raw.localized.block
  have hblockPosENN : 0 < (block.card : ENNReal) := by
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos ready.deltaGraph_pos _)).trans_le
        raw.block_threshold
  have hblockNonempty : block.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hblockPosENN
  rcases hblockNonempty with ⟨anchor, hanchor⟩
  let g := raw.gridScale
  let t := raw.threshold
  have hg : 0 < g := by
    dsimp only [g]
    rw [raw.gridScale_eq]
    exact Real.rpow_pos_of_pos ready.deltaGraph_pos _
  have ht : 0 < t := by
    dsimp only [t]
    rw [raw.threshold_eq]
    exact Real.rpow_pos_of_pos ready.deltaGraph_pos _
  have htOne : t ≤ 1 := by
    dsimp only [t]
    rw [raw.threshold_eq]
    exact Real.rpow_le_one ready.deltaGraph_pos.le
      (budget.delta_half.trans (by norm_num)) (mul_nonneg (by norm_num) heta.le)
  have hgeometry : 100 * g ≤ t := by
    simpa only [g, t, raw.gridScale_eq, raw.threshold_eq] using
      budget.geometry_absorb_real
  have hdiam := raw.localized.selected_diameter hg
  rcases hdiam with ⟨hFdiamRaw, hG₁diamRaw, hG₂diamRaw⟩
  have hFdiam : ∀ first ∈ raw.localized.selectedF,
      ∀ second ∈ raw.localized.selectedF, dist first second ≤ 2 * g := by
    simpa only [g] using hFdiamRaw
  have hG₁diam : ∀ first ∈ raw.localized.selectedG₁,
      ∀ second ∈ raw.localized.selectedG₁, dist first second ≤ 2 * g := by
    simpa only [g] using hG₁diamRaw
  have hG₂diam : ∀ first ∈ raw.localized.selectedG₂,
      ∀ second ∈ raw.localized.selectedG₂, dist first second ≤ 2 * g := by
    simpa only [g] using hG₂diamRaw
  have hanchorSupport := raw.localized.edge_support anchor hanchor
  have hanchorF : t ≤ dist anchor.1 0 :=
    raw.localized.first_far anchor hanchor
  have hanchorG : t ≤ dist anchor.2.1 anchor.2.2 :=
    raw.localized.endpoints_far anchor hanchor
  have hanchorFUpper : dist anchor.1 0 ≤ 1 :=
    unitBall.F_unit anchor.1
      (raw.localized.selectedF_subset hanchorSupport.1)
  have hanchorGUpper : dist anchor.2.1 anchor.2.2 ≤ 2 := by
    calc
      dist anchor.2.1 anchor.2.2 ≤
          dist anchor.2.1 0 + dist 0 anchor.2.2 :=
        dist_triangle _ _ _
      _ ≤ 1 + 1 := by
        gcongr
        · exact unitBall.G₁_unit anchor.2.1
            (raw.localized.selectedG₁_subset hanchorSupport.2.1)
        · simpa [dist_comm] using
            unitBall.G₁_unit anchor.2.2
              (raw.localized.selectedG₂_subset hanchorSupport.2.2)
      _ = 2 := by norm_num
  let midpointG : Point2 := (2 : ℝ)⁻¹ • (anchor.2.1 + anchor.2.2)
  let denomF := dist anchor.1 0 + 2 * g
  let denomG := dist anchor.2.1 anchor.2.2 / 2 + 2 * g
  let scaleF := denomF⁻¹
  let scaleG := denomG⁻¹
  have hdenomF : 0 < denomF := by
    dsimp only [denomF]
    positivity
  have hdenomG : 0 < denomG := by
    dsimp only [denomG]
    positivity
  have hgSmall : g ≤ 1 / 100 := by linarith
  have hdenomFUpper : denomF ≤ 2 := by
    dsimp only [denomF]
    linarith
  have hdenomGUpper : denomG ≤ 2 := by
    dsimp only [denomG]
    linarith
  have hscaleF : 0 < scaleF := inv_pos.mpr hdenomF
  have hscaleG : 0 < scaleG := inv_pos.mpr hdenomG
  have hscaleFHalf : 1 / 2 ≤ scaleF := by
    dsimp only [scaleF]
    simpa [one_div] using
      one_div_le_one_div_of_le hdenomF hdenomFUpper
  have hscaleGHalf : 1 / 2 ≤ scaleG := by
    dsimp only [scaleG]
    simpa [one_div] using
      one_div_le_one_div_of_le hdenomG hdenomGUpper
  let mapF := wz1PositiveSimilarity 0 scaleF
  let mapG := wz1PositiveSimilarity midpointG scaleG
  let F := raw.localized.selectedF.image mapF
  let G₁ := raw.localized.selectedG₁.image mapG
  let G₂ := raw.localized.selectedG₂.image mapG
  let H := block.image (wz1CommonEndpointAffineEdge mapF mapG)
  have hmapFInj : Function.Injective mapF :=
    wz1PositiveSimilarity_injective hscaleF
  have hmapGInj : Function.Injective mapG :=
    wz1PositiveSimilarity_injective hscaleG
  have hedgeInj :
      Function.Injective (wz1CommonEndpointAffineEdge mapF mapG) := by
    intro first second heq
    apply Prod.ext
    · exact hmapFInj (congr_arg Prod.fst heq)
    · apply Prod.ext
      · exact hmapGInj (congr_arg (fun edge => edge.2.1) heq)
      · exact hmapGInj (congr_arg (fun edge => edge.2.2) heq)
  have hHcard : H.card = block.card :=
    Finset.card_image_of_injective _ hedgeInj
  have hsupport :
      ∀ edge ∈ H, edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂ := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with ⟨source, hsource, rfl⟩
    have hs := raw.localized.edge_support source hsource
    exact ⟨Finset.mem_image.mpr ⟨source.1, hs.1, rfl⟩,
      Finset.mem_image.mpr ⟨source.2.1, hs.2.1, rfl⟩,
      Finset.mem_image.mpr ⟨source.2.2, hs.2.2, rfl⟩⟩
  have hnonempty : F.Nonempty ∧ G₁.Nonempty ∧ G₂.Nonempty := by
    exact ⟨⟨mapF anchor.1, Finset.mem_image.mpr
      ⟨anchor.1, hanchorSupport.1, rfl⟩⟩,
      ⟨mapG anchor.2.1, Finset.mem_image.mpr
        ⟨anchor.2.1, hanchorSupport.2.1, rfl⟩⟩,
      ⟨mapG anchor.2.2, Finset.mem_image.mpr
        ⟨anchor.2.2, hanchorSupport.2.2, rfl⟩⟩⟩
  have hmidpointFirst : dist anchor.2.1 midpointG =
      dist anchor.2.1 anchor.2.2 / 2 := by
    rw [dist_eq_norm]
    have heq : anchor.2.1 - midpointG =
        (2 : ℝ)⁻¹ • (anchor.2.1 - anchor.2.2) := by
      ext i
      simp [midpointG]
      ring
    rw [heq, norm_smul, Real.norm_eq_abs]
    norm_num
    rw [← dist_eq_norm]
    ring
  have hmidpointSecond : dist anchor.2.2 midpointG =
      dist anchor.2.1 anchor.2.2 / 2 := by
    rw [dist_eq_norm]
    have heq : anchor.2.2 - midpointG =
        (2 : ℝ)⁻¹ • (anchor.2.2 - anchor.2.1) := by
      ext i
      simp [midpointG]
      ring
    rw [heq, norm_smul, Real.norm_eq_abs]
    norm_num
    rw [← dist_eq_norm, dist_comm]
    ring
  have hFunit : DiscreteSet.IsInUnitBall F := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨source, hsource, rfl⟩
    change dist (wz1PositiveSimilarity 0 scaleF source) 0 ≤ 1
    rw [wz1PositiveSimilarity, sub_zero, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hscaleF]
    have hsourceAnchor := hFdiam source hsource anchor.1 hanchorSupport.1
    have hnorm : ‖source‖ ≤ dist anchor.1 0 + 2 * g := by
      calc
        ‖source‖ = dist source 0 := by rw [dist_zero_right]
        _ ≤ dist source anchor.1 + dist anchor.1 0 := dist_triangle _ _ _
        _ ≤ 2 * g + dist anchor.1 0 := by gcongr
        _ = denomF := by simp [denomF]; ring
    calc
      scaleF * ‖source‖ ≤ scaleF * denomF := by gcongr
      _ = 1 := by
        dsimp only [scaleF]
        exact inv_mul_cancel₀ hdenomF.ne'
  have hG₁unit : DiscreteSet.IsInUnitBall G₁ := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨source, hsource, rfl⟩
    change dist (wz1PositiveSimilarity midpointG scaleG source) 0 ≤ 1
    rw [wz1PositiveSimilarity, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hscaleG]
    have hsourceAnchor := hG₁diam source hsource anchor.2.1 hanchorSupport.2.1
    have hnorm : ‖source - midpointG‖ ≤ denomG := by
      rw [← dist_eq_norm]
      calc
        dist source midpointG ≤
            dist source anchor.2.1 + dist anchor.2.1 midpointG :=
          dist_triangle _ _ _
        _ ≤ 2 * g + dist anchor.2.1 anchor.2.2 / 2 := by
          exact add_le_add hsourceAnchor hmidpointFirst.le
        _ = denomG := by simp [denomG]; ring
    calc
      scaleG * ‖source - midpointG‖ ≤ scaleG * denomG := by gcongr
      _ = 1 := by
        dsimp only [scaleG]
        exact inv_mul_cancel₀ hdenomG.ne'
  have hG₂unit : DiscreteSet.IsInUnitBall G₂ := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨source, hsource, rfl⟩
    change dist (wz1PositiveSimilarity midpointG scaleG source) 0 ≤ 1
    rw [wz1PositiveSimilarity, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hscaleG]
    have hsourceAnchor := hG₂diam source hsource anchor.2.2 hanchorSupport.2.2
    have hnorm : ‖source - midpointG‖ ≤ denomG := by
      rw [← dist_eq_norm]
      calc
        dist source midpointG ≤
            dist source anchor.2.2 + dist anchor.2.2 midpointG :=
          dist_triangle _ _ _
        _ ≤ 2 * g + dist anchor.2.1 anchor.2.2 / 2 := by
          exact add_le_add hsourceAnchor hmidpointSecond.le
        _ = denomG := by simp [denomG]; ring
    calc
      scaleG * ‖source - midpointG‖ ≤ scaleG * denomG := by gcongr
      _ = 1 := by
        dsimp only [scaleG]
        exact inv_mul_cancel₀ hdenomG.ne'
  have hsourceSep :
      raw.localized.selectedF.IsDeltaSeparated ready.deltaGraph ∧
      raw.localized.selectedG₁.IsDeltaSeparated ready.deltaGraph ∧
      raw.localized.selectedG₂.IsDeltaSeparated ready.deltaGraph := by
    rw [ready.deltaGraph_eq]
    exact ⟨unitBall.F_separated.mono raw.localized.selectedF_subset,
      unitBall.G₁_separated.mono raw.localized.selectedG₁_subset,
      unitBall.G₁_separated.mono raw.localized.selectedG₂_subset⟩
  have himageSep :
      DiscreteSet.IsDeltaSeparated F (ready.deltaGraph / 2) ∧
      DiscreteSet.IsDeltaSeparated G₁ (ready.deltaGraph / 2) ∧
      DiscreteSet.IsDeltaSeparated G₂ (ready.deltaGraph / 2) := by
    constructor
    · intro first hfirst second hsecond hne
      rcases Finset.mem_image.mp hfirst with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hsecond with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun heq => hne (congr_arg mapF heq)
      change ready.deltaGraph / 2 ≤
        dist (wz1PositiveSimilarity 0 scaleF a)
          (wz1PositiveSimilarity 0 scaleF b)
      rw [wz1PositiveSimilarity_dist hscaleF]
      exact calc
        ready.deltaGraph / 2 ≤ scaleF * ready.deltaGraph := by
          nlinarith [ready.deltaGraph_pos]
        _ ≤ scaleF * dist a b := by gcongr; exact hsourceSep.1 ha hb hab
    constructor
    · intro first hfirst second hsecond hne
      rcases Finset.mem_image.mp hfirst with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hsecond with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun heq => hne (congr_arg mapG heq)
      change ready.deltaGraph / 2 ≤
        dist (wz1PositiveSimilarity midpointG scaleG a)
          (wz1PositiveSimilarity midpointG scaleG b)
      rw [wz1PositiveSimilarity_dist hscaleG]
      exact calc
        ready.deltaGraph / 2 ≤ scaleG * ready.deltaGraph := by
          nlinarith [ready.deltaGraph_pos]
        _ ≤ scaleG * dist a b := by gcongr; exact hsourceSep.2.1 ha hb hab
    · intro first hfirst second hsecond hne
      rcases Finset.mem_image.mp hfirst with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hsecond with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun heq => hne (congr_arg mapG heq)
      change ready.deltaGraph / 2 ≤
        dist (wz1PositiveSimilarity midpointG scaleG a)
          (wz1PositiveSimilarity midpointG scaleG b)
      rw [wz1PositiveSimilarity_dist hscaleG]
      exact calc
        ready.deltaGraph / 2 ≤ scaleG * ready.deltaGraph := by
          nlinarith [ready.deltaGraph_pos]
        _ ≤ scaleG * dist a b := by gcongr; exact hsourceSep.2.2 ha hb hab
  have hstd : WZ1StandardSeparation F G₁ G₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro first hfirst second hsecond
      rcases Finset.mem_image.mp hfirst with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hsecond with ⟨b, hb, rfl⟩
      change dist (wz1PositiveSimilarity 0 scaleF a)
        (wz1PositiveSimilarity 0 scaleF b) ≤ 1 / 10
      rw [wz1PositiveSimilarity_dist hscaleF]
      have hsource := hFdiam a ha b hb
      have hdenomLower : 20 * g ≤ denomF := by
        dsimp only [denomF]
        linarith
      dsimp only [scaleF]
      have hratio : denomF⁻¹ * (2 * g) ≤ 1 / 10 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2
        have hinv : denomF⁻¹ * denomF = 1 := inv_mul_cancel₀ hdenomF.ne'
        nlinarith [mul_le_mul_of_nonneg_left hdenomLower
          (inv_nonneg.mpr hdenomF.le)]
      exact (mul_le_mul_of_nonneg_left hsource
        (inv_nonneg.mpr hdenomF.le)).trans hratio
    · intro first hfirst second hsecond
      rcases Finset.mem_image.mp hfirst with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hsecond with ⟨b, hb, rfl⟩
      change dist (wz1PositiveSimilarity midpointG scaleG a)
        (wz1PositiveSimilarity midpointG scaleG b) ≤ 1 / 10
      rw [wz1PositiveSimilarity_dist hscaleG]
      have hsource := hG₁diam a ha b hb
      have hdenomLower : 20 * g ≤ denomG := by
        dsimp only [denomG]
        linarith
      dsimp only [scaleG]
      have hratio : denomG⁻¹ * (2 * g) ≤ 1 / 10 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2
        have hinv : denomG⁻¹ * denomG = 1 := inv_mul_cancel₀ hdenomG.ne'
        nlinarith [mul_le_mul_of_nonneg_left hdenomLower
          (inv_nonneg.mpr hdenomG.le)]
      exact (mul_le_mul_of_nonneg_left hsource
        (inv_nonneg.mpr hdenomG.le)).trans hratio
    · intro first hfirst second hsecond
      rcases Finset.mem_image.mp hfirst with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hsecond with ⟨b, hb, rfl⟩
      change dist (wz1PositiveSimilarity midpointG scaleG a)
        (wz1PositiveSimilarity midpointG scaleG b) ≤ 1 / 10
      rw [wz1PositiveSimilarity_dist hscaleG]
      have hsource := hG₂diam a ha b hb
      have hdenomLower : 20 * g ≤ denomG := by
        dsimp only [denomG]
        linarith
      dsimp only [scaleG]
      have hratio : denomG⁻¹ * (2 * g) ≤ 1 / 10 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2
        have hinv : denomG⁻¹ * denomG = 1 := inv_mul_cancel₀ hdenomG.ne'
        nlinarith [mul_le_mul_of_nonneg_left hdenomLower
          (inv_nonneg.mpr hdenomG.le)]
      exact (mul_le_mul_of_nonneg_left hsource
        (inv_nonneg.mpr hdenomG.le)).trans hratio
    · intro first hfirst second hsecond
      rcases Finset.mem_image.mp hfirst with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hsecond with ⟨b, hb, rfl⟩
      change 1 / 2 ≤ dist (wz1PositiveSimilarity midpointG scaleG a)
        (wz1PositiveSimilarity midpointG scaleG b)
      rw [wz1PositiveSimilarity_dist hscaleG]
      have haAnchor := hG₁diam a ha anchor.2.1 hanchorSupport.2.1
      have hbAnchor := hG₂diam b hb anchor.2.2 hanchorSupport.2.2
      have hsource : dist anchor.2.1 anchor.2.2 - 4 * g ≤ dist a b := by
        have htri := dist_triangle4 anchor.2.1 a b anchor.2.2
        have hba : dist anchor.2.1 a ≤ 2 * g := by
          simpa [dist_comm] using haAnchor
        have hbb : dist b anchor.2.2 ≤ 2 * g := by
          simpa [dist_comm] using hbAnchor
        linarith
      dsimp only [scaleG]
      have hratio : 1 / 2 ≤ denomG⁻¹ *
          (dist anchor.2.1 anchor.2.2 - 4 * g) := by
        have hd : 100 * g ≤ dist anchor.2.1 anchor.2.2 := hgeometry.trans hanchorG
        have hinv : denomG⁻¹ * denomG = 1 := inv_mul_cancel₀ hdenomG.ne'
        dsimp only [denomG] at hinv ⊢
        nlinarith [mul_nonneg (inv_nonneg.mpr hdenomG.le)
          (sub_nonneg.mpr (by linarith : 4 * g ≤ dist anchor.2.1 anchor.2.2))]
      exact hratio.trans
        (mul_le_mul_of_nonneg_left hsource
          (inv_nonneg.mpr hdenomG.le))
    · intro point hpoint
      rcases Finset.mem_image.mp hpoint with ⟨a, ha, rfl⟩
      change 1 / 2 ≤ dist (wz1PositiveSimilarity 0 scaleF a) 0
      have hzero : wz1PositiveSimilarity 0 scaleF 0 = (0 : Point2) := by
        simp [wz1PositiveSimilarity]
      have haAnchor := hFdiam a ha anchor.1 hanchorSupport.1
      have hsource : dist anchor.1 0 - 2 * g ≤ dist a 0 := by
        have htri := dist_triangle anchor.1 a 0
        linarith [dist_comm anchor.1 a]
      dsimp only [scaleF]
      have hratio : 1 / 2 ≤ denomF⁻¹ *
          (dist anchor.1 0 - 2 * g) := by
        have hd : 100 * g ≤ dist anchor.1 0 := hgeometry.trans hanchorF
        have hinv : denomF⁻¹ * denomF = 1 := inv_mul_cancel₀ hdenomF.ne'
        dsimp only [denomF] at hinv ⊢
        nlinarith [mul_nonneg (inv_nonneg.mpr hdenomF.le)
          (sub_nonneg.mpr (by linarith : 2 * g ≤ dist anchor.1 0))]
      calc
        1 / 2 ≤ denomF⁻¹ * (dist anchor.1 0 - 2 * g) := hratio
        _ ≤ scaleF * dist a 0 := by
          exact mul_le_mul_of_nonneg_left hsource
            (inv_nonneg.mpr hdenomF.le)
        _ = dist (wz1PositiveSimilarity 0 scaleF a)
            (wz1PositiveSimilarity 0 scaleF 0) :=
          (wz1PositiveSimilarity_dist hscaleF a 0).symm
        _ = dist (wz1PositiveSimilarity 0 scaleF a) 0 := by rw [hzero]
  let dotScale := scaleF * scaleG
  have hdotScale : 0 < dotScale := mul_pos hscaleF hscaleG
  have hdotEdge : ∀ source,
      inner ℝ (wz1CommonEndpointAffineEdge mapF mapG source).1
          ((wz1CommonEndpointAffineEdge mapF mapG source).2.1 -
            (wz1CommonEndpointAffineEdge mapF mapG source).2.2) =
        dotScale * inner ℝ source.1 (source.2.1 - source.2.2) := by
    intro source
    change inner ℝ (scaleF • (source.1 - 0))
      (scaleG • (source.2.1 - midpointG) -
        scaleG • (source.2.2 - midpointG)) = _
    rw [sub_zero, ← smul_sub, inner_smul_left, inner_smul_right]
    simp [dotScale]
    ring
  have hdot :
      wz1DotDifferenceSet H =
        (fun value : ℝ => dotScale * value) ''
          wz1DotDifferenceSet block := by
    ext value
    constructor
    · intro hvalue
      rcases Finset.mem_image.mp hvalue with ⟨edge, hedge, rfl⟩
      rcases Finset.mem_image.mp hedge with ⟨source, hsource, rfl⟩
      refine ⟨inner ℝ source.1 (source.2.1 - source.2.2), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨source, hsource, rfl⟩
      · exact (hdotEdge source).symm
    · rintro ⟨sourceValue, hsourceValue, rfl⟩
      rcases Finset.mem_image.mp hsourceValue with ⟨source, hsource, rfl⟩
      exact Finset.mem_image.mpr
        ⟨wz1CommonEndpointAffineEdge mapF mapG source,
          Finset.mem_image.mpr ⟨source, hsource, rfl⟩, hdotEdge source⟩
  exact ⟨{
    anchor := anchor
    anchor_mem := hanchor
    midpointG := midpointG
    scaleF := scaleF
    scaleG := scaleG
    scaleF_eq := rfl
    scaleG_eq := rfl
    scaleF_pos := hscaleF
    scaleG_pos := hscaleG
    scaleF_half := hscaleFHalf
    scaleG_half := hscaleGHalf
    mapF := mapF
    mapG := mapG
    mapF_eq := rfl
    mapG_eq := rfl
    F := F
    G₁ := G₁
    G₂ := G₂
    H := H
    F_eq := rfl
    G₁_eq := rfl
    G₂_eq := rfl
    H_eq := rfl
    edge_support := hsupport
    edge_card := hHcard
    F_nonempty := hnonempty.1
    G₁_nonempty := hnonempty.2.1
    G₂_nonempty := hnonempty.2.2
    F_unit := hFunit
    G₁_unit := hG₁unit
    G₂_unit := hG₂unit
    F_separated := himageSep.1
    G₁_separated := himageSep.2.1
    G₂_separated := himageSep.2.2
    standardSeparation := hstd
    dotScale := dotScale
    dotScale_eq := rfl
    dotScale_pos := hdotScale
    dot_image := hdot
  }⟩

end

end Kakeya.Assouad
