# A Formal Proof of the Sticky-Kakeya Theorem

This repository contains a **sorry-free, unconditional Lean 4 formalization** of
the sticky-Kakeya Assouad-dimension lower bound (Wang–Zahl, Theorem 5.2). Under
the all-scale sticky covering hypothesis (Assouad Definition 2.12), every
`λ`-dense shading of a nonempty tube family has union volume at least `δ^ε` for
all `ε > 0` and all sufficiently small `δ`.

```lean
def PureWZ2Theorem5_2Statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ η δ₀ : ℝ,
      0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily δ,
          family.Nonempty →
          WZ2PaperPureCWAAtNearbyScales family (realRpowENN δ (-η)) →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            shading.IsLambdaDense (realRpowENN δ η) →
            realRpowENN δ ε ≤ volume shading.union
```

Toolchain: `leanprover/lean4:v4.32.0-rc1`. Entry point: `MyLeanRepo.lean`.
Endpoint: `PureWZ2Theorem5_2Unconditional`.

This is a joint project of **Nankai University** and **ByteDance Seed AI4Math Team**: Mingfeng Chen, Shaoming Guo, Yixuan Pang, Mingxing Shen, Zhihong Wang, Zheng Yuan, Huanyu Zheng, and Thomas Zhu.

Formalization results include:

- Hong Wang and Joshua Zahl,
*[The Assouad dimension of Kakeya sets in \mathbb R^3](https://arxiv.org/abs/2401.12337)*,
Invent. Math. 241 (2025), 153–206 — Theorem 5.2, Propositions 6.2–6.5, and Section 7.
- Hong Wang and Joshua Zahl,
*[Sticky Kakeya sets and the sticky Kakeya conjecture](https://arxiv.org/abs/2210.09581)*,
J. Amer. Math. Soc. 39 (2026), 515–585 — Propositions 3.2 and 4.1, and Section 5.
- Thomas Wolff,
*[An improved bound for Kakeya type maximal functions](https://doi.org/10.4171/RMI/188)*,
Rev. Mat. Iberoam. 11 (1995), 651–674 — hairbrush volume lower bound.
- Anthony Carbery and Stefán Ingi Valdimarsson,
*[The endpoint multilinear Kakeya theorem via the Borsuk–Ulam theorem](https://doi.org/10.1016/j.jfa.2013.01.012)*,
J. Funct. Anal. 264 (2013), 1643–1663 — endpoint multilinear Kakeya theorem.
- William O'Regan, Pablo Shmerkin, and Hong Wang,
*[Simple proofs of discretised projection theorems](https://arxiv.org/abs/2511.21656)* —
Ruzsa corollaries, Frostman reduction, and strong/weak ring theorems.
- Tuomas Orponen and Pablo Shmerkin,
*[On the Hausdorff dimension of Furstenberg sets and orthogonal projections in the plane](https://doi.org/10.1215/00127094-2022-0103)*,
Duke Math. J. 172 (2023), 3559–3632 — Theorems 1.3 and 6.1, and Propositions 7.3 and 8.1.
- Tuomas Orponen, Pablo Shmerkin, and Hong Wang,
*[Kaufman and Falconer estimates for radial projections and a continuum version of Beck's theorem](https://arxiv.org/abs/2209.00348)*,
Geom. Funct. Anal. 34 (2024), 164–201 — Lemma 2.9.
- Malabika Pramanik, Tongou Yang, and Joshua Zahl,
*[A Furstenberg-type problem for circles, and a Kaufman-type restricted projection theorem in \mathbb R^3](https://arxiv.org/abs/2207.02259)* —
Theorem 1.7.

