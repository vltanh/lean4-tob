# Mitchell, Allman, Rhodes 2019: hypothesis testing near singularities and boundaries

Source: J. D. Mitchell, E. S. Allman, J. A. Rhodes, *Hypothesis testing near singularities and
boundaries*, Electron. J. Stat. 13 (2019), 2150–2193, <https://doi.org/10.1214/19-EJS1576>.

TINNiK's Proposition 5 applies the source's Theorem 3.1 to the cut model, and ECToBlob uses the source's
T1 test.

Theorem 3.1 is a general theorem on regular models. It rests on van der Vaart, *Asymptotic Statistics*,
Theorem 16.7, which needs differentiability in quadratic mean, local asymptotic normality and the
consistency of maximum likelihood estimates; Mathlib has none of these. So the general theorem is not
stated here. What is proved directly, from Mathlib's central limit theorem, is the special case the
papers use:

* `External.MitchellAllmanRhodes2019.cutModel_theorem31` (`CutModel.lean`): for the trinomial with true
  point `(1 - 2φ/3, φ/3, φ/3)`, `0 < φ < 3/2`, the likelihood ratio statistic of the cut model and the
  least squared distance from the normal sample `N((0, μ₀(n)), I)` to the lines `x = 0`, `y = ± γ₀ x`
  converge in distribution to the same limit. For `φ ≠ 1` the limit is `χ²₁` (`|μ₀(n)| → ∞`, with either
  sign); for `φ = 1` it is the least squared distance from a standard normal point to the three lines.
  This is the conclusion of Theorem 3.1 for this model, with the distance term of the alternative zero
  and the model's segments replaced by whole lines, as in TINNiK's proof of Proposition 5. TINNiK's
  `proposition5` computes the distances from it by the projections and takes their minimum, as the paper
  does.
* `External.MitchellAllmanRhodes2019.proposition4_1` (`T3Limit.lean`), Proposition 4.1 for the trinomial: at the true point
  `(1 - 2φ/3, φ/3, φ/3)`, `0 < φ ≤ 1`, the likelihood ratio statistic of model T3 (`Phylogenetics.Trinomial.t3S`, which
  `t3S_eq_likelihoodRatio` shows is `2 (sup_{Δ²} ℓ - sup_{Θ₀} ℓ)` on positive counts) and the variable `t3Var φ` under
  `N((0, μ₀(n)), I)` converge in distribution to the same limit. For `φ < 1` it is `χ²₁`
  (`QuartetTests.t3Stat_limitLaw_of_isT1Strict`, on a sample of gene trees).
* At the singularity, the limit law of the T3 statistic is that of `t3Var 1`, with `Z`, `Z̄` standard normal:
  `QuartetTests.t3Stat_limitLaw` (`T3Limit.lean`), with `tendstoInDistribution_t3Stat` and, for the density below,
  `t3Stat_limitLaw_density`. It is not `χ²_d` for any `d ≥ 1`, as the source says: `map_t3Var_one_ne_chiSqLaw`. With the true parameter
  `μ₀ = 0`, the p-value there is asymptotically uniform: `t3Tail_t3Stat_asymptoticallyUniform`. This says nothing of the p-value
  `t3PValue`, with the fitted `μ̂₀`, of which only non-collapse is proved (`QuartetTests.t3Test_nonCollapse`, in `T3Test.lean`). None of the
  sources read claims a limit law for it.
* `QuartetTests.t3Var_density`, also `External.MitchellAllmanRhodes2019.proposition4_2` (`T3Density.lean`), Proposition 4.2: the printed
  density, `t3Density`, is that of the law of `t3Var φ`. The source states it for `φ₀ ∈ (0, 1]`; it holds for `φ₀ < 3/2`. This proof
  follows the source's Appendix B: the same strips, the same reflection, differentiation in polar coordinates and the substitution
  `y = x tan β`, with `Basic/ForMathlib/Probability/GaussianStrip.lean` packaging what is in `GaussianPlane.lean`. What the source says of
  the density is also proved: at the singularity, `t3Density_one`; the limit `χ²₁` as `n → ∞`, `tendsto_t3Density_atTop`; continuity in
  `φ₀`, `continuousOn_t3Density`, on `(0, 3/2)`, where the source writes `[0, 1)`.
* `External.MitchellAllmanRhodes2019.proposition5_1` and `proposition5_2` (`T1Limit.lean`), the same two propositions for model T1:
  `t1S_eq_likelihoodRatio`, `t1Var_density`; on a sample, `t1Stat_limitLaw` at the boundary point and `t1Stat_limitLaw_of_isT1Strict` off it.
  At `μ₀ = 0` the law is `½ χ²₁ + ½ χ²₂` (`t1Tail_zero`, `t1Density_zero`), and the density tends to that of `χ²₁`
  (`tendsto_t1Density_atTop`), since `M₀(x) → 0` (`tendsto_struveM₀_atTop`). The proof of the density follows Appendix C. Its first
  display has a misprint: the second line for `d/dx G₁` repeats the line for `d/dx G₂`; the value the sum uses is
  `(1 / 2π) exp (-x² / 2) √(2π) ½ (1 + erf (μ₀ / √2))`. It also calls `x` the distance to the mean, where it is the distance to the half-line.
  The fitted T1 p-value at the boundary point is not asymptotically uniform (`t1PValue_centroid_not_asymptoticallyUniform`), and with the
  true parameter it is (`t1Tail_t1Stat_asymptoticallyUniform`).
* The T1 test, in `src/Basic/Testing/Trinomial/Tests.lean` of the library (`tendsto_t1`, `centroid_tight`), and from
  there `Phylogenetics.QuartetTests` in `src/Basic/Testing/Limits.lean`: under the null off its
  boundary the p-value of the source's §6 is asymptotically uniform, and at the centroid it stays away
  from `0` and `1`.

The source was read, in its arXiv version (arXiv:1806.08458v1, the TeX and the PDF), whose numbering is used here; the journal's text
was not compared.

Apart from Propositions 4.2 and 5.2, the proofs do not follow the source's route: the frequencies, whitened and centred
(`Phylogenetics.Trinomial.sampleW`), converge to two independent normals (`src/Basic/Testing/Trinomial/CLT.lean`,
`Whiten.lean`), and each statistic is close to a squared distance, uniformly on bounded sets of the
whitened frequencies, by the second-order expansion of `x log x`
(`src/Basic/ForMathlib/Analysis/SpecialFunctions/EntropyExcess.lean`, `src/Basic/Testing/Trinomial/Statistics.lean`).
