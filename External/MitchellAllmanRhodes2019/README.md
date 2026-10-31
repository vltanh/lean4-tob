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
* The T1 test, in `Basic/Probability/Trinomial/Tests.lean` (`tendsto_t1`, `centroid_tight`), and from
  there `Phylogenetics.QuartetTests` in `Basic/Probability/QuartetLimits.lean`: under the null off its
  boundary the p-value of the source's §6 is asymptotically uniform, and at the centroid it stays away
  from `0` and `1`.

The proofs do not follow the source's route: the frequencies, whitened and centred
(`Phylogenetics.Trinomial.sampleW`), converge to two independent normals (`Basic/Probability/Trinomial/CLT.lean`,
`Whiten.lean`), and each statistic is close to a squared distance, uniformly on bounded sets of the
whitened frequencies, by the second-order expansion of `x log x`
(`Basic/Analysis/SpecialFunctions/EntropyExcess.lean`, `Basic/Probability/Trinomial/Statistics.lean`).
