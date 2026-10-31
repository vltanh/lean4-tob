# Mitchell, Allman, Rhodes 2019: hypothesis testing near singularities and boundaries

Source: J. D. Mitchell, E. S. Allman, J. A. Rhodes, *Hypothesis testing near singularities and
boundaries*, Electron. J. Stat. 13 (2019), 2150–2193, <https://doi.org/10.1214/19-EJS1576>.

TINNiK's Proposition 5 applies the source's Theorem 3.1 to the cut model, and ECToBlob uses the source's
T1 test. Theorem 3.1 is a general theorem on regular models, resting on van der Vaart, *Asymptotic
Statistics*, Theorem 16.7, which needs a theory of quadratic mean differentiability that Mathlib lacks.
`External.MitchellAllmanRhodes2019` proves directly what the papers use, for the trinomial model: the
limit of the likelihood ratio statistics for the T1 and cut models at each point of the null, from the
central limit theorem. These are a different standard form of Theorem 3.1, which give exactly the
statements used; see `Basic/Probability/Trinomial/`.
