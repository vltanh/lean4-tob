module

public import Basic.Phylogenetics.Defs

/-!
# Ané, Fogg, Allman, Baños, Rhodes 2024: exchangeability under the network multispecies coalescent

C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the multispecies
coalescent: theory and prevalence*, J. Math. Biol. 88 (2024), https://doi.org/10.1007/s00285-024-02050-7.

The exchangeability of taxa on the same side of a cut edge is cited by TOB-QMC's proof of Lemma 3 from
this source and from TINNiK (ECToBlob §5.1 and Remark 3.3 use the same fact). This project takes it as
a hypothesis; see `External/AneEtAl2024/README.md`.
-/

@[expose] public noncomputable section

open Phylogenetics

namespace External.AneEtAl2024

end External.AneEtAl2024
