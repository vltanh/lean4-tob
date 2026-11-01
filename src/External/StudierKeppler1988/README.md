# Studier and Keppler 1988, the Lemma

Source: J. A. Studier, K. J. Keppler, *A note on the neighbor-joining algorithm of Saitou and Nei*, Mol. Biol. Evol. 5 (1988), 729-731, <https://doi.org/10.1093/oxfordjournals.molbev.a040527>. Read: the journal's PDF, a scan of 3 pages, in the copy of the Internet Archive; the publisher refused the download.

Page 730 assumes "a tree in which all branches are positive", and attributes to Saitou and Nei 1987, which was not read, the Lemma "If `i` and `j` are neighbors, then `S_ij` is the strictly least element in its row and column", with the proof "Each summand in formula (5a) is positive". `Lemma.lean` shows that this fails at a polytomy: on the star with four leaves and unit weights all `S_ij` are equal (`not_lemmaAsPrinted`).

The letter neither asks for a binary tree nor defines "neighbors". This reads them as the library's `Phylogenetics.NJ.Nbr`, a cherry of a resolution of the tree. If the letter means binary trees only, the star is outside its scope and the failure is one of wording.

The letter's Theorem, that a pair minimizing `S_ij` are neighbours, holds with polytomies: `Phylogenetics.NJ.exists_QC_lt_of_not_nbr` in the library.
