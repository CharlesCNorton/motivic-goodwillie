# motivic-goodwillie — program register

Every item lands compiling under Rocq 9 against Coq-HoTT with coqchk clean and zero Admitted.

1. Abelianize the carrier: rebuild the level-family category with abelian-group-valued levels, where levelwise biproducts and pushouts exist, so the n-excision predicate becomes positively testable and the excisiveness of P_n becomes a theorem rather than a universal property alone.
2. Triangulate MotivicSH with hom-abelian shift categories and genuine cofiber sequences, then build the slice spectral sequence of the tower as a WeightedSpectralSequence instance and run wss_degeneration on it, a formal weighted analogue of Levine's convergence.
3. Restrict concrete-scheme morphisms to polynomial maps and formulate Nisnevich squares with the decomposition condition, pushing descent beyond representables.
