# motivic-goodwillie — program register

Every item lands compiling under Rocq 9 against Coq-HoTT with coqchk clean and zero Admitted. No item retracts a claim; each names the construction that makes the ambient claim true.

1. goodwillie_tower_stabilizes is instantiated non-trivially by discharging its hypotheses for FamGoodwillieTower restricted to boundedly-supported families, where ZeroMeasureImpliesZeroObj becomes decidable.
2. FiberData is upgraded with the universal property of a genuine fiber, uniqueness of factorization through the inclusion, so that zero composites no longer qualify by default and the obstruction objects are canonically determined.
3. Genuine mapping cones for arbitrary maps are constructed in FamCat, replacing the cofiber that returns either zero or the untouched target.
4. The converse detection is proven for FamGoodwillieTower: a tower map that is an isomorphism forces its layer to vanish, so layers never over-report.
5. The carrier is abelianized: the level-family category is rebuilt with abelian-group-valued levels, where levelwise biproducts and pushouts exist, so the n-excision predicate becomes positively testable.
6. FamP n is proven n-excisive, and if the guard-cube notion refuses the proof the cube notion is repaired until the theorem holds.
7. The n-homogeneous predicate is defined and FamD n is proven to satisfy it, earning the name layer.
8. The equivalence between hom from the suspension of X to Y and hom from X to the loops of Y is derived from the ProperStable triangle identities and used at least once.
9. The opposite-category machinery pays rent with one dual theorem, tower limits exchanged with tower colimits under duality_principle.
10. CField is completed to a genuine field, addition and inverses joining the multiplication so that straight-line homotopies run through the full field structure and the record earns its name.
11. CScheme acquires structure that determines cs_dim and cs_sing, such as polynomial maps on affine zero-sets, so dimension is a theorem about the carrier rather than a tag beside it.
12. Concrete-scheme morphisms are restricted to polynomial maps and Nisnevich squares are formulated with the decomposition condition, pushing descent beyond representables.
13. Fiber products of concrete schemes are constructed with their dimension and singularity bookkeeping, and CompatibleFamily is restated on the pullbacks its quantification over all test schemes silently encodes.
14. The Nisnevich section earns its name: the completely decomposed condition is added and one statement is proven that plain joint surjectivity cannot deliver.
15. One actual functor on CSch is defined, its level family is derived from the geometry, and the tower is run on it, so the scheme world and the tower world exchange morphisms.
16. The field bm_levels is derived from the blowdown fiber data rather than stored, occupancy at each level coming from actual fibers, with support below bm_exc_dim proven from bm_exc_below.
17. A1Homotopic is closed into an equivalence relation by chains, proven a congruence, the localization of CSch inverting the affine line is constructed as a quotient category, and the point is proven equivalent to the affine line there.
18. The field gms_level becomes load-bearing: spectrum morphisms are rebuilt as levelwise scheme maps compatible with bonding, so the levels carry the homotopical content their name promises.
19. MotivicSH is rebuilt with homs that depend on the objects, as level-family maps or graded groups, so that nonzero spectra fall into more than two isomorphism classes.
20. The codiscrete Scheme category is recast as the file's explicit degenerate model, each of its SH convergence theorems paired with the MotivicSH statement that supersedes it, so no vacuous theorem parades as content and the collapse suite stands as the counterexample it is.
21. BaseField is fused with CField so that its carrier, constants, and characteristic are read by the concrete scheme layer, leaving no record whose fields nothing consumes.
22. One spectral sequence is produced whose bound and detection hypotheses are theorems: the spectral sequence of a weight-filtered tower, its first page identified with the graded pieces of the WeightFiltration and its differential measure derived.
23. Abutment is stated and proven: past the degeneration page the stable page is identified with the graded pieces of a limit object.
24. MotivicSH is triangulated with hom-abelian shift categories and genuine cofiber sequences, and the slice spectral sequence of the tower runs through wss_degeneration as a formal weighted analogue of Levine's convergence.
25. The total weight earns its factors: one theorem exhibits cs_dim changing the stage of stabilization, realized by an obstruction measure calibrated to dimension rather than absorbed into the constant.
