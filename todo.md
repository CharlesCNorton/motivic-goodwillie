# motivic-goodwillie — program register

Every item lands compiling under Rocq 9 against Coq-HoTT with coqchk clean and zero Admitted. No item retracts a claim; each names the construction that makes the ambient claim true.

1. Numeral notation for nat literals and a Boolean case-analysis tactic are installed so that successor towers and quadruple destructs disappear from proofs.
2. The lemma bounded_measure_limit_zero is hoisted to the arithmetic core and its six specialized clones are derived from it in one line each.
3. The QPos order module is completed with qpos_le, totality, decidability, and multiplication compatibility on both sides, supplying the missing mirror of qpos_mult_lt_l.
4. QPos is quotiented by cross-multiplication into a genuine rational type, the order and HasMinimalPositive descending to the quotient, so every theorem holds representation-independently.
5. The reproved Boolean lemmas and global instances such as andb_assoc and hset_unit are audited against the HoTT library, importing what exists and localizing what must stay.
6. The relations nat_lt and nat_le are reflected into the library leq once and their lemma farm is ported through the reflection, so the computational shape justifies the definitions rather than a duplicate suite.
7. IsIsomorphism over hset hom-types is proven to be an hprop, enabling clean rewriting of inverse data.
8. GradedCat, ZGradedCat, and GradedSHCat are re-derived as ShiftCat instances, their parallel lemma suites collapsing into one-line corollaries of the generic construction.
9. The loop functor of GradedCat is completed by factoring through the Z-graded refinement, where composition holds and the functor packages, so the abandoned morphism action becomes a genuine endofunctor.
10. The theorem the title promises is stated and proven: the approximation isomorphisms past the stabilization stage compose with stab_tower_limit into IsTowerLimit exhibiting X itself as the limit of fam_P_tower X, the unit cone commuting through lev_change_comp_mono and nat_leb_succ_r.
11. The capstone threshold is unified and sharpened: a single tower exhibits stabilization at its support bound and provable failure at the predecessor stage.
12. Connectivity is defined as the least occupied level and the equivalence between weight-boundedness and fiber connectivity growth is proven, the in-model analogue of the classical analyticity criterion.
13. The advertised Milnor sequence is assembled: lim is defined as the kernel of one_minus_shift, the four-term exact sequence through the two products and lim one is proven, and lim-one vanishing is connected to uniqueness in IsTowerLimit.
14. The on-the-nose path equality wct_obs_matches is generalized to two-sided qpos_le bounds between the categorical measure and the arithmetic obstruction, strengthening every theorem that consumes it and admitting the richer models the strict form excludes.
15. WeightMeasure acquires morphism-respecting axioms, fiber measures bounded by totals and non-increase along towers, from which the matching conditions are derived.
16. DistinguishedTriangle acquires a hom-level exactness condition ruling out all-zero triangles, and ZeroFiberInTriangleImpliesIso becomes a theorem rather than a standing hypothesis.
17. Every lemma with an unused hypothesis, eventually_iso_tower_stabilizes_via_measure and ZGraded_complete_convergence_chain foremost, routes its stabilization stage through the measure witness, so every stated hypothesis is load-bearing.
18. WeightedCategoricalTower and TowerInStable each receive one non-degenerate instance, giving the two flagship convergence theorems honest instantiations.
19. goodwillie_tower_stabilizes is instantiated non-trivially by discharging its hypotheses for FamGoodwillieTower restricted to boundedly-supported families, where ZeroMeasureImpliesZeroObj becomes decidable.
20. FiberData is upgraded with the universal property of a genuine fiber, uniqueness of factorization through the inclusion, so that zero composites no longer qualify by default and the obstruction objects are canonically determined.
21. Genuine mapping cones for arbitrary maps are constructed in FamCat, replacing the cofiber that returns either zero or the untouched target.
22. The converse detection is proven for FamGoodwillieTower: a tower map that is an isomorphism forces its layer to vanish, so layers never over-report.
23. The carrier is abelianized: the level-family category is rebuilt with abelian-group-valued levels, where levelwise biproducts and pushouts exist, so the n-excision predicate becomes positively testable.
24. FamP n is proven n-excisive, and if the guard-cube notion refuses the proof the cube notion is repaired until the theorem holds.
25. The n-homogeneous predicate is defined and FamD n is proven to satisfy it, earning the name layer.
26. The equivalence between hom from the suspension of X to Y and hom from X to the loops of Y is derived from the ProperStable triangle identities and used at least once.
27. The opposite-category machinery pays rent with one dual theorem, tower limits exchanged with tower colimits under duality_principle.
28. CField is completed to a genuine field, addition and inverses joining the multiplication so that straight-line homotopies run through the full field structure and the record earns its name.
29. CScheme acquires structure that determines cs_dim and cs_sing, such as polynomial maps on affine zero-sets, so dimension is a theorem about the carrier rather than a tag beside it.
30. Concrete-scheme morphisms are restricted to polynomial maps and Nisnevich squares are formulated with the decomposition condition, pushing descent beyond representables.
31. Fiber products of concrete schemes are constructed with their dimension and singularity bookkeeping, and CompatibleFamily is restated on the pullbacks its quantification over all test schemes silently encodes.
32. The Nisnevich section earns its name: the completely decomposed condition is added and one statement is proven that plain joint surjectivity cannot deliver.
33. One actual functor on CSch is defined, its level family is derived from the geometry, and the tower is run on it, so the scheme world and the tower world exchange morphisms.
34. The field bm_levels is derived from the blowdown fiber data rather than stored, occupancy at each level coming from actual fibers, with support below bm_exc_dim proven from bm_exc_below.
35. A1Homotopic is closed into an equivalence relation by chains, proven a congruence, the localization of CSch inverting the affine line is constructed as a quotient category, and the point is proven equivalent to the affine line there.
36. The field gms_level becomes load-bearing: spectrum morphisms are rebuilt as levelwise scheme maps compatible with bonding, so the levels carry the homotopical content their name promises.
37. MotivicSH is rebuilt with homs that depend on the objects, as level-family maps or graded groups, so that nonzero spectra fall into more than two isomorphism classes.
38. The codiscrete Scheme category is recast as the file's explicit degenerate model, each of its SH convergence theorems paired with the MotivicSH statement that supersedes it, so no vacuous theorem parades as content and the collapse suite stands as the counterexample it is.
39. BaseField is fused with CField so that its carrier, constants, and characteristic are read by the concrete scheme layer, leaving no record whose fields nothing consumes.
40. One spectral sequence is produced whose bound and detection hypotheses are theorems: the spectral sequence of a weight-filtered tower, its first page identified with the graded pieces of the WeightFiltration and its differential measure derived.
41. Abutment is stated and proven: past the degeneration page the stable page is identified with the graded pieces of a limit object.
42. MotivicSH is triangulated with hom-abelian shift categories and genuine cofiber sequences, and the slice spectral sequence of the tower runs through wss_degeneration as a formal weighted analogue of Levine's convergence.
43. The total weight earns its factors: one theorem exhibits cs_dim changing the stage of stabilization, realized by an obstruction measure calibrated to dimension rather than absorbed into the constant.
