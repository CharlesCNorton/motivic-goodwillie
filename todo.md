# motivic-goodwillie — program register

1. Compile the file end-to-end in CI against a pinned Rocq and HoTT-library version, and run Print Assumptions on every headline theorem to certify the axiom base is exactly {Funext}, with {Univalence} confined to its declared sites.
2. Split the monolith into a dependency-ordered module DAG for incremental builds and legible logical structure.
3. Audit universe polymorphism and consistency across MotivicSpace, SH, FamCat, and the quotient constructions.
4. Descend the capstone convergence bounds along qrat_class into QRat.
5. Exhibit a non-integer-valued but weight-bounded discrete obstruction to exercise bounded_measure_limit_zero and the QRat descent on a rational sequence, extending past the integer-valued instances.
6. Re-derive cokernel-quotient effectiveness through a decidable coset encoding and remove Univalence from the file's closure.
7. Prove fam_count window-invariant past the support bound and make bfam_measure canonical.
8. Instantiate TowerWeightMeasure on the decreasing-fiber tower and fire wct_of_tower_measure on the instance.
9. Upgrade TowerWithFibers to carry FiberUniversal at every stage and re-instantiate the concrete towers, so zero_obstructions_imply_stabilization rests on genuine fibers throughout.
10. Prove the shift-category cofiber a weak cokernel by levelwise case analysis and upgrade the ZGraded and MotivicSH cofiber triangles to ExactDistinguishedTriangle instances.
11. Package the FamCat mapping cones from fam_cone_universal as ExactDistinguishedTriangle instances over FamPreStable, tying the cone construction to the exactness machinery.
12. Prove GradedToShift full and faithful and transport the gm and gsm law suites across the identification.
13. Make the nat-graded loop functorial and give GradedCat its own susp-loop adjunction, retiring GradedLoopThroughZ as a first-class functor, or state the dimension-zero asymmetry as a theorem.
14. Replace the identity placeholders on BFamPreStable with window-truncated suspension and loop and their unit and counit transformations.
15. Construct the forgetful functor from BFamCat to FamCat with commuting tower squares.
16. Rebuild the guarded polynomial tower over AbFamCat with layers as levelwise kernels and cokernels, and rerun the capstone convergence with homology-valued obstruction measures.
17. Define cross-effects through the AbFamCat biproducts and prove the n-th cross-effect of FamP n trivial and the (n+1)-st nontrivial.
18. Prove FamD n and its AbFamCat analog determined by their n-th cross-effect, classifying the n-homogeneous layers.
19. Prove a FamP excision theorem that consumes the strongly-cocartesian hypothesis, sending cocartesian cubes below the level to cartesian ones, rather than routing through all_iso_cube_cartesian.
20. Prove an excision theorem over AbFamCat whose cartesian conclusion is derived from the strongly cocartesian squares, making the pushout hypothesis load-bearing.
21. Introduce an AdditivePreStableCategory refinement with hom-abelian-group enrichment and biproducts, fusing MotivicSH_hom_ab, abfam_biprod, and MotivicSH_compose_biadditive, so triangles live in an additive setting and ps_zero_morphism is the additive zero.
22. Strengthen DistinguishedTriangle and PreStableCategory toward a triangulated axiomatization: prove TR1 and TR3 for the concrete instances and either prove or scope out the octahedral axiom, since rotation closure alone is insufficient.
23. Construct sequential limits in FamCat and AbFamCat for non-stabilizing towers, beyond the eventually-constant case handled by stab_tower_limit.
24. Feed the levelwise abelian-group tower from an AbFamCat tower into the Milnor machinery and prove lim-one vanishes for boundedly-supported input, recovering tower-limit equals object, tying the AbTower section to the geometry.
25. State and prove the dual cofiltered-colimit convergence theorem via duality_principle and opposite_proper_stable, upgrading iso_cotower_colimit and opposite_tower_stabilizes to a substantive result.
26. Construct a weighted spectral sequence with a nonzero early differential and derive its vanishing past the weight bound from the filtration jumps.
27. Add exhaustiveness and separatedness to WeightFiltration, realize them on an instance, and reconstruct the filtered group from its graded pieces for finite filtrations.
28. Restate the weighted Levine degeneration on the Int-graded slice filtration with pages indexed by slice degree and occupancy read from SliceLayer.
29. Construct fiber products of affine data as mask intersections and prove the pullback dimension equal to the free-coordinate count.
30. Assemble the category of affine data with PolyMor homs and prove it a subcategory of CSch through pm_apply.
31. Prove the completely-decomposed NisSquares generate a Grothendieck pretopology, stable under pullback through the affine-data fiber products, containing isomorphisms, with local character.
32. Generate a Cover from the two legs of a NisSquare, discharge its surjectivity by the decomposed condition, and instantiate representable_is_sheaf on it.
33. Construct a non-representable sheaf, prove sheaves closed under limits, and connect NisSquare to Cover to descent through compatible_iff_pullbacks, extending the sheaf theory past representable_is_sheaf.
34. Repair the tower weight to descend through A1Loc or to an A1-invariant quantity: cproj_A1_equiv makes cs_product X (cA1 F) A1-equivalent to X while cs_dim increments, so cs_dim is not A1-invariant and the weight indexing the tower should be motivic rather than dimensional.
35. Make cs_sing load-bearing in the tower itself rather than only inside w_total: index the level family by two-variable dimension-singularity occupancy and prove biconvergence, so singularity data drives stabilization.
36. Define BlowupModel occupancy from the blowdown's fiber structure rather than nat_leb k bm_exc_dim, so bm_fiber_witness drives the tower rather than paralleling it.
37. Construct the localization functor from CSch to A1Loc and prove its universal property: every functor inverting the homotopy relation factors through it uniquely.
38. Prove the class of every A1-equivalence an isomorphism in A1Loc and recover the point-affine-line isomorphism as an instance.
39. Extend scheme_level_family to a functor on the dimension-monotone subcategory of CSch and restate cs_dim_changes_stage through the induced tower maps.
40. Exhibit SH as a degenerate quotient of MotivicSH2 through an explicit functor, so the all-morphisms-iso collapse is a proven quotient, or retire the codiscrete SchemeCategory, MotivicSpectrum, and SH tower to a declared baseline.
41. Derive spm_A1_level as the product of the level map with the identity once the scheme category carries products, and prove its compatibility square.
42. Rebuild the MotivicSH2 homs as levelwise polynomial scheme maps compatible with bonding.
43. Equip MotivicSH2 with the zero spectrum, suspension and loop through the level-family shift, and restate the convergence theorems with the object-dependent homs.
44. Prove the test spectra pairwise non-isomorphic in both directions for all distinct dimensions and package an injection from nat into the isomorphism classes of MotivicSH2.
45. Add a companion non-vacuity witness with a provably minimal nonzero stabilization stage to every top-level convergence predicate, extending the genuine_threshold pattern up to the headline theorems.
46. Add an Example and Compute regression suite pinning computed values to catch silent breakage.
47. Add a scope statement to the file header calibrating the title to the definitions, separating the codiscrete baseline, the combinatorial graded and FamCat models, and the concrete-scheme layer.
48. Regenerate the README with each completed result named beside its backing theorem.
