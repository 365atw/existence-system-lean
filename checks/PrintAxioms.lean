import ExistenceSystem

/-!
Axiom audit list. Each line is one fully qualified `#print axioms` declaration.
Qualified names keep a union merge (`merge=union` in `.gitattributes`) from
depending on an `open` scope.

`checks/item-logs.sh` writes `logs/<Item>-build.log` and
`logs/<Item>-print-axioms.log`. Pass an item name to record only that item.
-/

#print axioms ExistenceSystem.KL1.existsUnique_pos_root
#print axioms ExistenceSystem.KL1.r_mem_Ioo
#print axioms ExistenceSystem.KL1.r_pow
#print axioms ExistenceSystem.KL1.r_succ_lt
#print axioms ExistenceSystem.KL1.one_lt_r
#print axioms ExistenceSystem.KL1.tendsto_r
#print axioms ExistenceSystem.KL1.planar_face
#print axioms ExistenceSystem.KL1.spatial_face
#print axioms ExistenceSystem.KL1.rho_cube
#print axioms ExistenceSystem.KL1.rho_unique

#print axioms ExistenceSystem.KL2.minpoly_omega
#print axioms ExistenceSystem.KL2.minpoly_phi
#print axioms ExistenceSystem.KL2.carries_minpoly
#print axioms ExistenceSystem.KL2.agree

#print axioms ExistenceSystem.KL3.V_branches
#print axioms ExistenceSystem.KL3.V_even
#print axioms ExistenceSystem.KL3.hasDerivAt_V
#print axioms ExistenceSystem.KL3.deriv_V_eq_zero_iff
#print axioms ExistenceSystem.KL3.critical_set
#print axioms ExistenceSystem.KL3.critical_set_ncard
#print axioms ExistenceSystem.KL3.minimizers_eq
#print axioms ExistenceSystem.KL3.minimizers_nontrivial
#print axioms ExistenceSystem.KL3.minimizers_ncard
#print axioms ExistenceSystem.KL3.flow_eq_neg_deriv

#print axioms ExistenceSystem.KL12.free
#print axioms ExistenceSystem.KL12.bound
#print axioms ExistenceSystem.KL12.free_iff_not_bound_of_nonneg
#print axioms ExistenceSystem.KL12.residual_free
#print axioms ExistenceSystem.KL12.not_bound_residual
#print axioms ExistenceSystem.KL5.starVec_dot
#print axioms ExistenceSystem.KL5.starVec_dot_self
#print axioms ExistenceSystem.KL5.starVec_dot_ne_neg_half
#print axioms ExistenceSystem.KL5.no_closed_triad
#print axioms ExistenceSystem.KL5.secondShell_sq_add
#print axioms ExistenceSystem.KL5.secondShell_sq_sub
#print axioms ExistenceSystem.KL5.secondShell_ratio_sq
#print axioms ExistenceSystem.KL5.shell_ratio
#print axioms ExistenceSystem.KL5.mixed_triad_long_not_unit

#print axioms ExistenceSystem.KL13.residual_pos

#print axioms ExistenceSystem.KL16.sigmaIdeal_prime_pow
#print axioms ExistenceSystem.KL16.sigmaIdeal_mul_coprime
#print axioms ExistenceSystem.KL16.four_perfect_ideals
#print axioms ExistenceSystem.KL16.sigma_orbits
#print axioms ExistenceSystem.KL16.classical_perfect_numbers_do_not_lift
#print axioms ExistenceSystem.KL16.KL16_four_perfect_ideals

#print axioms ExistenceSystem.KL14.fixedPoint_eq_zero
#print axioms ExistenceSystem.KL14.ascent_tendsto_zero

#print axioms ExistenceSystem.KL15.piSwap_eq_m

#print axioms ExistenceSystem.KL18.lucas
#print axioms ExistenceSystem.KL18.goldenRatio_pow_add_goldenConj_pow
#print axioms ExistenceSystem.KL18.goldenConj_eq_one_sub
#print axioms ExistenceSystem.KL18.conj_neg
#print axioms ExistenceSystem.KL18.conj_abs_lt_one
#print axioms ExistenceSystem.KL18.goldenConj_pow_tendsto_zero
#print axioms ExistenceSystem.KL18.fold_coil
#print axioms ExistenceSystem.KL18.fold_coil_zero
#print axioms ExistenceSystem.KL18.goldenRatio_pow_succ_irrational
#print axioms ExistenceSystem.KL18.goldenConj_pow_succ_irrational
#print axioms ExistenceSystem.KL18.face_par_irrational
#print axioms ExistenceSystem.KL18.face_perp_irrational
#print axioms ExistenceSystem.KL18.norm_pair
#print axioms ExistenceSystem.KL18.norm_pair_abs
#print axioms ExistenceSystem.KL18.residual_pos
#print axioms ExistenceSystem.KL18.residual_tendsto_zero
#print axioms ExistenceSystem.KL18.piswap_trace

#print axioms ExistenceSystem.KL20.piParallel_coe_eq
#print axioms ExistenceSystem.KL20.piPerp_coe_eq
#print axioms ExistenceSystem.KL20.sigma_transfer
#print axioms ExistenceSystem.KL20.rawT_mulVec_injective
#print axioms ExistenceSystem.KL20.rawT_par
#print axioms ExistenceSystem.KL20.rawT_perp
#print axioms ExistenceSystem.KL20.joint_vanishing
#print axioms ExistenceSystem.KL20.no_integer_relation
#print axioms ExistenceSystem.KL20.parProj_lattice
#print axioms ExistenceSystem.KL20.perp_inter_lattice_eq_zero
#print axioms ExistenceSystem.KL20.parProj_injOn_lattice

#print axioms ExistenceSystem.KL22.piParallel_sum
#print axioms ExistenceSystem.KL22.monoPhase_eq
#print axioms ExistenceSystem.KL22.phase_trivial_iff
#print axioms ExistenceSystem.KL22.piParallel_zero_iff_closure
#print axioms ExistenceSystem.KL22.admissible_iff_closure

#print axioms ExistenceSystem.KL27.fold_eq_lucas
#print axioms ExistenceSystem.KL27.diff_eq_sqrt5_fib
#print axioms ExistenceSystem.KL27.no_rational_root
#print axioms ExistenceSystem.KL27.sigma_involutive
#print axioms ExistenceSystem.KL27.traceForm_self_adjoint
#print axioms ExistenceSystem.KL27.fold_fixed
#print axioms ExistenceSystem.KL27.fold_eq_algebraMap_trace
#print axioms ExistenceSystem.KL27.diff_antifixed
#print axioms ExistenceSystem.KL27.diff_trace_zero
#print axioms ExistenceSystem.KL27.star_algebraMap_rat
#print axioms ExistenceSystem.KL27.reflection_decomposition
#print axioms ExistenceSystem.KL27.fixed_iff_scalar
#print axioms ExistenceSystem.KL27.antifixed_iff_trace_zero
#print axioms ExistenceSystem.KL27.eigenvalue_eq_one_or_neg_one

#print axioms ExistenceSystem.KL23.fsIndicator_chi3
#print axioms ExistenceSystem.KL23.fsIndicator_chi3'
#print axioms ExistenceSystem.KL23.dim_perp_not_complex_type
#print axioms ExistenceSystem.KL23.dim_perp_not_quaternionic_type
#print axioms ExistenceSystem.KL23.inequivalent
#print axioms ExistenceSystem.KL23.chi_ne_on_c5
#print axioms ExistenceSystem.KL23.irreducible_chi3
#print axioms ExistenceSystem.KL23.mixed_block_vanishes
#print axioms ExistenceSystem.KL23.perp_block_scalar
#print axioms ExistenceSystem.KL23.par_block_scalar
#print axioms ExistenceSystem.KL23.two_rate

#print axioms ExistenceSystem.KL17.preserves_splitting
#print axioms ExistenceSystem.KL17.par_block_scalar
#print axioms ExistenceSystem.KL17.perp_block_scalar
#print axioms ExistenceSystem.KL17.isotropic_one_ratio
#print axioms ExistenceSystem.KL17.same_ratio_every_direction

#print axioms ExistenceSystem.Lucas.lucas
#print axioms ExistenceSystem.Lucas.lucas_zero
#print axioms ExistenceSystem.Lucas.lucas_one
#print axioms ExistenceSystem.Lucas.lucas_add_two
#print axioms ExistenceSystem.Lucas.goldenRatio_pow_add_goldenConj_pow

#print axioms ExistenceSystem.Quadratic.no_rational_root
#print axioms ExistenceSystem.Quadratic.sigma_involutive
#print axioms ExistenceSystem.Quadratic.fold_eq_trace
#print axioms ExistenceSystem.Quadratic.trace_def'
#print axioms ExistenceSystem.Quadratic.norm_def'
#print axioms ExistenceSystem.Quadratic.coeZphi_star
#print axioms ExistenceSystem.Quadratic.omega_sq_zphi
#print axioms ExistenceSystem.Quadratic.embedPhi_mk
#print axioms ExistenceSystem.Quadratic.embedPsi_mk
#print axioms ExistenceSystem.Quadratic.embedPhi_omega
#print axioms ExistenceSystem.Quadratic.embedPsi_omega
#print axioms ExistenceSystem.Quadratic.embedPsi_eq_embedPhi_star
#print axioms ExistenceSystem.Quadratic.embedPhi_coeZphi
#print axioms ExistenceSystem.Quadratic.embedPsi_coeZphi
#print axioms ExistenceSystem.Quadratic.embedPhi_injective

#print axioms ExistenceSystem.Icosahedral.qDot_eq
#print axioms ExistenceSystem.Icosahedral.qDot_self
#print axioms ExistenceSystem.Icosahedral.qDot_off
#print axioms ExistenceSystem.Icosahedral.sign_ne_zero_off
#print axioms ExistenceSystem.Icosahedral.qVec_dot
#print axioms ExistenceSystem.Icosahedral.qVecPerp_dot
#print axioms ExistenceSystem.Icosahedral.qVec_norm_sq
#print axioms ExistenceSystem.Icosahedral.qVecPerp_norm_sq
#print axioms ExistenceSystem.Icosahedral.two_add_phi_eq_sqrt5_mul_phi
#print axioms ExistenceSystem.Icosahedral.phi_div_norm_sq
#print axioms ExistenceSystem.Icosahedral.psi_div_conj_norm_sq
#print axioms ExistenceSystem.Icosahedral.length_ratio
#print axioms ExistenceSystem.Icosahedral.three_sub_phi_eq
#print axioms ExistenceSystem.Icosahedral.Q_dot_self
#print axioms ExistenceSystem.Icosahedral.Q_dot_off
#print axioms ExistenceSystem.Icosahedral.Qperp_dot_self
#print axioms ExistenceSystem.Icosahedral.Qperp_dot_off
#print axioms ExistenceSystem.Icosahedral.row_dot
#print axioms ExistenceSystem.Icosahedral.row_orthonormal
#print axioms ExistenceSystem.Icosahedral.A_mul_transpose
#print axioms ExistenceSystem.Icosahedral.A_transpose_mul
#print axioms ExistenceSystem.Icosahedral.mem_lattice_rows
#print axioms ExistenceSystem.Icosahedral.rawM_eq_images
#print axioms ExistenceSystem.Icosahedral.det_rawM
#print axioms ExistenceSystem.Icosahedral.det_rawM_ne_zero
#print axioms ExistenceSystem.Icosahedral.piJoin_bijective

#print axioms ExistenceSystem.IcosahedralRep.classSize_sum
#print axioms ExistenceSystem.IcosahedralRep.star_chi3
#print axioms ExistenceSystem.IcosahedralRep.embedPsi_chi3
#print axioms ExistenceSystem.IcosahedralRep.charInner_chi3_self
#print axioms ExistenceSystem.IcosahedralRep.charInner_chi3_cross

#print axioms ExistenceSystem.Landau.cc_eq_two_re
#print axioms ExistenceSystem.Landau.shellQuad_uniform
#print axioms ExistenceSystem.Landau.shellQuartic_uniform
#print axioms ExistenceSystem.Landau.t1_saturated
#print axioms ExistenceSystem.Landau.t2_saturated
#print axioms ExistenceSystem.Landau.sum_evalTerm
#print axioms ExistenceSystem.Landau.sectorJ_div_vol
#print axioms ExistenceSystem.Landau.slave_exact
#print axioms ExistenceSystem.Landau.uniform_slave

#print axioms ExistenceSystem.EulerLagrange.el_gradientOnly
#print axioms ExistenceSystem.EulerLagrange.variation_at_zero
#print axioms ExistenceSystem.EulerLagrange.hasDerivAt_setEntry
#print axioms ExistenceSystem.EulerLagrange.hasDerivAt_gradDensity
#print axioms ExistenceSystem.EulerLagrange.ibp_line
#print axioms ExistenceSystem.EulerLagrange.ibp_frechet
#print axioms ExistenceSystem.EulerLagrange.ibp_sum_directions

#print axioms ExistenceSystem.TheThing.int_coord_unique
#print axioms ExistenceSystem.TheThing.discr_eq_neg_twenty
#print axioms ExistenceSystem.TheThing.intNorm_pair
#print axioms ExistenceSystem.TheThing.isUnit_iff
#print axioms ExistenceSystem.TheThing.no_norm_two
#print axioms ExistenceSystem.TheThing.no_norm_three
#print axioms ExistenceSystem.TheThing.nrRealPlaces_eq_zero
#print axioms ExistenceSystem.TheThing.nrComplexPlaces_eq_one
#print axioms ExistenceSystem.TheThing.minkowskiBound_lt_three
#print axioms ExistenceSystem.TheThing.p₂_sq
#print axioms ExistenceSystem.TheThing.p₃_mul_p₃'
#print axioms ExistenceSystem.TheThing.p₂_mul_p₃
#print axioms ExistenceSystem.TheThing.p₂_mul_p₃'
#print axioms ExistenceSystem.TheThing.span_six_eq_two_mul_three
#print axioms ExistenceSystem.TheThing.span_six_eq_prime_factors
#print axioms ExistenceSystem.TheThing.span_six_eq_conj_factors
#print axioms ExistenceSystem.TheThing.six_factorizations
#print axioms ExistenceSystem.TheThing.irreducible_two
#print axioms ExistenceSystem.TheThing.irreducible_three
#print axioms ExistenceSystem.TheThing.irreducible_one_add
#print axioms ExistenceSystem.TheThing.irreducible_one_sub
#print axioms ExistenceSystem.TheThing.two_not_prime
#print axioms ExistenceSystem.TheThing.not_uniqueFactorization_elements
#print axioms ExistenceSystem.TheThing.uniqueFactorization_ideals
#print axioms ExistenceSystem.TheThing.factorizations_not_associated
#print axioms ExistenceSystem.TheThing.p₂_not_principal
#print axioms ExistenceSystem.TheThing.p₂_order
#print axioms ExistenceSystem.TheThing.eq_p₂_of_absNorm_eq_two
#print axioms ExistenceSystem.TheThing.class_eq_one_or_p₂
#print axioms ExistenceSystem.TheThing.classGroup_card_eq_two
#print axioms ExistenceSystem.TheThing.classNumber_eq_two
#print axioms ExistenceSystem.TheThing.classGroup_isCyclic
#print axioms ExistenceSystem.TheThing.not_principalIdealRing
#print axioms ExistenceSystem.TheThing.p₃_class_eq_p₂
#print axioms ExistenceSystem.TheThing.p₃'_class_eq_p₂
#print axioms ExistenceSystem.TheThing.χ_neg20_level
#print axioms ExistenceSystem.TheThing.χ_neg20_eq_mul
#print axioms ExistenceSystem.TheThing.three_char_eq_one
#print axioms ExistenceSystem.TheThing.legendre_five_neg_one
#print axioms ExistenceSystem.TheThing.χ_neg20_split
#print axioms ExistenceSystem.TheThing.split_of_norm_two_p
#print axioms ExistenceSystem.TheThing.seven_home
#print axioms ExistenceSystem.TheThing.sixtySeven_home
#print axioms ExistenceSystem.TheThing.oneHundredSeven_home

#print axioms ExistenceSystem.Summit.χ_neg20_eq_legendre_negFive
#print axioms ExistenceSystem.Summit.χ_neg20ℂ_odd
#print axioms ExistenceSystem.Summit.two_ramifies
#print axioms ExistenceSystem.Summit.five_ramifies
#print axioms ExistenceSystem.Summit.splitting_of_χ
#print axioms ExistenceSystem.Summit.zetaProduct_trivialZero
#print axioms ExistenceSystem.Summit.zetaProduct_ne_zero_of_one_le_re
#print axioms ExistenceSystem.Summit.rh_one_piece
#print axioms ExistenceSystem.Summit.alphaForced
#print axioms ExistenceSystem.Summit.noTerminatingOmega
#print axioms ExistenceSystem.Summit.hasDerivAt_re_criticalPoint
#print axioms ExistenceSystem.Summit.hasDerivAt_criticalTrajectory
#print axioms ExistenceSystem.Summit.criticalTangent_eq
#print axioms ExistenceSystem.KL10.inner_gradient_eq_zero
#print axioms ExistenceSystem.KL10.hasDerivAt_coord
#print axioms ExistenceSystem.KL10.conserved_coord
#print axioms ExistenceSystem.KL10.conserved_along_neg_gradient
#print axioms ExistenceSystem.Summit.χ_neg20ℂ_isPrimitive
#print axioms ExistenceSystem.Summit.nontrivialZero_one_sub
#print axioms ExistenceSystem.Summit.riemannZeta_one_sub_eq_zero
#print axioms ExistenceSystem.Summit.LFunction_one_sub_eq_zero
#print axioms ExistenceSystem.Summit.riemannZeta_neg_odd_ne_zero
#print axioms ExistenceSystem.Summit.zeroLine_of_stripZeroFree
#print axioms ExistenceSystem.Summit.stripZeroFree_iff
#print axioms ExistenceSystem.Summit.continuation_eq_zetaProduct
#print axioms ExistenceSystem.Summit.idealCount_mul
#print axioms ExistenceSystem.Summit.halfPlane_holds
#print axioms ExistenceSystem.Summit.idealCount_split
#print axioms ExistenceSystem.Summit.idealCount_ramified
#print axioms ExistenceSystem.Summit.idealCount_inert
#print axioms ExistenceSystem.Summit.idealCountA_eq_zetaMul
#print axioms ExistenceSystem.Summit.zetaProduct_isContinuation
#print axioms ExistenceSystem.Summit.continuation_unique
#print axioms ExistenceSystem.Summit.frontier_of_stripZeroFree
#print axioms ExistenceSystem.Summit.stripZeroFree_of_frontier
#print axioms ExistenceSystem.Summit.rh_one_piece_strip
#print axioms ExistenceSystem.Summit.hasDerivAt_transverse
#print axioms ExistenceSystem.Summit.criticalTangent_eq_I_mul_transverse
#print axioms ExistenceSystem.Summit.reflection_fixes_alpha

#print axioms ExistenceSystem.KL19.energyDensity_eq_of_freq_eq
#print axioms ExistenceSystem.KL19.freq_eq_of_energyDensity_eq
#print axioms ExistenceSystem.KL19.energyDensity_eq_of_liClass
#print axioms ExistenceSystem.KL19.not_ranks_of_liClass
#print axioms ExistenceSystem.KL19.no_better

#print axioms ExistenceSystem.KL21.embedPsi_injective
#print axioms ExistenceSystem.KL21.sigma_transfer_perp
#print axioms ExistenceSystem.KL21.no_integer_relation_perp
#print axioms ExistenceSystem.KL21.perpProj_lattice
#print axioms ExistenceSystem.KL21.par_inter_lattice_eq_zero
#print axioms ExistenceSystem.KL21.perpProj_injOn_lattice
#print axioms ExistenceSystem.KL21.closure_transfer
#print axioms ExistenceSystem.KL21.starMap_apply
#print axioms ExistenceSystem.KL21.starMap_add
#print axioms ExistenceSystem.KL21.starMap_zero

#print axioms ExistenceSystem.KL7.constant_on_free
#print axioms ExistenceSystem.KL7.isMinOn_free
#print axioms ExistenceSystem.KL7.fderiv_free_eq_zero
#print axioms ExistenceSystem.KL7.free_deriv_is_zero_fun
#print axioms ExistenceSystem.KL7.mixed_hessian_block_vanishes
#print axioms ExistenceSystem.KL7.no_implicit_function_route
#print axioms ExistenceSystem.KL7.factorsThrough_quotient
#print axioms ExistenceSystem.KL7.par_perp_inner_zero
#print axioms ExistenceSystem.KL7.par_inf_perp_eq_bot
#print axioms ExistenceSystem.KL7.tensorChar_values
#print axioms ExistenceSystem.KL7.no_identity_component
#print axioms ExistenceSystem.KL7.piPerp_sum
#print axioms ExistenceSystem.KL7.phasonPhase_eq
#print axioms ExistenceSystem.KL7.phasonPhase_trivial_iff_closure
#print axioms ExistenceSystem.KL7.physical_iff_phason
#print axioms ExistenceSystem.KL7.no_admissible_perturbation_selects
#print axioms ExistenceSystem.KL24.recipVec_sum
#print axioms ExistenceSystem.KL24.monoPhasePerp_eq
#print axioms ExistenceSystem.KL24.landau_term_phase_trivial
#print axioms ExistenceSystem.KL24.landau_pointwise_w_independent
#print axioms ExistenceSystem.KL24.landau_bare_partial_zero
#print axioms ExistenceSystem.KL24.displayed_piStress
#print axioms ExistenceSystem.KL24.gradient_only_divergence
#print axioms ExistenceSystem.KL6.ampPhasePerp_norm
#print axioms ExistenceSystem.KL6.norm_mul_ampPhasePerp
#print axioms ExistenceSystem.KL6.piPerp_sum
#print axioms ExistenceSystem.KL6.monoPhasePerp_eq
#print axioms ExistenceSystem.KL6.piPerp_zero_iff_closure
#print axioms ExistenceSystem.KL6.admissible_phason_invariant
#print axioms ExistenceSystem.KL6.phason_invariant_iff_closure
#print axioms ExistenceSystem.KL6.uniform_shift_grad_zero
#print axioms ExistenceSystem.KL6.elastic_uniform_invariant
#print axioms ExistenceSystem.KL6.phasonTerm_const
#print axioms ExistenceSystem.KL6.no_pinning_fderiv
#print axioms ExistenceSystem.KL6.no_pinning_iteratedFDeriv
#print axioms ExistenceSystem.KL6.perp_coefficient_zero
#print axioms ExistenceSystem.KL6.summand_zero
#print axioms ExistenceSystem.KL6.no_pinning

#print axioms ExistenceSystem.KL8.normalFormLocus_volume_zero
#print axioms ExistenceSystem.KL8.normalForm_degenerate_card
#print axioms ExistenceSystem.KL8.bias_breaks_branches
#print axioms ExistenceSystem.KL8.icosahedral_indifferent_full
#print axioms ExistenceSystem.KL8.symmetry_protected
#print axioms ExistenceSystem.KL8.unbreakable
#print axioms ExistenceSystem.KL8.identity_at_every_order
#print axioms ExistenceSystem.KL8.symmetry_protection_upgrade

#print axioms ExistenceSystem.KL9.lyapunov_rate
#print axioms ExistenceSystem.KL9.lyapunov_nonpos
#print axioms ExistenceSystem.KL9.lyapunov_eq_zero_iff
#print axioms ExistenceSystem.KL9.trajectory_unique
#print axioms ExistenceSystem.KL9.uniform_shift_grad_zero
#print axioms ExistenceSystem.KL9.uniform_equilibrium
#print axioms ExistenceSystem.KL9.uniform_equilibria_fill_Eperp
#print axioms ExistenceSystem.KL9.flux_integral_zero
#print axioms ExistenceSystem.KL9.mean_conserved
#print axioms ExistenceSystem.KL9.mean_conserved_of_boundary
#print axioms ExistenceSystem.KL9.relaxes_to_mean
