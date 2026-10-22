import ExistenceSystem
open ExistenceSystem.KL1
#print axioms existsUnique_pos_root
#print axioms r_mem_Ioo
#print axioms r_pow
#print axioms r_succ_lt
#print axioms one_lt_r
#print axioms tendsto_r
#print axioms planar_face
#print axioms spatial_face
#print axioms rho_cube
#print axioms rho_unique

open ExistenceSystem.KL2
#print axioms minpoly_omega
#print axioms minpoly_phi
#print axioms carries_minpoly
#print axioms agree

open ExistenceSystem.KL3
#print axioms V_branches
#print axioms V_even
#print axioms hasDerivAt_V
#print axioms deriv_V_eq_zero_iff
#print axioms critical_set
#print axioms critical_set_ncard
#print axioms minimizers_eq
#print axioms minimizers_nontrivial
#print axioms minimizers_ncard
#print axioms flow_eq_neg_deriv

#print axioms ExistenceSystem.KL13.residual_pos

#print axioms ExistenceSystem.KL14.fixedPoint_eq_zero
#print axioms ExistenceSystem.KL14.ascent_tendsto_zero

#print axioms ExistenceSystem.KL15.piSwap_eq_m

open ExistenceSystem.KL18
#print axioms lucas
#print axioms goldenRatio_pow_add_goldenConj_pow
#print axioms goldenConj_eq_one_sub
#print axioms conj_neg
#print axioms conj_abs_lt_one
#print axioms goldenConj_pow_tendsto_zero
#print axioms fold_coil
#print axioms fold_coil_zero
#print axioms goldenRatio_pow_succ_irrational
#print axioms goldenConj_pow_succ_irrational
#print axioms face_par_irrational
#print axioms face_perp_irrational
#print axioms norm_pair
#print axioms norm_pair_abs
#print axioms residual_pos
#print axioms residual_tendsto_zero
#print axioms piswap_trace

open ExistenceSystem.KL27
#print axioms ExistenceSystem.KL27.fold_eq_lucas
#print axioms diff_eq_sqrt5_fib
#print axioms no_rational_root
#print axioms sigma_involutive
#print axioms traceForm_self_adjoint
#print axioms fold_fixed
#print axioms fold_eq_algebraMap_trace
#print axioms diff_antifixed
#print axioms diff_trace_zero
#print axioms star_algebraMap_rat
#print axioms reflection_decomposition
#print axioms fixed_iff_scalar
#print axioms antifixed_iff_trace_zero
#print axioms eigenvalue_eq_one_or_neg_one

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

open ExistenceSystem.TheThing
#print axioms int_coord_unique
#print axioms discr_eq_neg_twenty
#print axioms intNorm_pair
#print axioms isUnit_iff
#print axioms no_norm_two
#print axioms no_norm_three
#print axioms nrRealPlaces_eq_zero
#print axioms nrComplexPlaces_eq_one
#print axioms minkowskiBound_lt_three
#print axioms p₂_sq
#print axioms p₃_mul_p₃'
#print axioms p₂_mul_p₃
#print axioms p₂_mul_p₃'
#print axioms span_six_eq_two_mul_three
#print axioms span_six_eq_prime_factors
#print axioms span_six_eq_conj_factors
#print axioms six_factorizations
#print axioms irreducible_two
#print axioms irreducible_three
#print axioms irreducible_one_add
#print axioms irreducible_one_sub
#print axioms two_not_prime
#print axioms not_uniqueFactorization_elements
#print axioms uniqueFactorization_ideals
#print axioms factorizations_not_associated
#print axioms p₂_not_principal
#print axioms p₂_order
#print axioms eq_p₂_of_absNorm_eq_two
#print axioms class_eq_one_or_p₂
#print axioms classGroup_card_eq_two
#print axioms classNumber_eq_two
#print axioms classGroup_isCyclic
#print axioms not_principalIdealRing
#print axioms p₃_class_eq_p₂
#print axioms p₃'_class_eq_p₂
#print axioms χ_neg20_level
#print axioms χ_neg20_eq_mul
#print axioms three_char_eq_one
#print axioms legendre_five_neg_one
#print axioms χ_neg20_split
#print axioms split_of_norm_two_p
#print axioms seven_home
#print axioms sixtySeven_home
#print axioms oneHundredSeven_home
