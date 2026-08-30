import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.MeanValue

open Metric Real Complex

open scoped Nat

theorem norm_iteratedDeriv_le_of_re_le {R : ℝ} {f : ℂ → ℂ} {c : ℂ} {n : ℕ} {M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ z ∈ sphere c R, (f z).re ≤ M) (hn : 1 ≤ n) :
    ‖iteratedDeriv n f c‖ ≤ 2 * n ! * (M - (f c).re) / R ^ n := by
  have hRabs : |R| = R := abs_of_pos hR
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hfc : ContinuousOn f (closedBall c R) := hf.continuousOn_ball
  have hzne : ∀ z ∈ sphere c R, z - c ≠ 0 := by
    intro z hz hz0
    rw [mem_sphere_iff_norm, hz0, norm_zero] at hz
    exact hR.ne hz
  have hconj : ∀ z ∈ sphere c R, (starRingEnd ℂ) (z - c) = (R : ℂ) ^ 2 / (z - c) := by
    intro z hz
    have h1 : (z - c) * (starRingEnd ℂ) (z - c) = ((R : ℂ)) ^ 2 := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, mem_sphere_iff_norm.mp hz]
    field_simp [hzne z hz] at h1 ⊢
    linear_combination h1
  -- Step 1 : the average of `conj w / (z - c) ^ n` vanishes
  have key : ∀ w : ℂ → ℂ, DiffContOnCl ℂ w (ball c R) →
      circleAverage (fun z => (starRingEnd ℂ) (w z) / (z - c) ^ n) c R = 0 := by
    intro w hw
    have hwc : ContinuousOn w (closedBall c R) := hw.continuousOn_ball
    have hdc : DiffContOnCl ℂ (fun z => w z * (z - c) ^ n) (ball c |R|) := by
      rw [hRabs]
      exact DiffContOnCl.mk_ball (hw.differentiableOn.mul (by fun_prop)) (hwc.mul (by fun_prop))
    have h1 : circleAverage (fun z => w z * (z - c) ^ n) c R = 0 := by
      rw [hdc.circleAverage]; simp [zero_pow hn0]
    have hint : CircleIntegrable (fun z => w z * (z - c) ^ n) c R :=
      ContinuousOn.circleIntegrable hR.le ((hwc.mono sphere_subset_closedBall).mul (by fun_prop))
    have h2 : circleAverage (fun z => (starRingEnd ℂ) (w z * (z - c) ^ n)) c R = 0 := by
      have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.circleAverage_comp_comm hint
      simp only [Function.comp_def] at this
      rw [show (fun z => (starRingEnd ℂ) (w z * (z - c) ^ n)) =
        fun z => (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap (w z * (z - c) ^ n) from rfl,
        this, h1]
      simp
    have h3 : circleAverage
          (fun z => ((R : ℂ) ^ 2) ^ n • ((starRingEnd ℂ) (w z) / (z - c) ^ n)) c R
        = circleAverage (fun z => (starRingEnd ℂ) (w z * (z - c) ^ n)) c R := by
      apply circleAverage_congr_sphere
      intro z hz
      rw [hRabs] at hz
      simp only [smul_eq_mul, map_mul, map_pow, hconj z hz, div_pow]
      ring
    rw [h2, circleAverage_fun_smul, smul_eq_zero] at h3
    rcases h3 with h3 | h3
    · exact absurd h3 (pow_ne_zero _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hR.ne')))
    · exact h3
  -- integrability of `g / (z - c) ^ n` on the circle
  have hcirc : ∀ g : ℂ → ℂ, ContinuousOn g (sphere c R) →
      CircleIntegrable (fun z => g z / (z - c) ^ n) c R := fun g hg =>
    ContinuousOn.circleIntegrable hR.le
      (hg.div (by fun_prop) fun z hz => pow_ne_zero _ (hzne z hz))
  have hfs : ContinuousOn f (sphere c R) := hfc.mono sphere_subset_closedBall
  have hI1 : CircleIntegrable (fun z => f z / (z - c) ^ n) c R := hcirc f hfs
  have hI2 : CircleIntegrable (fun z => (starRingEnd ℂ) (f z) / (z - c) ^ n) c R :=
    hcirc _ (Complex.continuous_conj.comp_continuousOn hfs)
  have hI3 : CircleIntegrable (fun z => (2 * M : ℂ) / (z - c) ^ n) c R :=
    hcirc _ continuousOn_const
  have hI12 : CircleIntegrable
      (fun z => f z / (z - c) ^ n + (starRingEnd ℂ) (f z) / (z - c) ^ n) c R := hI1.add hI2
  have hreI : CircleIntegrable (fun z => (f z).re) c R :=
    ContinuousOn.circleIntegrable hR.le (Complex.continuous_re.comp_continuousOn hfs)
  -- Step 2 : Cauchy's integral formula for derivatives, as a circle average
  have E3 : circleAverage (fun z => f z / (z - c) ^ n) c R = iteratedDeriv n f c / n ! := by
    rw [circleAverage_eq_circleIntegral hR.ne']
    have hI : (∮ z in C(c, R), (z - c)⁻¹ • (f z / (z - c) ^ n))
        = ∮ z in C(c, R), (1 / (z - c) ^ (n + 1)) • f z := by
      congr 1
      funext z
      simp only [smul_eq_mul, pow_succ, mul_inv, div_eq_mul_inv]
      ring
    rw [hI, hf.circleIntegral_one_div_sub_center_pow_smul hR n, smul_smul, smul_eq_mul]
    have h2pi : (2 * (π : ℂ) * I) ≠ 0 := Complex.two_pi_I_ne_zero
    have hfac : ((n ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  -- Step 3 : the two vanishing averages
  have E1 : circleAverage (fun z => (starRingEnd ℂ) (f z) / (z - c) ^ n) c R = 0 := key f hf
  have E2 : circleAverage (fun z => (2 * M : ℂ) / (z - c) ^ n) c R = 0 := by
    have h := key (fun _ => 1) diffContOnCl_const
    simp only [map_one] at h
    have : (fun z : ℂ => (2 * M : ℂ) / (z - c) ^ n)
        = fun z => (2 * M : ℂ) • ((1 : ℂ) / (z - c) ^ n) := by
      funext z; simp [smul_eq_mul, div_eq_mul_inv]
    rw [this, circleAverage_fun_smul, h, smul_zero]
  -- Step 4 : rewrite the derivative as the average of a real-part expression
  have hGsum : circleAverage (fun z => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n) c R
      = iteratedDeriv n f c / n ! := by
    have hEq : (fun z : ℂ => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n)
        = fun z => (f z / (z - c) ^ n + (starRingEnd ℂ) (f z) / (z - c) ^ n)
            - (2 * M : ℂ) / (z - c) ^ n := by
      funext z
      rw [← add_div, ← sub_div]
      congr 1
      rw [Complex.add_conj]
      push_cast
      ring
    rw [hEq, circleAverage_fun_sub hI12 hI3, circleAverage_fun_add hI1 hI2, E1, E2, E3]
    ring
  -- Step 5 : the mean value property for the real part
  have hre : circleAverage (fun z => (f z).re) c R = (f c).re := by
    have hfi : CircleIntegrable f c R := ContinuousOn.circleIntegrable hR.le hfs
    have hcomm := Complex.reCLM.circleAverage_comp_comm (c := c) (R := R) hfi
    simp only [Function.comp_def, Complex.reCLM_apply] at hcomm
    have hmv : circleAverage f c R = f c := by
      have hf' : DiffContOnCl ℂ f (ball c |R|) := by rwa [hRabs]
      exact hf'.circleAverage
    rw [hcomm, hmv]
  -- Step 6 : the norm of an average is at most the average of the norm
  have hnorm : ∀ g : ℂ → ℂ, ‖circleAverage g c R‖ ≤ circleAverage (fun z => ‖g z‖) c R := by
    intro g
    rw [circleAverage_def, circleAverage_def, norm_smul, smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le) (by positivity)
  -- Step 7 : estimate the average
  have hbound : ‖circleAverage (fun z => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n) c R‖
      ≤ 2 * (M - (f c).re) / R ^ n := by
    refine (hnorm _).trans ?_
    have hcongr : circleAverage
        (fun z => ‖((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n‖) c R
        = circleAverage (fun z => (2 / R ^ n) • (M - (f z).re)) c R := by
      apply circleAverage_congr_sphere
      intro z hz
      rw [hRabs] at hz
      have hzn : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, hzn, smul_eq_mul]
      rw [abs_of_nonpos (by linarith [hM z hz] : 2 * ((f z).re - M) ≤ 0)]
      ring
    rw [hcongr, circleAverage_fun_smul, smul_eq_mul,
      circleAverage_fun_sub (circleIntegrable_const M c R) hreI, circleAverage_const, hre]
    exact le_of_eq (by ring)
  -- Conclusion
  have hexp : iteratedDeriv n f c
      = (n ! : ℂ) * circleAverage (fun z => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n) c R := by
    rw [hGsum, mul_comm]
    exact (div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)).symm
  rw [hexp, norm_mul, Complex.norm_natCast]
  calc (n ! : ℝ) * ‖circleAverage (fun z => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n) c R‖
      ≤ (n ! : ℝ) * (2 * (M - (f c).re) / R ^ n) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 * n ! * (M - (f c).re) / R ^ n := by ring

/-- **Maximum principle for the real part**: if `Re f ≤ M` on the circle `sphere c R`, then
`Re f ≤ M` on the whole closed disc `closedBall c R`. -/
theorem re_le_of_re_le_of_mem_closedBall {R : ℝ} {f : ℂ → ℂ} {c z : ℂ} {M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ w ∈ sphere c R, (f w).re ≤ M)
    (hz : z ∈ closedBall c R) : (f z).re ≤ M := by
  have hexp : DiffContOnCl ℂ (fun w => Complex.exp (f w)) (ball c R) :=
    ⟨hf.differentiableOn.cexp, hf.continuousOn.cexp⟩
  have hb : ∀ w ∈ frontier (ball c R), ‖Complex.exp (f w)‖ ≤ Real.exp M := by
    intro w hw
    rw [frontier_ball c hR.ne'] at hw
    exact Complex.norm_exp (f w) ▸ Real.exp_le_exp.mpr (hM w hw)
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hexp hb
    (show z ∈ closure (ball c R) by rwa [closure_ball c hR.ne'])
  rw [Complex.norm_exp] at h
  exact Real.exp_le_exp.mp h

/-- **Borel-Carathéodory theorem**: if `f` is holomorphic on the disc `ball c R`, continuous up to
the boundary, and `Re f ≤ M` on the boundary circle, then on the smaller disc of radius `r < R`
the function is bounded in terms of `M - Re (f c)`. -/
theorem norm_sub_le_of_re_le {R r : ℝ} {f : ℂ → ℂ} {c z : ℂ} {M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ w ∈ sphere c R, (f w).re ≤ M)
    (hr : r < R) (hz : ‖z - c‖ ≤ r) :
    ‖f z - f c‖ ≤ 2 * r * (M - (f c).re) / (R - r) := by
  have hs0 : (0 : ℝ) ≤ ‖z - c‖ := norm_nonneg _
  have hsr : ‖z - c‖ < R := lt_of_le_of_lt hz hr
  have hA : 0 ≤ M - (f c).re :=
    sub_nonneg.mpr (re_le_of_re_le_of_mem_closedBall hR hf hM (mem_closedBall_self hR.le))
  -- the Taylor series of `f` at `c`, with its constant term removed
  have hsum : HasSum (fun n : ℕ => ((n ! : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) :=
    Complex.hasSum_taylorSeries_on_ball hf.differentiableOn
      (by rw [mem_ball, dist_eq_norm]; exact hsr)
  have hsum1 : HasSum
      (fun n : ℕ => (((n + 1)! : ℂ))⁻¹ • (z - c) ^ (n + 1) • iteratedDeriv (n + 1) f c)
      (f z - f c) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hsum
  -- each Taylor coefficient is bounded by the Cauchy-type estimate at the centre
  have hcoeff : ∀ n : ℕ,
      ‖(((n + 1)! : ℂ))⁻¹ • (z - c) ^ (n + 1) • iteratedDeriv (n + 1) f c‖
      ≤ 2 * (M - (f c).re) * (‖z - c‖ / R) ^ (n + 1) := by
    intro n
    have hd := norm_iteratedDeriv_le_of_re_le hR hf hM (Nat.le_add_left 1 n)
    have hfac : (0 : ℝ) < ((n + 1)! : ℝ) := by positivity
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow, div_pow]
    calc (((n + 1)! : ℝ))⁻¹ * (‖z - c‖ ^ (n + 1) * ‖iteratedDeriv (n + 1) f c‖)
        ≤ (((n + 1)! : ℝ))⁻¹ * (‖z - c‖ ^ (n + 1)
            * (2 * ((n + 1)! : ℝ) * (M - (f c).re) / R ^ (n + 1))) := by gcongr
      _ = 2 * (M - (f c).re) * (‖z - c‖ ^ (n + 1) / R ^ (n + 1)) := by field_simp
  -- sum the geometric majorant
  have hgeo : HasSum (fun n : ℕ => 2 * (M - (f c).re) * (‖z - c‖ / R) ^ (n + 1))
      (2 * (M - (f c).re) * ‖z - c‖ / (R - ‖z - c‖)) := by
    have h1 := (hasSum_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ ‖z - c‖ / R)
      ((div_lt_one hR).mpr hsr)).mul_left (2 * (M - (f c).re) * (‖z - c‖ / R))
    have h2 : (fun n : ℕ => 2 * (M - (f c).re) * (‖z - c‖ / R) * (‖z - c‖ / R) ^ n)
        = fun n : ℕ => 2 * (M - (f c).re) * (‖z - c‖ / R) ^ (n + 1) := by
      funext n; rw [pow_succ]; ring
    have hne : R - ‖z - c‖ ≠ 0 := sub_ne_zero.mpr hsr.ne'
    have h3 : 2 * (M - (f c).re) * (‖z - c‖ / R) * (1 - ‖z - c‖ / R)⁻¹
        = 2 * (M - (f c).re) * ‖z - c‖ / (R - ‖z - c‖) := by
      rw [eq_div_iff hne]
      field_simp
    rwa [h2, h3] at h1
  have hzs : ‖f z - f c‖ ≤ 2 * (M - (f c).re) * ‖z - c‖ / (R - ‖z - c‖) :=
    hsum1.norm_le_of_bounded hgeo hcoeff
  -- monotonicity in the radius
  refine hzs.trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg hA (sub_nonneg.mpr hz)) hR.le]

/-- **Borel-Carathéodory theorem for the derivative**: under the hypotheses of
`norm_sub_le_of_re_le`, the derivative of `f` on the disc of radius `r < R` is bounded in terms of
`M - Re (f c)`. -/
theorem norm_deriv_le_of_re_le {R r : ℝ} {f : ℂ → ℂ} {c z : ℂ} {M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ w ∈ sphere c R, (f w).re ≤ M)
    (hr : r < R) (hz : ‖z - c‖ ≤ r) :
    ‖deriv f z‖ ≤ 2 * R * (M - (f c).re) / (R - r) ^ 2 := by
  have hs0 : (0 : ℝ) ≤ ‖z - c‖ := norm_nonneg _
  have hsr : ‖z - c‖ < R := lt_of_le_of_lt hz hr
  have hA : 0 ≤ M - (f c).re :=
    sub_nonneg.mpr (re_le_of_re_le_of_mem_closedBall hR hf hM (mem_closedBall_self hR.le))
  -- `deriv f` is again holomorphic on the disc, so it is the sum of its Taylor series at `c`
  have hsum : HasSum
      (fun n : ℕ => ((n ! : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv (n + 1) f c) (deriv f z) := by
    have h := Complex.hasSum_taylorSeries_on_ball (hf.differentiableOn.deriv isOpen_ball)
      (show z ∈ ball c R by rw [mem_ball, dist_eq_norm]; exact hsr)
    simpa only [← iteratedDeriv_succ'] using h
  -- each coefficient is bounded by the estimate on the derivatives at the centre
  have hcoeff : ∀ n : ℕ, ‖((n ! : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv (n + 1) f c‖
      ≤ 2 * (M - (f c).re) / R * (((n : ℝ) + 1) * (‖z - c‖ / R) ^ n) := by
    intro n
    have hd := norm_iteratedDeriv_le_of_re_le hR hf hM (Nat.le_add_left 1 n)
    have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
    have hfacsucc : (((n + 1)! : ℝ)) = ((n : ℝ) + 1) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow, div_pow]
    calc ((n ! : ℝ))⁻¹ * (‖z - c‖ ^ n * ‖iteratedDeriv (n + 1) f c‖)
        ≤ ((n ! : ℝ))⁻¹ * (‖z - c‖ ^ n
            * (2 * ((n + 1)! : ℝ) * (M - (f c).re) / R ^ (n + 1))) := by gcongr
      _ = 2 * (M - (f c).re) / R * (((n : ℝ) + 1) * (‖z - c‖ ^ n / R ^ n)) := by
          rw [hfacsucc]
          field_simp
          ring
  -- sum the majorant : a differentiated geometric series
  have hgeo : HasSum (fun n : ℕ => 2 * (M - (f c).re) / R * (((n : ℝ) + 1) * (‖z - c‖ / R) ^ n))
      (2 * R * (M - (f c).re) / (R - ‖z - c‖) ^ 2) := by
    have ht : ‖(‖z - c‖ / R : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_lt_one hR).mpr hsr
    have hne : R - ‖z - c‖ ≠ 0 := sub_ne_zero.mpr hsr.ne'
    have h1 := (hasSum_choose_mul_geometric_of_norm_lt_one 1 ht).mul_left
      (2 * (M - (f c).re) / R)
    have h2 : (fun n : ℕ => 2 * (M - (f c).re) / R
          * ((((n + 1).choose 1 : ℕ) : ℝ) * (‖z - c‖ / R) ^ n))
        = fun n : ℕ => 2 * (M - (f c).re) / R * (((n : ℝ) + 1) * (‖z - c‖ / R) ^ n) := by
      funext n
      simp [Nat.choose_one_right]
    have h3 : 2 * (M - (f c).re) / R * (1 / (1 - ‖z - c‖ / R) ^ (1 + 1))
        = 2 * R * (M - (f c).re) / (R - ‖z - c‖) ^ 2 := by
      rw [show (1 : ℝ) - ‖z - c‖ / R = (R - ‖z - c‖) / R by field_simp, div_pow, one_div_div,
        div_mul_div_comm,
        div_eq_div_iff (mul_ne_zero hR.ne' (pow_ne_zero _ hne)) (pow_ne_zero 2 hne)]
      ring
    rwa [h2, h3] at h1
  -- conclude, and let the radius grow to `r`
  refine (hsum.norm_le_of_bounded hgeo hcoeff).trans ?_
  rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos (by linarith) 2)]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
