import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.MeanValue

open Metric Real Complex

open scoped Nat

variable {r R M : ℝ} {c z : ℂ} {f : ℂ → ℂ} {n : ℕ}

lemma deriv_eq_circleAverage (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) :
    circleAverage (fun z ↦ (1 / (z - c) ^ n) • f z) c R = iteratedDeriv n f c / n ! := by
  rw [circleAverage_eq_circleIntegral hR.ne.symm, inv_smul_eq_iff₀ (by simp)]
  convert hf.circleIntegral_one_div_sub_center_pow_smul hR n using 1
  · congr
    ext
    simp [pow_succ]
    field
  · simp; field

theorem norm_iteratedDeriv_le_of_re_le (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ z ∈ sphere c R, (f z).re ≤ M) (hn : 1 ≤ n) :
    ‖iteratedDeriv n f c‖ ≤ 2 * n ! * M / R ^ n := by
  have hRabs : |R| = R := abs_of_pos hR
  have hfs : ContinuousOn f (sphere c R) := hf.continuousOn_ball.mono sphere_subset_closedBall
  have hzne : ∀ z ∈ sphere c R, z - c ≠ 0 := fun z hz h =>
    hR.ne (by simpa [h] using mem_sphere_iff_norm.mp hz)
  have hconj : ∀ z ∈ sphere c R, (starRingEnd ℂ) (z - c) = (R : ℂ) ^ 2 / (z - c) := by
    intro z hz
    rw [eq_div_iff (hzne z hz), mul_comm, mul_conj, normSq_eq_norm_sq,
      mem_sphere_iff_norm.mp hz]
    norm_cast
  -- Step 1 : for holomorphic `w` the average of `conj w / (z - c) ^ n` vanishes.  Indeed the mean
  -- value property kills the average of `w * (z - c) ^ n`, and conjugating it turns `conj (z - c)`
  -- into `R ^ 2 / (z - c)` on the circle.
  have key : ∀ w : ℂ → ℂ, DiffContOnCl ℂ w (ball c R) →
      circleAverage (fun z => (starRingEnd ℂ) (w z) / (z - c) ^ n) c R = 0 := by
    intro w hw
    have hwc : ContinuousOn w (closedBall c R) := hw.continuousOn_ball
    have hdc : DiffContOnCl ℂ (fun z => w z * (z - c) ^ n) (ball c |R|) := by
      rw [hRabs]
      exact DiffContOnCl.mk_ball (hw.differentiableOn.mul (by fun_prop)) (hwc.mul (by fun_prop))
    have h1 : circleAverage (fun z => w z * (z - c) ^ n) c R = 0 := by
      rw [hdc.circleAverage]
      simp [zero_pow (by omega : n ≠ 0)]
    have hint : CircleIntegrable (fun z => w z * (z - c) ^ n) c R :=
      ContinuousOn.circleIntegrable hR.le ((hwc.mono sphere_subset_closedBall).mul (by fun_prop))
    have h2 : circleAverage (fun z => (starRingEnd ℂ) (w z * (z - c) ^ n)) c R = 0 := by
      have h := (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.circleAverage_comp_comm hint
      simp only [Function.comp_def, h1, map_zero] at h
      exact h
    have h3 : circleAverage
          (fun z => ((R : ℂ) ^ 2) ^ n • ((starRingEnd ℂ) (w z) / (z - c) ^ n)) c R = 0 := by
      rw [← h2]
      refine circleAverage_congr_sphere fun z hz => ?_
      rw [hRabs] at hz
      simp only [smul_eq_mul, map_mul, map_pow, hconj z hz, div_pow]
      ring
    rw [circleAverage_fun_smul, smul_eq_zero] at h3
    exact h3.resolve_left (pow_ne_zero _ (pow_ne_zero _ (ofReal_ne_zero.mpr hR.ne')))
  -- integrability of `g / (z - c) ^ n` on the circle
  have hcirc : ∀ g : ℂ → ℂ, ContinuousOn g (sphere c R) →
      CircleIntegrable (fun z => g z / (z - c) ^ n) c R := fun g hg =>
    ContinuousOn.circleIntegrable hR.le
      (hg.div (by fun_prop) fun z hz => pow_ne_zero _ (hzne z hz))
  have hI1 : CircleIntegrable (fun z => f z / (z - c) ^ n) c R := hcirc f hfs
  have hI2 : CircleIntegrable (fun z => (starRingEnd ℂ) (f z) / (z - c) ^ n) c R :=
    hcirc _ (continuous_conj.comp_continuousOn hfs)
  have hI12 : CircleIntegrable
      (fun z => f z / (z - c) ^ n + (starRingEnd ℂ) (f z) / (z - c) ^ n) c R := hI1.add hI2
  have hreI : CircleIntegrable (fun z => (f z).re) c R :=
    ContinuousOn.circleIntegrable hR.le (continuous_re.comp_continuousOn hfs)
  -- Step 2 : Cauchy's integral formula for derivatives, as a circle average
  have E3 : circleAverage (fun z => f z / (z - c) ^ n) c R = iteratedDeriv n f c / n ! := by
    convert deriv_eq_circleAverage hf hR
    simp
    field
  -- the average of the constant term vanishes too, by `key` applied to `w = 1`
  have E2 : circleAverage (fun z => (2 * M : ℂ) / (z - c) ^ n) c R = 0 := by
    have h := key (fun _ => 1) diffContOnCl_const
    simp only [map_one] at h
    rw [show (fun z : ℂ => (2 * M : ℂ) / (z - c) ^ n)
        = fun z => (2 * M : ℂ) • ((1 : ℂ) / (z - c) ^ n) from
      funext fun z => by simp [smul_eq_mul, div_eq_mul_inv], circleAverage_fun_smul, h, smul_zero]
  -- Step 3 : since `f + conj f - 2 * M = 2 * (Re f - M)` and the last two averages vanish,
  -- the derivative is the average of a real-part expression
  set G : ℂ → ℂ := fun z => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n with hG
  have hGsum : circleAverage G c R = iteratedDeriv n f c / n ! := by
    rw [hG, show (fun z : ℂ => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n)
        = fun z => (f z / (z - c) ^ n + (starRingEnd ℂ) (f z) / (z - c) ^ n)
            - (2 * M : ℂ) / (z - c) ^ n from by
          funext z
          rw [← add_div, ← sub_div]
          congr 1
          rw [add_conj]
          push_cast
          ring,
      circleAverage_fun_sub hI12 (hcirc _ continuousOn_const),
      circleAverage_fun_add hI1 hI2, key f hf, E2, E3]
    ring
  -- Step 4 : the mean value property for the real part, which vanishes since `f c = 0`
  have hre : circleAverage (fun z => (f z).re) c R = 0 := by
    have hmv : circleAverage f c R = f c :=
      (show DiffContOnCl ℂ f (ball c |R|) by rwa [hRabs]).circleAverage
    simpa [Function.comp_def, hmv, hf0] using reCLM.circleAverage_comp_comm
      (c := c) (R := R) (ContinuousOn.circleIntegrable hR.le hfs)
  -- Step 5 : the norm of the average is at most the average of the norm, which the mean value
  -- property evaluates
  calc ‖iteratedDeriv n f c‖
      = (n ! : ℝ) * ‖circleAverage G c R‖ := by
        rw [hGsum, norm_div, Complex.norm_natCast, mul_div_cancel₀ _
          (Nat.cast_ne_zero.mpr n.factorial_ne_zero : ((n ! : ℝ)) ≠ 0)]
    _ ≤ (n ! : ℝ) * circleAverage (fun z => ‖G z‖) c R := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [circleAverage_def, circleAverage_def, norm_smul, smul_eq_mul, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le) (by positivity)
    _ = (n ! : ℝ) * (2 * M / R ^ n) := by
        rw [circleAverage_congr_sphere (f₂ := fun z => (2 / R ^ n) • (M - (f z).re)) fun z hz => by
              rw [hRabs] at hz
              simp only [hG, norm_div, norm_real, Real.norm_eq_abs, norm_pow,
                mem_sphere_iff_norm.mp hz, smul_eq_mul,
                abs_of_nonpos (by linarith [hM z hz] : 2 * ((f z).re - M) ≤ 0)]
              ring,
          circleAverage_fun_smul, smul_eq_mul,
          circleAverage_fun_sub (circleIntegrable_const M c R) hreI, circleAverage_const, hre]
        ring
    _ = 2 * n ! * M / R ^ n := by ring

/-- **Maximum principle for the real part**: if `Re f ≤ M` on the circle `sphere c R`, then
`Re f ≤ M` on the whole closed disc `closedBall c R`. -/
theorem re_le_of_re_le_of_mem_closedBall (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hM : ∀ w ∈ sphere c R, (f w).re ≤ M)
    (hz : z ∈ closedBall c R) : (f z).re ≤ M := by
  -- apply the maximum modulus principle to `exp ∘ f`, whose modulus is `exp (Re f)`
  refine Real.exp_le_exp.mp ?_
  rw [← Complex.norm_exp]
  refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    ⟨hf.differentiableOn.cexp, hf.continuousOn.cexp⟩ (fun w hw => ?_)
    (by rwa [closure_ball c hR.ne'])
  rw [frontier_ball c hR.ne'] at hw
  exact Complex.norm_exp (f w) ▸ Real.exp_le_exp.mpr (hM w hw)

/-- **Borel-Carathéodory theorem**: if `f` is holomorphic on the disc `ball c R`, continuous up to
the boundary, vanishes at `c`, and satisfies `Re f ≤ M` on the boundary circle, then it is bounded
by `2 * r * M / (R - r)` on the smaller disc of radius `r < R`. -/
theorem norm_le_of_re_le (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ w ∈ sphere c R, (f w).re ≤ M) (hr : r < R) (hz : ‖z - c‖ ≤ r) :
    ‖f z‖ ≤ 2 * r * M / (R - r) := by
  have hs0 : (0 : ℝ) ≤ ‖z - c‖ := norm_nonneg _
  have hsr : ‖z - c‖ < R := lt_of_le_of_lt hz hr
  have hne : R - ‖z - c‖ ≠ 0 := sub_ne_zero.mpr hsr.ne'
  have hA : 0 ≤ M := by
    simpa [hf0] using re_le_of_re_le_of_mem_closedBall hR hf hM (mem_closedBall_self hR.le)
  -- the Taylor series of `f` at `c`, whose constant term vanishes since `f c = 0`
  have hsum : HasSum
      (fun n : ℕ => (((n + 1)! : ℂ))⁻¹ • (z - c) ^ (n + 1) • iteratedDeriv (n + 1) f c) (f z) := by
    simpa [hf0] using (hasSum_nat_add_iff' 1).mpr (hasSum_taylorSeries_on_ball
      hf.differentiableOn (by rw [mem_ball, dist_eq_norm]; exact hsr))
  -- each Taylor coefficient is bounded by the estimate on the derivatives at the centre
  have hcoeff : ∀ n : ℕ, ‖(((n + 1)! : ℂ))⁻¹ • (z - c) ^ (n + 1) • iteratedDeriv (n + 1) f c‖
      ≤ 2 * M * (‖z - c‖ / R) * (‖z - c‖ / R) ^ n := by
    intro n
    have hd := norm_iteratedDeriv_le_of_re_le hR hf hf0 hM (Nat.le_add_left 1 n)
    have hfac : (0 : ℝ) < ((n + 1)! : ℝ) := by positivity
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow]
    calc (((n + 1)! : ℝ))⁻¹ * (‖z - c‖ ^ (n + 1) * ‖iteratedDeriv (n + 1) f c‖)
        ≤ (((n + 1)! : ℝ))⁻¹ * (‖z - c‖ ^ (n + 1) * (2 * ((n + 1)! : ℝ) * M / R ^ (n + 1))) := by
          gcongr
      _ = 2 * M * (‖z - c‖ / R) * (‖z - c‖ / R) ^ n := by
          rw [div_pow, pow_succ]
          field_simp
          ring
  -- compare with a geometric series, then let the radius grow to `r`
  refine (hsum.norm_le_of_bounded ((hasSum_geometric_of_lt_one (by positivity)
    ((div_lt_one hR).mpr hsr)).mul_left (2 * M * (‖z - c‖ / R))) hcoeff).trans ?_
  rw [show 2 * M * (‖z - c‖ / R) * (1 - ‖z - c‖ / R)⁻¹ = 2 * M * ‖z - c‖ / (R - ‖z - c‖) from by
      rw [eq_div_iff hne]
      field_simp,
    div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg hA (sub_nonneg.mpr hz)) hR.le]

/-- **Borel-Carathéodory theorem for the derivative**: under the hypotheses of `norm_le_of_re_le`,
the derivative of `f` on the disc of radius `r < R` is bounded by `2 * R * M / (R - r) ^ 2`. -/
theorem norm_deriv_le_of_re_le (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ w ∈ sphere c R, (f w).re ≤ M) (hr : r < R) (hz : ‖z - c‖ ≤ r) :
    ‖deriv f z‖ ≤ 2 * R * M / (R - r) ^ 2 := by
  have hs0 : (0 : ℝ) ≤ ‖z - c‖ := norm_nonneg _
  have hsr : ‖z - c‖ < R := lt_of_le_of_lt hz hr
  have hA : 0 ≤ M := by
    simpa [hf0] using re_le_of_re_le_of_mem_closedBall hR hf hM (mem_closedBall_self hR.le)
  -- `deriv f` is again holomorphic on the disc, so it is the sum of its Taylor series at `c`
  have hsum : HasSum
      (fun n : ℕ => ((n ! : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv (n + 1) f c) (deriv f z) := by
    have h := Complex.hasSum_taylorSeries_on_ball (hf.differentiableOn.deriv isOpen_ball)
      (show z ∈ ball c R by rw [mem_ball, dist_eq_norm]; exact hsr)
    simpa only [← iteratedDeriv_succ'] using h
  -- each coefficient is bounded by the estimate on the derivatives at the centre
  have hcoeff : ∀ n : ℕ, ‖((n ! : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv (n + 1) f c‖
      ≤ 2 * M / R * (((n : ℝ) + 1) * (‖z - c‖ / R) ^ n) := by
    intro n
    have hd := norm_iteratedDeriv_le_of_re_le hR hf hf0 hM (Nat.le_add_left 1 n)
    have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
    have hfacsucc : (((n + 1)! : ℝ)) = ((n : ℝ) + 1) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow, div_pow]
    calc ((n ! : ℝ))⁻¹ * (‖z - c‖ ^ n * ‖iteratedDeriv (n + 1) f c‖)
        ≤ ((n ! : ℝ))⁻¹ * (‖z - c‖ ^ n
            * (2 * ((n + 1)! : ℝ) * M / R ^ (n + 1))) := by gcongr
      _ = 2 * M / R * (((n : ℝ) + 1) * (‖z - c‖ ^ n / R ^ n)) := by
          rw [hfacsucc]
          field_simp
          ring
  -- sum the majorant : a differentiated geometric series
  have hgeo : HasSum (fun n : ℕ => 2 * M / R * (((n : ℝ) + 1) * (‖z - c‖ / R) ^ n))
      (2 * R * M / (R - ‖z - c‖) ^ 2) := by
    have hne : R - ‖z - c‖ ≠ 0 := sub_ne_zero.mpr hsr.ne'
    have h1 := (hasSum_choose_mul_geometric_of_norm_lt_one 1
      (show ‖(‖z - c‖ / R : ℝ)‖ < 1 by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact (div_lt_one hR).mpr hsr)).mul_left (2 * M / R)
    rw [show 2 * M / R * (1 / (1 - ‖z - c‖ / R) ^ (1 + 1)) = 2 * R * M / (R - ‖z - c‖) ^ 2 from by
      rw [show (1 : ℝ) - ‖z - c‖ / R = (R - ‖z - c‖) / R by field_simp, div_pow, one_div_div,
        div_mul_div_comm,
        div_eq_div_iff (mul_ne_zero hR.ne' (pow_ne_zero _ hne)) (pow_ne_zero 2 hne)]
      ring] at h1
    simpa using h1
  -- conclude, and let the radius grow to `r`
  refine (hsum.norm_le_of_bounded hgeo hcoeff).trans ?_
  rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos (by linarith) 2)]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
