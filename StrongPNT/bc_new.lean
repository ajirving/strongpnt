import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.MeanValue

open Metric Real Complex Filter Topology

open scoped Nat ComplexConjugate

variable {r R M : ℝ} {c z : ℂ} {f : ℂ → ℂ} {n : ℕ}

private lemma circleAverage_eq_iteratedDeriv_div_factorial (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) :
    circleAverage (fun z ↦ f z / (z - c) ^ n) c R = iteratedDeriv n f c / n ! := by
  rw [circleAverage_eq_circleIntegral hR.ne.symm, inv_smul_eq_iff₀ (by simp)]
  convert hf.circleIntegral_one_div_sub_center_pow_smul hR n using 1
  · congr
    ext
    simp [pow_succ]
    field
  · simp; field

theorem norm_circleAverage_le_circleAverage_norm {E : Type*} {f : ℂ → E} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖circleAverage f c R‖ ≤ circleAverage (fun z ↦ ‖f z‖) c R := by
  simp only  [circleAverage_def, norm_smul, smul_eq_mul]
  gcongr
  · simp [abs_of_nonneg pi_nonneg]
  exact intervalIntegral.norm_integral_le_integral_norm (by positivity)

theorem norm_iteratedDeriv_le_of_re_le_sphere (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ z ∈ sphere c R, (f z).re ≤ M) (hn : 1 ≤ n) :
    ‖iteratedDeriv n f c / (n !)‖ ≤ 2 * M / R ^ n := by
  have hRabs : |R| = R := abs_of_pos hR
  have hfs : ContinuousOn f (sphere c R) := hf.continuousOn_ball.mono sphere_subset_closedBall
  have hzne : ∀ z ∈ sphere c R, z - c ≠ 0 := fun z hz h =>
    hR.ne (by simpa [h] using mem_sphere_iff_norm.mp hz)
  have hconj : ∀ z ∈ sphere c R, conj (z - c) = (R : ℂ) ^ 2 / (z - c) := by
    intro z hz
    rw [eq_div_iff (hzne z hz), mul_comm, mul_conj, normSq_eq_norm_sq,
      mem_sphere_iff_norm.mp hz]
    norm_cast
  -- Step 1 : for holomorphic `w` the average of `conj w / (z - c) ^ n` vanishes.  Indeed the mean
  -- value property kills the average of `w * (z - c) ^ n`, and conjugating it turns `conj (z - c)`
  -- into `R ^ 2 / (z - c)` on the circle.
  have key : circleAverage (fun z => conj (f z) / (z - c) ^ n) c R = 0 := by
    have hwc : ContinuousOn f (closedBall c R) := hf.continuousOn_ball
    have hdc : DiffContOnCl ℂ (fun z => f z * (z - c) ^ n) (ball c |R|) := by
      rw [hRabs]
      exact DiffContOnCl.mk_ball (hf.differentiableOn.mul (by fun_prop)) (hwc.mul (by fun_prop))
    have h1 : circleAverage (fun z => f z * (z - c) ^ n) c R = 0 := by
      rw [hdc.circleAverage]
      simp [zero_pow (by omega : n ≠ 0)]
    have hint : CircleIntegrable (fun z => f z * (z - c) ^ n) c R :=
      ContinuousOn.circleIntegrable hR.le ((hwc.mono sphere_subset_closedBall).mul (by fun_prop))
    have h2 : circleAverage (fun z => conj (f z * (z - c) ^ n)) c R = 0 := by
      have h := (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.circleAverage_comp_comm hint
      simp only [Function.comp_def, h1, map_zero] at h
      exact h
    have h3 : circleAverage
          (fun z => ((R : ℂ) ^ 2) ^ n • (conj (f z) / (z - c) ^ n)) c R = 0 := by
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
  have hI2 : CircleIntegrable (fun z => conj (f z) / (z - c) ^ n) c R :=
    hcirc _ (continuous_conj.comp_continuousOn hfs)
  have hI12 : CircleIntegrable
      (fun z => f z / (z - c) ^ n + conj (f z) / (z - c) ^ n) c R := hI1.add hI2
  have hreI : CircleIntegrable (fun z => (f z).re) c R :=
    ContinuousOn.circleIntegrable hR.le (continuous_re.comp_continuousOn hfs)
  -- Step 2 : Cauchy's integral formula for derivatives, as a circle average
  have E3 : circleAverage (fun z => f z / (z - c) ^ n) c R = iteratedDeriv n f c / n ! := by
    exact circleAverage_eq_iteratedDeriv_div_factorial hf hR
  -- the average of the constant term vanishes too, by `key` applied to `w = 1`
  have E2 : circleAverage (fun z => (2 * M : ℂ) / (z - c) ^ n) c R = 0 := by
    convert circleAverage_eq_iteratedDeriv_div_factorial (n := n) (f := (fun z => (2 * M : ℂ))) diffContOnCl_const hR
    · simp [iteratedDeriv_const, (by linarith : n ≠ 0)]
  -- Step 3 : since `f + conj f - 2 * M = 2 * (Re f - M)` and the last two averages vanish,
  -- the derivative is the average of a real-part expression
  set G : ℂ → ℂ := fun z => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n with hG
  have hGsum : circleAverage G c R = iteratedDeriv n f c / n ! := by
    rw [hG, show (fun z : ℂ => ((2 * ((f z).re - M) : ℝ) : ℂ) / (z - c) ^ n)
        = fun z => (f z / (z - c) ^ n + conj (f z) / (z - c) ^ n)
            - (2 * M : ℂ) / (z - c) ^ n from by
          funext z
          rw [← add_div, ← sub_div]
          congr 1
          rw [add_conj]
          push_cast
          ring,
      circleAverage_fun_sub hI12 (hcirc _ continuousOn_const),
      circleAverage_fun_add hI1 hI2, key, E2, E3]
    ring
  -- Step 4 : the mean value property for the real part, which vanishes since `f c = 0`
  have hre : circleAverage (fun z => (f z).re) c R = 0 := by
    have hmv : circleAverage f c R = f c :=
      (show DiffContOnCl ℂ f (ball c |R|) by rwa [hRabs]).circleAverage
    simpa [Function.comp_def, hmv, hf0] using reCLM.circleAverage_comp_comm
      (c := c) (R := R) (ContinuousOn.circleIntegrable hR.le hfs)
  -- Step 5 : the norm of the average is at most the average of the norm, which the mean value
  -- property evaluates
  grw [← hGsum, norm_circleAverage_le_circleAverage_norm]
  apply le_of_eq
  simp only [hG, norm_div, norm_pow, norm_real, Real.norm_eq_abs]
  trans circleAverage (fun z => (2 / R ^ n) • (M - (f z).re)) c R
  · refine circleAverage_congr_sphere fun z hz ↦ ?_
    rw [hRabs] at hz
    rw [abs_of_nonpos (by linarith [hM z hz])]
    simp [mem_sphere_iff_norm.mp hz, smul_eq_mul]
    ring
  · rw [circleAverage_fun_smul, smul_eq_mul,
          circleAverage_fun_sub (circleIntegrable_const M c R) hreI, circleAverage_const, hre]
    ring

/-- The bound on the derivatives at the centre, assuming only that `f` is holomorphic on the open
disc and that `Re f ≤ M` there : apply the previous estimate on the discs of radius `R' < R` and
let `R'` tend to `R`. -/
theorem norm_iteratedDeriv_le_of_re_le (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ z ∈ ball c R, (f z).re ≤ M) (hn : 1 ≤ n) :
    ‖iteratedDeriv n f c / (n !)‖ ≤ 2 * M / R ^ n := by
  refine ge_of_tendsto (f := fun R' : ℝ => 2 * M / R' ^ n) (x := 𝓝[<] R)
    (((continuousAt_const.div (by fun_prop) (by positivity)).tendsto).mono_left
      nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_gt_nhds hR)] with R' hR'R hR'0
  have hsub : closedBall c R' ⊆ ball c R := closedBall_subset_ball hR'R
  exact norm_iteratedDeriv_le_of_re_le_sphere hR'0 (hf.diffContOnCl_ball hsub) hf0
    (fun z hz => hM z (hsub (sphere_subset_closedBall hz))) hn

/-- **Borel-Carathéodory theorem**: if `f` is holomorphic on the disc `ball c R`, vanishes at `c`,
and satisfies `Re f ≤ M` there, then it is bounded by `2 * r * M / (R - r)` on the smaller disc of
radius `r < R`. -/
theorem norm_le_of_re_le (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ w ∈ ball c R, (f w).re ≤ M) (hr : r < R) (hz : ‖z - c‖ ≤ r) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  have hsr : ‖z - c‖ < R := by linarith
  -- the Taylor series of `f` at `c`, whose constant term vanishes since `f c = 0`
  have hsum : HasSum
      (fun n : ℕ => (((n + 1)! : ℂ))⁻¹ • (z - c) ^ (n + 1) • iteratedDeriv (n + 1) f c) (f z) := by
    simpa [hf0] using (hasSum_nat_add_iff' 1).mpr (hasSum_taylorSeries_on_ball
      hf (by rw [mem_ball, dist_eq_norm]; exact hsr))
  convert hsum.norm_le_of_bounded ((hasSum_geometric_of_lt_one (by positivity)
    ((div_lt_one hR).mpr hsr)).mul_left (2 * M * (‖z - c‖ / R))) fun n ↦ _
  · field
  · simp only [smul_eq_mul]
    rw [mul_comm, mul_assoc, norm_mul, norm_pow]
    calc
    _ = ‖iteratedDeriv (n + 1) f c / ((n + 1) !)‖ * ‖z - c‖ ^ (n + 1) := by field_simp
    _ ≤ _ := by
      grw [norm_iteratedDeriv_le_of_re_le hR hf hf0 hM (Nat.le_add_left 1 n)]
      apply le_of_eq
      rw [pow_succ, pow_succ, div_pow]
      field

/-- **Borel-Carathéodory theorem for the derivative**: under the hypotheses of `norm_le_of_re_le`,
the derivative of `f` on the disc of radius `r < R` is bounded by `2 * R * M / (R - r) ^ 2`. -/
theorem norm_deriv_le_of_re_le (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ w ∈ ball c R, (f w).re ≤ M) (hr : r < R) (hz : ‖z - c‖ ≤ r) :
    ‖deriv f z‖ ≤ 2 * R * M / (R - r) ^ 2 := by
  have hs0 : (0 : ℝ) ≤ ‖z - c‖ := norm_nonneg _
  have hsr : ‖z - c‖ < R := lt_of_le_of_lt hz hr
  have hA : 0 ≤ M := by simpa [hf0] using hM c (mem_ball_self hR)
  -- `deriv f` is again holomorphic on the disc, so it is the sum of its Taylor series at `c`
  have hsum : HasSum
      (fun n : ℕ => ((n ! : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv (n + 1) f c) (deriv f z) := by
    have h := Complex.hasSum_taylorSeries_on_ball (hf.deriv isOpen_ball)
      (show z ∈ ball c R by rw [mem_ball, dist_eq_norm]; exact hsr)
    simpa only [← iteratedDeriv_succ'] using h
  have hgeo : HasSum (fun n : ℕ => 2 * M / R * (((n : ℝ) + 1) * (‖z - c‖ / R) ^ n))
      (2 * R * M / (R - ‖z - c‖) ^ 2) := by
    have hne : R - ‖z - c‖ ≠ 0 := sub_ne_zero.mpr hsr.ne'
    have h1 := (hasSum_choose_mul_geometric_of_norm_lt_one 1
      (show ‖(‖z - c‖ / R : ℝ)‖ < 1 by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact (div_lt_one hR).mpr hsr)).mul_left (2 * M / R)
    convert! h1 using 1
    · simp
    · rw [show (1 : ℝ) - ‖z - c‖ / R = (R - ‖z - c‖) / R by field_simp, div_pow]
      field
  grw [hsum.norm_le_of_bounded hgeo fun n ↦ ?_]
  · gcongr
  · have hfacsucc : (((n + 1)! : ℝ)) = ((n : ℝ) + 1) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow, div_pow]
    calc
    _ = ‖z - c‖ ^ n * (n + 1) * (‖iteratedDeriv (n + 1) f c‖ / (n + 1) !) := by
      rw [hfacsucc]
      field
    _ = ‖z - c‖ ^ n * (n + 1) * (‖iteratedDeriv (n + 1) f c / ((n + 1) !)‖) := by simp
    _ ≤ _ := by
      grw [norm_iteratedDeriv_le_of_re_le hR hf hf0 hM (Nat.le_add_left 1 n)]
      exact le_of_eq (by field)
