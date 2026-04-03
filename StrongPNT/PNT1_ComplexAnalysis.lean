import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Module.ModuleTopology
import PrimeNumberTheoremAnd.BorelCaratheodory

lemma lem_coseveny (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : Real.cos (-y * Real.log (n : ℝ)) = Real.cos (y * Real.log (n : ℝ)) := by
  rw [neg_mul, Real.cos_neg]


lemma lem_niyelog (n : ℕ) (hn : n ≥ 1) (y : ℝ) : (n : ℂ) ^ (-y * Complex.I) = Complex.exp (-y * Complex.I * Real.log (n : ℝ)) := by
  -- First show that (n : ℂ) ≠ 0
  have h1 : (n : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rw [← Nat.one_le_iff_ne_zero]
    exact hn
  -- Use cpow_def_of_ne_zero: x ^ y = exp (log x * y)
  rw [Complex.cpow_def_of_ne_zero h1]
  -- Now we have exp (log (n : ℂ) * (-y * Complex.I))
  -- Use natCast_log: Real.log n = log n
  rw [← Complex.natCast_log]
  -- Now we have exp (Real.log n * (-y * Complex.I))
  -- Use commutativity and associativity
  ring_nf

lemma lem_eacosalog (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : (Complex.exp (-y * Complex.I * Real.log (n : ℝ))).re = Real.cos (-y * Real.log (n : ℝ)) := by
  -- Let a = -y * Real.log (n : ℝ)
  let a := -y * Real.log (n : ℝ)
  -- Rewrite the expression to match lem_Reecos
  have h : -y * Complex.I * Real.log (n : ℝ) = a * Complex.I := by
    simp [a, mul_assoc, mul_comm Complex.I]
  rw [h, Complex.exp_ofReal_mul_I_re]

lemma lem_eacosalog2 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (-y * Real.log (n : ℝ)) := by
  rw [lem_niyelog n hn y]
  exact lem_eacosalog n hn y

lemma lem_eacosalog3 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (y * Real.log (n : ℝ)) := by
  rw [lem_eacosalog2 n hn y]
  exact lem_coseveny n hn y

lemma lem_cos2cos341 (θ : ℝ) : 2 * (1 + Real.cos θ) ^ 2 = 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  ring

lemma lem_postrig (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [← lem_cos2cos341]
  positivity

lemma lem_postriglogn (n : ℕ) (_hn : n ≥ 1) (t : ℝ) : 0 ≤ 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) := by
  rw [mul_assoc]
  exact lem_postrig (t * Real.log (n : ℝ))

def ballDR (R : ℝ) : Set ℂ := Metric.ball (0 : ℂ) R

-- First, the easy auxiliary lemmas:

lemma lem_HardMMP (R B : ℝ) (hR : R > 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball h_analytic.differentiableOn.diffContOnCl
  rw [frontier_ball _ (by linarith)]
  simp_all


def I := Complex.I

lemma cauchy_formula_deriv {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hfdiff: DifferentiableOn ℂ f (Metric.ball 0 R_analytic))
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r_int), (w - z)⁻¹ ^ 2 • f w := by
  rw [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable Metric.isOpen_ball
    (Metric.closedBall_subset_ball h_r_int_lt_R_analytic) hfdiff
    (Metric.closedBall_subset_ball h_r_z_lt_r_int hz)]
  simp [I]

lemma lem_f_prime_bound {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R_analytic))
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
  rw [cauchy_formula_deriv (analytic.differentiableOn.mono Metric.ball_subset_closedBall) h_r_z_lt_r_int h_r_int_lt_R_analytic hz, one_div, I]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r_int / ((R_analytic - r_int) * (r_int - r_z) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory_closedBall (by grind) analytic hf0 hM_pos hRe_f_le_M h_r_int_lt_R_analytic
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r_int - r_z) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr
    · exact pow_pos (by linarith) _
    · linarith
    · simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
      dist_zero_right] at hz' hz
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)

theorem borel_caratheodory_II {f : ℂ → ℂ} {R M r : ℝ}
    (hR_pos : 0 < R)
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
norm (deriv f z) ≤ (16 * M * R ^ 2) / ((R - r) ^ 3) := by
  grw [lem_f_prime_bound (r_int := (r + R) / 2) hM_pos hR_pos hr_pos (by linarith)
    (by linarith) analytic hf0 hRe_f_le_M hz]
  calc
  _ = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by field
  _ ≤ _ := by
    gcongr 1
    · exact pow_nonneg (by linarith) _
    · grw [(by linarith : R + r ≤ 2 * R)]
      field_simp
      norm_num

#print axioms borel_caratheodory_II

open Complex MeasureTheory intervalIntegral
open scoped Interval

open Filter Topology


open Classical

open scoped Topology

theorem log_of_analytic_open
    {r : ℝ} {B : ℂ → ℂ} (rpos : 0 < r)
    (hB : AnalyticOnNhd ℂ B (Metric.ball (0 : ℂ) r))
    (hB_ne_zero : ∀ z ∈ Metric.ball (0 : ℂ) r, B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.ball (0 : ℂ) r) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  obtain ⟨J, hJ⟩ := hB.deriv.div hB hB_ne_zero|>.differentiableOn.isExactOn_ball
  refine ⟨fun z ↦ J z - J 0, ?_, (by simp), ?_, ?_⟩
  · apply AnalyticOnNhd.sub _ analyticOnNhd_const
    exact DifferentiableOn.analyticOnNhd (fun z hz ↦ DifferentiableAt.differentiableWithinAt (hJ z hz).differentiableAt) (Metric.isOpen_ball)
  · intro z hz
    rw [deriv_sub_const, (hJ z hz).deriv]
  · intro z hz
    suffices B z = B 0 * Complex.exp (J z - J 0) by
      rw [this, norm_mul, Real.log_mul, Complex.norm_exp, Real.log_exp]
      · simp
      · exact norm_ne_zero_iff.mpr (hB_ne_zero 0 (by simpa))
      · exact norm_ne_zero_iff.mpr <| Complex.exp_ne_zero _
    let f := (fun z ↦ (J z).exp / B z)
    suffices f z = f 0 by
      unfold f at this
      rw [Complex.exp_sub]
      field_simp [hB_ne_zero z hz, hB_ne_zero 0 (by simpa)] at this ⊢
      rw [← this]
    refine IsOpen.is_const_of_deriv_eq_zero (s := Metric.ball 0 r) Metric.isOpen_ball Metric.isPreconnected_ball ?_ ?_ hz (by simpa)
    · unfold f
      refine fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_
      have :=hJ z hz|>.differentiableAt
      have := hB.differentiableOn z hz|>.differentiableAt (IsOpen.mem_nhds Metric.isOpen_ball hz)
      have := hB_ne_zero z hz
      fun_prop (disch := assumption)
    · intro z hz
      have : HasDerivAt (fun z ↦ cexp (J z)) ((J z).exp * deriv J z) z := by
        refine (Complex.hasDerivAt_exp (J z)).comp z (hJ z hz|>.differentiableAt|>.hasDerivAt)
      unfold f
      rw [deriv_fun_div this.differentiableAt
        ((hB.differentiableOn z hz).differentiableAt (IsOpen.mem_nhds Metric.isOpen_ball hz)) (hB_ne_zero z hz), this.deriv, (hJ z hz).deriv]
      simp only [Pi.zero_apply]
      field [hB_ne_zero z hz]

theorem log_of_analytic
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.closedBall (0 : ℂ) r1) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := log_of_analytic_open (by linarith)
    (hB.mono (subset_trans (Metric.ball_subset_ball hR'_lt_R.le) Metric.ball_subset_closedBall))
    (fun z hz ↦ hB_ne_zero z (Metric.ball_subset_closedBall hz))
  refine ⟨J, hJ1.mono (Metric.closedBall_subset_ball hr1_lt_R'), hJ2, fun z hz ↦ hJ3 z ?_,
    fun z hz ↦ hJ4 z ?_⟩
  all_goals exact Metric.closedBall_subset_ball hr1_lt_R' hz
