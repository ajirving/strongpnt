import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Module.ModuleTopology
import StrongPNT.bc_new

open Complex Metric

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
  rw [lem_eacosalog2 n hn y, neg_mul, Real.cos_neg]

lemma lem_postrig (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul, (by ring : 3 + 4 * Real.cos θ + (2 * Real.cos θ ^ 2 - 1) = 2 * (1 + Real.cos θ) ^ 2)]
  positivity

lemma lem_postriglogn (n : ℕ) (_hn : n ≥ 1) (t : ℝ) : 0 ≤ 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) := by
  rw [mul_assoc]
  exact lem_postrig (t * Real.log (n : ℝ))


theorem borelCaratheodory_centre {f : ℂ → ℂ} {M R : ℝ} {z c : ℂ} (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball c R))
    (hf₁ : Set.MapsTo f (ball c R) {z | z.re ≤ M}) (hR : 0 < R) (hz : z ∈ ball c R)
    (hf₂ : f c = 0) : ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  convert Complex.borelCaratheodory_zero (f := (fun z ↦ f (z + c))) (z := z - c) hM (fun z hz ↦ ?_)
    (fun z hz ↦ (hf₁ (by simp_all)))   hR (by simp_all [dist_eq_norm_sub]) (by simp_all)
  · simp
  · rw [differentiableWithinAt_comp_add_right]
    convert! hf (z + c) (by simp_all)
    simp

theorem borel_caratheodory_II {f : ℂ → ℂ} {R M r : ℝ} {c : ℂ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hf0 : f c = 0)
    (hRe_f_le_M : Set.MapsTo f (ball c R) {z | z.re ≤ M})
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv f z‖ ≤ (8 * M * R) / ((R - r) ^ 2) := by
  -- apply the sharp Borel-Carathéodory bound on the intermediate disc of radius `(R + r) / 2`
  have hsub : closedBall c ((R + r) / 2) ⊆ ball c R := closedBall_subset_ball (by linarith)
  refine (norm_deriv_le_of_re_le (by linarith) (hf.diffContOnCl_ball hsub)
    (fun w hw ↦ hRe_f_le_M (hsub (sphere_subset_closedBall hw))) (by linarith)
    (mem_closedBall_iff_norm.mp hz)).trans ?_
  rw [hf0]
  simp only [Complex.zero_re, sub_zero]
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg hM_pos.le (sq_nonneg (R - r))]

#print axioms borel_caratheodory_II

open Complex MeasureTheory intervalIntegral
open scoped Interval

open Filter Topology

open scoped Topology

theorem log_of_analytic_open
    {r : ℝ} {B : ℂ → ℂ} {c : ℂ} (rpos : 0 < r)
    (hB : AnalyticOnNhd ℂ B (Metric.ball c r))
    (hB_ne_zero : ∀ z ∈ Metric.ball c r, B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.ball c r) ∧
      J_B c = 0 ∧
      (∀ z ∈ Metric.ball c r, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.ball c r,
        Real.log ‖B z‖ - Real.log ‖B c‖ = Complex.re (J_B z)) := by
  obtain ⟨J, hJ⟩ := hB.deriv.div hB hB_ne_zero|>.differentiableOn.isExactOn_ball
  refine ⟨fun z ↦ J z - J c, ?_, (by simp), ?_, ?_⟩
  · apply AnalyticOnNhd.sub _ analyticOnNhd_const
    exact DifferentiableOn.analyticOnNhd (fun z hz ↦ DifferentiableAt.differentiableWithinAt (hJ z hz).differentiableAt) (Metric.isOpen_ball)
  · intro z hz
    rw [deriv_sub_const, (hJ z hz).deriv]
  · intro z hz
    suffices B z = B c * Complex.exp (J z - J c) by
      rw [this, norm_mul, Real.log_mul, Complex.norm_exp, Real.log_exp]
      · simp
      · exact norm_ne_zero_iff.mpr (hB_ne_zero c (by simpa))
      · exact norm_ne_zero_iff.mpr <| Complex.exp_ne_zero _
    let f := (fun z ↦ (J z).exp / B z)
    suffices f z = f c by
      unfold f at this
      rw [Complex.exp_sub]
      field_simp [hB_ne_zero z hz, hB_ne_zero c (by simpa)] at this ⊢
      rw [← this]
    refine IsOpen.is_const_of_deriv_eq_zero (s := Metric.ball c r) Metric.isOpen_ball Metric.isPreconnected_ball ?_ ?_ hz (by simpa)
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
