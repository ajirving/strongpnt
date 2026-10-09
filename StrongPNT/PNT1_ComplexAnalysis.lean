import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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


theorem borel_caratheodory_II {f : ℂ → ℂ} {R M r : ℝ} {c : ℂ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hf0 : f c = 0)
    (hRe_f_le_M : Set.MapsTo f (ball c R) {z | z.re ≤ M})
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv f z‖ ≤ (2 * M * R) / ((R - r) ^ 2) := by
  simp only [mem_closedBall, dist_eq_norm_sub] at hz
  have R_pos : 0 < R := by linarith
  grw [norm_deriv_le_of_re_le R_pos hf hf0 (fun w hw ↦ hRe_f_le_M hw)
    (by simp_all [dist_eq_norm_sub]; linarith), hz]
  · rw [(by ring : 2 * R * M = 2 * M * R)]
  · linarith
  · positivity
#print axioms borel_caratheodory_II

open Complex MeasureTheory intervalIntegral
open scoped Interval

open Filter Topology

open scoped Topology

/-! ### Holomorphic logarithms

The following lemmas are intended for upstreaming to Mathlib. -/

theorem Convex.isSimplyConnected {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s : Set E} (hs : Convex ℝ s)
    (hne : s.Nonempty) : IsSimplyConnected s := by
  have := hs.contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible s

theorem AnalyticAt.of_exp_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {x : E} (hg : AnalyticAt ℂ (exp ∘ f) x)
    (hf : ContinuousAt f x) : AnalyticAt ℂ f x := by
  have : AnalyticAt ℂ cexp (f x) := analyticAt_cexp
  have hd : deriv cexp (f x) ≠ 0 := by simp
  refine ((this.analyticAt_localInverse hd).comp_of_eq hg rfl).congr ?_
  exact hf.eventually (this.hasStrictDerivAt.eventually_left_inverse hd)

/-- A nonvanishing analytic function on an open simply connected set has an analytic
logarithm. -/
theorem AnalyticOnNhd.exists_eqOn_exp_comp {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hg0 : 0 ∉ g '' U) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ Set.EqOn (exp ∘ f) g U := by
  obtain ⟨f, hfc, hf⟩ := exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn hg0
  refine ⟨f, fun z hz ↦ AnalyticAt.of_exp_comp ?_ (hfc.continuousAt (hUo.mem_nhds hz)), hf⟩
  refine (hg z hz).congr ?_
  filter_upwards [hUo.mem_nhds hz] with y hy using (hf hy).symm

theorem deriv_eq_logDeriv_of_exp_comp {f g : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℂ f x)
    (hfg : ∀ᶠ y in 𝓝 x, exp (f y) = g y) : deriv f x = deriv g x / g x := by
  have h := ((hasDerivAt_exp (f x)).comp x hf.hasDerivAt).congr_of_eventuallyEq
    (hfg.mono fun _ h ↦ h.symm)
  rw [h.deriv, ← hfg.self_of_nhds]
  field

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
  obtain ⟨f, hfa, hf⟩ := hB.exists_eqOn_exp_comp
    ((convex_ball c r).isSimplyConnected ⟨c, mem_ball_self rpos⟩) isOpen_ball (by simpa)
  refine ⟨fun z ↦ f z - f c, hfa.sub analyticOnNhd_const, by simp, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [deriv_sub_const]
    exact deriv_eq_logDeriv_of_exp_comp (hfa z hz).differentiableAt <| by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy using hf hy
  · rw [sub_re, ← hf hz, ← hf (mem_ball_self rpos)]
    simp [norm_exp]
