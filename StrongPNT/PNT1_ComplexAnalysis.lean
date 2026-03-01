import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Module.ModuleTopology
import PrimeNumberTheoremAnd.BorelCaratheodory

lemma lem_exprule (n : ℕ) (hn : n ≥ 1) (α β : ℂ) : (n : ℂ) ^ (α + β) = (n : ℂ) ^ α * (n : ℂ) ^ β := by
  apply Complex.cpow_add
  -- Need to prove (n : ℂ) ≠ 0
  rw [Nat.cast_ne_zero]
  -- Need to prove n ≠ 0
  rw [← Nat.one_le_iff_ne_zero]
  exact hn

lemma lem_realbw (b : ℝ) (w : ℂ) : (b * w).re = b * w.re := by
  exact Complex.re_ofReal_mul b w

lemma lem_Euler (a : ℝ) : Complex.exp (a * Complex.I) = Real.cos a + Real.sin a * Complex.I := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma lem_Reecos (a : ℝ) : (Complex.exp (a * Complex.I)).re = Real.cos a := by
  rw [lem_Euler]
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex.re_ofReal_mul]
  rw [Complex.I_re]
  simp

lemma lem_coseven (a : ℝ) : Real.cos (-a) = Real.cos a := by
  exact Real.cos_neg a

lemma lem_coseveny (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : Real.cos (-y * Real.log (n : ℝ)) = Real.cos (y * Real.log (n : ℝ)) := by
  rw [neg_mul]
  exact lem_coseven (y * Real.log (n : ℝ))

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
  rw [h]
  -- Apply lem_Reecos
  exact lem_Reecos a

lemma lem_eacosalog2 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (-y * Real.log (n : ℝ)) := by
  rw [lem_niyelog n hn y]
  exact lem_eacosalog n hn y

lemma lem_eacosalog3 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (y * Real.log (n : ℝ)) := by
  rw [lem_eacosalog2 n hn y]
  exact lem_coseveny n hn y

lemma lem_cos2t (θ : ℝ) : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
  exact Real.cos_two_mul θ

lemma lem_cos2t2 (θ : ℝ) : 2 * Real.cos θ ^ 2 = 1 + Real.cos (2 * θ) := by
  rw [lem_cos2t]
  ring

lemma lem_cosSquare (θ : ℝ) : 2 * (1 + Real.cos θ)^2 = 2 + 4 * Real.cos θ + 2 * Real.cos θ^2 := by
  ring

lemma lem_cos2cos341 (θ : ℝ) : 2 * (1 + Real.cos θ) ^ 2 = 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [lem_cosSquare]
  rw [lem_cos2t2]
  ring

lemma lem_SquarePos (y : ℝ) : 0 ≤ y ^ 2 := by
  exact sq_nonneg y

lemma lem_SquarePos2 (y : ℝ) : 0 ≤ 2 * y ^ 2 := by
  apply mul_nonneg
  · norm_num
  · exact lem_SquarePos y

lemma lem_SquarePoscos (θ : ℝ) : 0 ≤ 2 * (1 + Real.cos θ) ^ 2 := by
  exact lem_SquarePos2 (1 + Real.cos θ)

lemma lem_postrig (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [← lem_cos2cos341]
  exact lem_SquarePoscos θ

lemma lem_postriglogn (n : ℕ) (_hn : n ≥ 1) (t : ℝ) : 0 ≤ 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) := by
  rw [mul_assoc]
  exact lem_postrig (t * Real.log (n : ℝ))

lemma lem_abspos (z : ℂ) : z ≠ 0 → norm z > 0 := by
  intro h_ne_zero
  apply Real.sqrt_pos.mpr
  exact Complex.normSq_pos.mpr h_ne_zero

lemma lem_wReIm (w : ℂ) : w = w.re + Complex.I * w.im := by
  apply Complex.ext
  simp
  simp

def ballDR (R : ℝ) : Set ℂ := Metric.ball (0 : ℂ) R

-- First, the easy auxiliary lemmas:

lemma lem_ballDR (R : ℝ) (hR : R > 0) : closure (ballDR R) = Metric.closedBall (0 : ℂ) R := by
  unfold ballDR
  exact closure_ball 0 (ne_of_gt hR)

lemma lem_inDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∈ closure (ballDR R)) : norm w ≤ R := by
  rw [lem_ballDR R hR] at hw
  rw [Metric.mem_closedBall] at hw
  rw [Complex.dist_eq] at hw
  simp at hw
  exact hw

lemma lem_notinDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∉ ballDR R) : norm w ≥ R := by
  -- Apply definition of ballDR
  unfold ballDR at hw
  -- Use characterization of metric ball membership
  rw [Metric.mem_ball] at hw
  -- hw : ¬(dist w 0 < R), which is equivalent to dist w 0 ≥ R
  push_neg at hw
  -- Use Complex.dist_eq to relate distance to complex absolute value
  rw [Complex.dist_eq] at hw
  -- Simplify w - 0 = w
  simp at hw
  exact hw

lemma lem_legeR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : norm w ≤ R) (hw2 : norm w ≥ R) : norm w = R := by
  linarith

lemma lem_circleDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : w ∈ closure (ballDR R)) (hw2 : w ∉ ballDR R) : norm w = R := by
  have h1 : norm w ≤ R := lem_inDR R hR w hw1
  have h2 : norm w ≥ R := lem_notinDR R hR w hw2
  exact lem_legeR R hR w h1 h2

lemma lem_Rself (R : ℝ) (hR : R > 0) : |R| = R := by
  rw [abs_eq_self]
  linarith

lemma lem_Rself2 (R : ℝ) (hR : R > 0) : |R| ≤ R := by
  rw [lem_Rself R hR]

lemma lem_Rself3 (R : ℝ) (hR : R > 0) : (R : ℂ) ∈ closure (ballDR R) := by
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  simp [Complex.dist_eq]
  exact lem_Rself2 R hR

lemma lem_DRcompact (R : ℝ) (hR : R > 0) : IsCompact (closure (ballDR R)) := by
  rw [lem_ballDR R hR]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Metric.isClosed_closedBall
  · exact Metric.isBounded_closedBall

lemma lem_ExtrValThm {K : Set ℂ} (hK : IsCompact K) (hK_nonempty : K.Nonempty) (g : K → ℂ) (hg : Continuous g) :
∃ v : K, ∀ z : K, norm (g z) ≤ norm (g v) := by
  -- The subtype K inherits compactness
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- K is nonempty as a type
  haveI : Nonempty K := hK_nonempty.to_subtype
  -- Consider the function that maps each point to norm (g z)
  let f : K → ℝ := fun z => norm (g z)
  -- This function is continuous
  have hf_cont : Continuous f := continuous_norm.comp hg
  -- Apply the extreme value theorem for compact spaces
  obtain ⟨v, hv_mem, hv_max⟩ := IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty hf_cont.continuousOn
  use v
  intro z
  exact hv_max (Set.mem_univ z)

lemma lem_ExtrValThmDR (R : ℝ) (hR : R > 0) (g : closure (ballDR R) → ℂ) (hg : Continuous g) :
∃ v : closure (ballDR R), ∀ z : closure (ballDR R), norm (g z) ≤ norm (g v) := by
  -- Apply lem_ExtrValThm with K = closure (ballDR R)
  have hK_compact : IsCompact (closure (ballDR R)) := lem_DRcompact R hR
  -- Show that closure (ballDR R) is nonempty
  have hK_nonempty : (closure (ballDR R)).Nonempty := by
    rw [lem_ballDR R hR]
    rw [Metric.nonempty_closedBall]
    linarith
  -- Apply the extreme value theorem
  exact lem_ExtrValThm hK_compact hK_nonempty g hg

lemma lem_AnalCont {R : ℝ} (hR : R > 0) (H : ℂ → ℂ) (h_analytic : AnalyticOn ℂ H (closure (ballDR R))) :
Continuous (H ∘ (Subtype.val : closure (ballDR R) → ℂ)) := by
  -- H is continuous on closure (ballDR R) since it's analytic there
  have h_cont_on : ContinuousOn H (closure (ballDR R)) := AnalyticOn.continuousOn h_analytic
  -- Subtype.val is continuous
  have h_val_cont : Continuous (Subtype.val : closure (ballDR R) → ℂ) := continuous_subtype_val
  -- The composition is continuous since we're composing a continuous function with a continuous function
  -- and the range of Subtype.val is contained in the domain where H is continuous
  exact ContinuousOn.comp_continuous h_cont_on h_val_cont (fun _ => Subtype.mem _)

lemma lem_ExtrValThmh {R : ℝ} (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ u : closure (ballDR R), ∀ z : closure (ballDR R), norm (h u) ≥ norm (h z) := by
  -- Apply lem_ExtrValThmDR with g = h ∘ Subtype.val
  have hg_continuous : Continuous (h ∘ Subtype.val : closure (ballDR R) → ℂ) :=
    lem_AnalCont hR h h_analytic
  -- Get the point v where |h(v)| is maximized
  obtain ⟨v, hv⟩ := lem_ExtrValThmDR R hR (h ∘ Subtype.val) hg_continuous
  -- Use v as our u
  use v
  -- Show that |h(u)| ≥ |h(z)| for all z
  intro z
  have : norm ((h ∘ Subtype.val) z) ≤ norm ((h ∘ Subtype.val) v) := hv z
  -- Simplify the composition
  simp [Function.comp] at this
  exact this

lemma lem_MaxModP (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) := by
  -- The ball is preconnected (since metric balls are convex)
  have h_preconnected : IsPreconnected (ballDR R) := by
    unfold ballDR
    apply Convex.isPreconnected
    exact convex_ball (0 : ℂ) R

  -- The ball is open
  have h_open : IsOpen (ballDR R) := by
    unfold ballDR
    exact Metric.isOpen_ball

  -- h is differentiable on ballDR R and continuous on its closure
  have h_diff_cont : DiffContOnCl ℂ h (ballDR R) := by
    constructor
    · -- h is differentiable on ballDR R
      apply AnalyticOn.differentiableOn
      exact h_analytic.mono subset_closure
    · -- h is continuous on closure (ballDR R)
      exact AnalyticOn.continuousOn h_analytic

  -- Establish the maximum condition in terms of norm
  have h_max_on : IsMaxOn (norm ∘ h) (ballDR R) w := by
    intro z hz
    simp only [Function.comp_apply]
    -- Since norm is deprecated in favor of norm, they should be definitionally equal
    convert hw_max z hz

  -- Apply the main maximum modulus theorem
  have h_eq := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn h_preconnected h_open h_diff_cont hw_in_DR h_max_on

  -- Convert back to norm for the conclusion
  intro z hz
  have norm_eq := h_eq hz
  simp only [Function.comp_apply, Function.const_apply] at norm_eq
  -- Since norm is deprecated in favor of norm, they should be definitionally equal
  convert norm_eq

lemma lem_MaxModR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : norm (h R) = norm (h w) := by
  -- Apply lem_MaxModP to get constant absolute value on closure
  have h_const : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) :=
    lem_MaxModP R hR h h_analytic w hw_in_DR hw_max
  -- Show that R (as complex number) is in the closure
  have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
  -- Apply the constant property at z = R
  exact h_const (R : ℂ) hR_in_closure

lemma lem_MaxModRR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) :
∀ z ∈ closure (ballDR R), norm (h R) ≥ norm (h z) := by
  intro z hz
  -- Apply lem_MaxModP to get |h(z)| = |h(w)| for all z ∈ closure (ballDR R)
  have h1 := lem_MaxModP R hR h h_analytic w hw_in_DR hw_max z hz
  -- Apply lem_MaxModR to get |h(R)| = |h(w)|
  have h2 := lem_MaxModR R hR h h_analytic w hw_in_DR hw_max
  -- From h1: |h(z)| = |h(w)| and h2: |h(R)| = |h(w)|, we get |h(R)| = |h(z)|
  rw [h2, h1]

theorem lem_MaxModv2 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : closure (ballDR R), norm (v : ℂ) = R ∧ ∀ z : closure (ballDR R), norm (h (v : ℂ)) ≥ norm (h (z : ℂ)) := by
  -- Apply lem_ExtrValThmh to get u with maximal |h(u)|
  obtain ⟨u, hu⟩ := lem_ExtrValThmh hR h h_analytic

  -- Case split on whether u ∈ ballDR R
  if h_case : (u : ℂ) ∈ ballDR R then
    -- If u ∈ ballDR R, set v = R
    have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
    let v : closure (ballDR R) := ⟨R, hR_in_closure⟩
    use v
    constructor
    · -- Show |v| = R
      -- Since v coerces to R as a complex number, and norm (R : ℂ) = |R| = R
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
      -- Use the fact that norm of a real number equals the real absolute value
      have : norm (R : ℂ) = abs R := by
        simp [Complex.norm_real]
      rw [this, lem_Rself R hR]
    · -- Show |h(v)| ≥ |h(z)| for all z using lem_MaxModRR
      intro z
      -- We need to show that u satisfies the hypothesis of lem_MaxModRR
      have hw_max : ∀ w ∈ ballDR R, norm (h w) ≤ norm (h (u : ℂ)) := by
        intro w hw
        -- w ∈ ballDR R implies w ∈ closure (ballDR R)
        have hw_closure : w ∈ closure (ballDR R) := subset_closure hw
        -- Create subtype element and apply hu
        let w_sub : closure (ballDR R) := ⟨w, hw_closure⟩
        exact hu w_sub
      -- Apply lem_MaxModRR to get the result
      have h_result := lem_MaxModRR R hR h h_analytic (u : ℂ) h_case hw_max
      -- Since v coerces to R, we have h(v) = h(R)
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
      -- Apply h_result with the membership condition for z
      exact h_result (z : ℂ) (Subtype.mem z)
  else
    -- If u ∉ ballDR R, set v = u
    use u
    constructor
    · -- Show |u| = R using lem_circleDR
      exact lem_circleDR R hR (u : ℂ) (Subtype.mem u) h_case
    · -- Show |h(u)| ≥ |h(z)| for all z, which follows directly from hu
      exact hu

theorem lem_MaxModv3 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : ℂ, norm v = R ∧ ∀ z : ℂ, z ∈ closure (ballDR R) → norm (h v) ≥ norm (h z) := by
  -- Apply lem_MaxModv2 to get a point in closure with |v| = R and maximum property
  obtain ⟨v_sub, hv_abs, hv_max⟩ := lem_MaxModv2 R hR h h_analytic
  -- Extract the underlying complex number from the subtype
  let v := (v_sub : ℂ)
  use v
  constructor
  · -- Show |v| = R
    exact hv_abs
  · -- Show maximality property
    intro z hz
    -- Apply hv_max to the subtype version of z
    have hz_sub : z ∈ closure (ballDR R) := hz
    let z_sub : closure (ballDR R) := ⟨z, hz_sub⟩
    have := hv_max z_sub
    -- Simplify the coercions
    simp [v] at this
    exact this

lemma lem_MaxModv4 (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∃ v : ℂ, norm v = R ∧ (∀ w : ℂ, w ∈ closure (ballDR R) → norm (h v) ≥ norm (h w)) ∧ norm (h v) ≤ B := by
  -- Apply lem_MaxModv3 to get a point v with |v| = R where |h(v)| is maximal
  obtain ⟨v, hv_abs, hv_max⟩ := lem_MaxModv3 R hR h h_analytic
  -- Use v as our witness
  use v
  constructor
  · -- |v| = R
    exact hv_abs
  constructor
  · -- |h(v)| ≥ |h(w)| for all w ∈ closure (ballDR R)
    exact hv_max
  · -- |h(v)| ≤ B using the boundary bound assumption
    apply h_boundary_bound
    exact hv_abs

lemma lem_HardMMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B := by
  intro w hw
  -- Apply lem_MaxModv4 to get a point v with |v| = R where |h(v)| is maximal and |h(v)| ≤ B
  obtain ⟨v, hv_abs, hv_max, hv_bound⟩ := lem_MaxModv4 R B hR hB h h_analytic h_boundary_bound
  -- We have |h(w)| ≤ |h(v)| ≤ B
  have h1 : norm (h w) ≤ norm (h v) := hv_max w hw
  have h2 : norm (h v) ≤ B := hv_bound
  -- Combine the inequalities
  linarith [h1, h2]

lemma lem_BCI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_in_ball : norm z ≤ r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
  rw [lem_ballDR R hR] at *
  convert borelCaratheodory_closedBall hR h_analytic h_zero hM h_re_bound hr_lt_R (mem_closedBall_zero_iff.mpr hz_in_ball) using 1
  ring

theorem thm_BorelCaratheodoryI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R) :
sSup ((norm ∘ f) '' (closure (ballDR r))) ≤ (2 * r / (R - r)) * M := by
  -- Apply Real.sSup_le - we need to show every element is bounded and the bound is nonnegative
  apply Real.sSup_le
  · -- Show that every element x ∈ (norm ∘ f) '' (closure (ballDR r)) satisfies x ≤ (2 * r / (R - r)) * M
    intro x hx
    -- hx : x ∈ (norm ∘ f) '' (closure (ballDR r))
    -- This means ∃ z ∈ closure (ballDR r), x = norm (f z)
    obtain ⟨z, hz_in_closure, hx_eq⟩ := hx
    rw [← hx_eq]
    -- Now we need to show norm (f z) ≤ (2 * r / (R - r)) * M
    -- First, convert closure membership to |z| ≤ r
    have hz_bound : norm z ≤ r := by
      rw [lem_ballDR r hr_pos] at hz_in_closure
      rw [Metric.mem_closedBall] at hz_in_closure
      rw [Complex.dist_eq] at hz_in_closure
      simp at hz_in_closure
      exact hz_in_closure
    -- Apply lem_BCI
    exact lem_BCI R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_bound
  · -- Show that (2 * r / (R - r)) * M ≥ 0
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · linarith [hr_pos]
      · linarith [hr_lt_R]
    · linarith [hM]


def I := Complex.I

lemma cauchy_formula_deriv {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r_int), (w - z)⁻¹ ^ 2 • f w := by
  -- Extract the witness from hf_domain
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain

  -- Show z is in the ball of radius r_int
  have hz_in_ball : z ∈ Metric.ball (0 : ℂ) r_int := by
    apply Metric.mem_ball.mpr
    have h1 : ‖z - 0‖ ≤ r_z := Metric.mem_closedBall.mp hz
    simp only [sub_zero] at h1
    have h2 : ‖z‖ < r_int := lt_of_le_of_lt h1 h_r_z_lt_r_int
    rwa [dist_eq_norm, sub_zero]

  -- Use U = ball 0 R_analytic as our open set
  set U := Metric.ball (0 : ℂ) R_analytic

  -- Show closedBall 0 r_int ⊆ U
  have hc_subset : Metric.closedBall (0 : ℂ) r_int ⊆ U := by
    apply Metric.closedBall_subset_ball
    exact h_r_int_lt_R_analytic

  -- Show f is differentiable on U
  have hf_on_U : DifferentiableOn ℂ f U := by
    -- Since Metric.ball 0 R_analytic ⊆ Metric.closedBall 0 R_analytic ⊆ U'
    -- and f is differentiable on U', it's also differentiable on the smaller set U
    apply DifferentiableOn.mono hf_diff_U'
    calc U = Metric.ball 0 R_analytic := rfl
         _ ⊆ Metric.closedBall 0 R_analytic := Metric.ball_subset_closedBall
         _ ⊆ U' := h_subset

  -- Apply the Cauchy integral formula for derivatives
  have cauchy_eq := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
    Metric.isOpen_ball hc_subset hf_on_U hz_in_ball

  -- Convert to our desired form
  rw [← cauchy_eq]

  -- The coefficients are equal and the integrands are equal
  congr 2
  · -- (2 * π * I)⁻¹ = 1 / (2 * Real.pi * I)
    simp only [one_div]
    -- Complex.I = I by definition
    rfl
  · -- ((w - z) ^ 2)⁻¹ • f w = (w - z)⁻¹ ^ 2 • f w
    ext w
    rw [← inv_pow]

lemma circleMap_zero_eq_exp (r : ℝ) (t : ℝ) : circleMap 0 r t = r * Complex.exp (I * t) := by
  -- By definition, circleMap 0 r t = 0 + r * Complex.exp (t * Complex.I)
  rw [circleMap]
  -- Simplify 0 + r * Complex.exp (t * Complex.I) to r * Complex.exp (t * Complex.I)
  simp only [zero_add]
  -- Show that t * Complex.I = I * t using commutativity and I = Complex.I
  congr 2
  rw [mul_comm (t : ℂ) Complex.I]
  -- Since I = Complex.I by definition
  rfl

lemma deriv_ofReal_eq_one (t : ℝ) : deriv Complex.ofReal t = 1 := by
  -- Complex.ofReal is a continuous linear map, so use the general theorem
  -- The derivative of a continuous linear map e at any point x is e(1)
  have h : deriv Complex.ofReal t = Complex.ofReal 1 := by
    -- Apply the theorem for continuous linear maps
    -- Complex.ofReal can be viewed as ⇑Complex.ofRealCLM
    rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
    exact ContinuousLinearMap.deriv Complex.ofRealCLM
  -- Now simplify: Complex.ofReal 1 = 1
  rw [h]
  simp only [Complex.ofReal_one]

lemma differentiableAt_ofReal (t : ℝ) : DifferentiableAt ℝ Complex.ofReal t := by
  -- Complex.ofReal is definitionally equal to the coercion of Complex.ofRealCLM
  rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
  -- Apply the theorem that continuous linear maps are differentiable at every point
  apply ContinuousLinearMap.differentiableAt

lemma lem_dw_dt_real {r_int : ℝ} (t : ℝ) :
deriv (fun (t' : ℝ) => r_int * Complex.exp (I * t')) t = I * r_int * Complex.exp (I * t) := by
  -- Apply constant multiplication rule
  rw [deriv_const_mul]
  -- Apply chain rule for complex exponential
  rw [deriv_cexp]
  -- Apply constant multiplication rule for I * t'
  rw [deriv_const_mul]
  -- Use the existing lemma for derivative of Complex.ofReal
  rw [deriv_ofReal_eq_one]
  -- Simplify: r_int * (Complex.exp (I * t) * (I * 1)) = I * r_int * Complex.exp (I * t)
  ring
  -- Prove differentiability conditions (in reverse order as they appear)
  · exact differentiableAt_ofReal t
  · exact (differentiableAt_const I).mul (differentiableAt_ofReal t)
  · exact DifferentiableAt.cexp ((differentiableAt_const I).mul (differentiableAt_ofReal t))

lemma deriv_circleMap_zero (r : ℝ) (t : ℝ) : deriv (circleMap 0 r) t = I * r * Complex.exp (I * t) := by
  -- Show that circleMap 0 r equals the exponential function
  have h : circleMap 0 r = fun (t' : ℝ) => r * Complex.exp (I * t') := by
    ext t'
    exact circleMap_zero_eq_exp r t'

  -- Rewrite the derivative using this equality
  rw [h]

  -- Apply lem_dw_dt_real with r_int = r
  exact lem_dw_dt_real t

lemma lem_CIF_deriv_param {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi * I)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(I * r_int * Complex.exp (I * t) * ((r_int * Complex.exp (I * t)) - z)⁻¹ ^ 2) * f (r_int * Complex.exp (I * t))) := by
  -- Apply cauchy_formula_deriv to get the circle integral form
  rw [cauchy_formula_deriv hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  -- Convert circle integral to parametric integral using circleIntegral_def_Icc
  rw [circleIntegral_def_Icc]

  -- Convert scalar multiplication to regular multiplication
  rw [smul_eq_mul]

  -- Substitute circleMap and its derivative
  simp only [circleMap_zero_eq_exp, deriv_circleMap_zero]

  -- Now we need to match the form: the integrand should be
  -- (I * r_int * Complex.exp (I * t)) • ((r_int * Complex.exp (I * t) - z)⁻¹ ^ 2 • f (r_int * Complex.exp (I * t)))
  -- which equals our target form
  congr 2
  ext t
  simp only [smul_eq_mul]
  ring

lemma complex_coeff_I_cancel : (1 : ℂ) / (2 * Real.pi * I) * I = 1 / (2 * Real.pi) := by
  field_simp [Complex.I_ne_zero, Real.pi_pos.ne']
  exact div_self Complex.I_ne_zero

lemma factor_I_from_integrand (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) :
  ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  I * ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) := by
  -- Rewrite the left-hand side to separate I from the rest of the integrand
  -- The key insight is that I * (expression) = I • (expression) in ℂ
  have h : ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
           ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I • (↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t))) := by
    congr 1
    ext t
    rw [smul_eq_mul]
    ring
  rw [h]
  -- Apply linearity of integration to factor out the scalar I
  rw [MeasureTheory.integral_smul]
  -- Convert scalar multiplication back to regular multiplication
  rw [smul_eq_mul]

lemma integrand_transform_div (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) (t : ℝ) :
  ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  ↑r_int * Complex.exp (I * ↑t) * f (↑r_int * Complex.exp (I * ↑t)) / (↑r_int * Complex.exp (I * ↑t) - z) ^ 2 := by
  -- Use inv_pow to transform (w - z)⁻¹ ^ 2 to ((w - z) ^ 2)⁻¹
  rw [inv_pow]
  -- Use div_eq_mul_inv in reverse to transform multiplication by inverse to division
  rw [← div_eq_mul_inv]
  -- Now we need to rearrange the multiplication
  ring

lemma lem_CIF_deriv_simplified {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
  -- Apply lem_CIF_deriv_param
  rw [lem_CIF_deriv_param hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  -- Factor out I from the integrand using linearity
  rw [factor_I_from_integrand f r_int z]

  -- Rearrange to cancel I factors: (1 / (2 * Real.pi * I)) * I = 1 / (2 * Real.pi)
  rw [← mul_assoc, complex_coeff_I_cancel]

  -- Transform the integrand from multiplicative inverse to division form
  congr 2
  funext t
  rw [integrand_transform_div f r_int z t]

lemma lem_modulus_of_f_prime0 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) = norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
  -- Apply the simplified Cauchy integral formula for derivatives
  rw [lem_CIF_deriv_simplified hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

lemma one_div_two_pi_pos : (1 : ℝ) / (2 * Real.pi) > 0 := by
  -- Use the fact that π > 0
  have h_pi_pos : Real.pi > 0 := Real.pi_pos
  -- Show that 2 * π > 0
  have h_2pi_pos : 2 * Real.pi > 0 := by
    apply mul_pos
    · norm_num
    · exact h_pi_pos
  -- Show that 1 / (2 * π) > 0
  apply div_pos
  · norm_num
  · exact h_2pi_pos

lemma abs_integral_le_integral_abs {a b : ℝ} {g : ℝ → ℂ} (hab : a ≤ b) : norm (∫ (t : ℝ) in Set.Icc a b, g t) ≤ ∫ (t : ℝ) in Set.Icc a b, norm (g t) := by
  -- Apply the general triangle inequality for integrals from measure theory
  -- Since norm is the norm on ℂ, this follows directly
  exact MeasureTheory.norm_integral_le_integral_norm g

lemma complex_abs_mul (a b : ℂ) : norm (a * b) = norm a * norm b :=
  Complex.norm_mul a b

lemma complex_abs_ofReal_nonneg (r : ℝ) (hr : r ≥ 0) : norm (↑r : ℂ) = r := by
  -- Use abs_ofReal_mul_complex with z = 1
  have h1 : norm (↑r * 1) = r * norm (1 : ℂ) := by simp; assumption
  -- Simplify: ↑r * 1 = ↑r and norm 1 = 1
  simp only [mul_one] at h1
  have h2 : norm (1 : ℂ) = 1 := by simp
  rw [h2] at h1
  simp only [mul_one] at h1
  simp
  assumption

lemma abs_one_div_two_pi_complex : norm (1 / (2 * ↑Real.pi : ℂ)) = 1 / (2 * Real.pi) := by
  -- First rewrite the complex expression as a coercion of the real expression
  have h_eq : (1 / (2 * ↑Real.pi) : ℂ) = ↑(1 / (2 * Real.pi) : ℝ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]

  rw [h_eq]

  -- Now show that 1 / (2 * Real.pi) ≥ 0
  have h_nonneg : (1 / (2 * Real.pi) : ℝ) ≥ 0 := by
    apply div_nonneg
    · norm_num
    · apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos

  -- Apply the existing lemma
  exact complex_abs_ofReal_nonneg (1 / (2 * Real.pi)) h_nonneg

lemma lem_integral_modulus_inequality {r_int : ℝ} {z : ℂ} {f : ℂ → ℂ} :
norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), (r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
  -- Use the multiplicative property |a * b| = |a| * |b|
  rw [complex_abs_mul]

  -- Use the fact that |1 / (2 * π)| = 1 / (2 * π) since it's positive real
  rw [abs_one_div_two_pi_complex]

  -- Apply the triangle inequality |∫g| ≤ ∫|g| with correct hypothesis
  apply mul_le_mul_of_nonneg_left
  · -- Need to prove 0 ≤ 2 * Real.pi for abs_integral_le_integral_abs
    have h_2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by
      apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos
    exact abs_integral_le_integral_abs h_2pi_nonneg
  · exact le_of_lt one_div_two_pi_pos

lemma lem_modulus_of_f_prime {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
  -- Apply lem_modulus_of_f_prime0 to get the equality form
  rw [lem_modulus_of_f_prime0 hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
  -- Apply lem_integral_modulus_inequality to get the desired inequality
  exact lem_integral_modulus_inequality

lemma lem_modulus_of_integrand_product2 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
    norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) =
norm (f (r_int * Complex.exp (I * t))) * norm (r_int * Complex.exp (I * t)) := by
  -- Since norm is the norm, use the multiplicative property of norms
  rw [norm_mul]

lemma lem_modeit (t : ℝ) : norm (Complex.exp (I * t)) = Real.exp (Complex.re (I * t)) := by
  -- This is a direct application of the general theorem
  exact Complex.norm_exp (I * t)

lemma lem_Reit0 (t : ℝ) : Complex.re (I * t) = 0 := by
  -- Unfold the definition I = Complex.I
  unfold I
  -- Use the formula for real part of multiplication
  rw [Complex.mul_re]
  -- We have Complex.I.re * (↑t).re - Complex.I.im * (↑t).im
  -- Complex.I.re = 0, Complex.I.im = 1, (↑t).re = t, (↑t).im = 0
  rw [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  -- Now we have 0 * t - 1 * 0 = 0
  ring

lemma lem_e01 : Real.exp 0 = 1 := by
  exact Real.exp_zero

lemma lem_modulus_of_e_it_is_one (t : ℝ) : norm (Complex.exp (I * t)) = 1 := by
  -- Apply lem_modeit to rewrite norm (Complex.exp (I * t)) as Real.exp (Complex.re (I * t))
  rw [lem_modeit]
  -- Apply lem_Reit0 to show Complex.re (I * t) = 0
  rw [lem_Reit0]
  -- Apply lem_e01 to show Real.exp 0 = 1
  rw [lem_e01]

lemma lem_modulus_of_ae_it {a t : ℝ} (ha : 0 < a) : norm (a * Complex.exp (I * t)) = a := by
  -- avoid fragile `change` on coerced terms; rewrite directly
  rw [norm_mul, lem_modulus_of_e_it_is_one, mul_one, Complex.norm_real]
  exact abs_of_pos ha

lemma lem_modulus_of_integrand_product3 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) = r_int * norm (f (r_int * Complex.exp (I * t))) := by
  -- Use lem_modulus_of_integrand_product2 to split the absolute value
  rw [lem_modulus_of_integrand_product2 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]
  -- Use lem_modulus_of_ae_it to simplify norm (r_int * Complex.exp (I * t))
  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  rw [lem_modulus_of_ae_it h_r_int_pos]
  -- Now we have norm (f (...)) * r_int = r_int * norm (f (...))
  ring

lemma lem_modulus_wz (w z : ℂ) : norm ((w - z) ^ 2) = (norm (w - z)) ^ 2 := by
  -- Apply Complex.abs_pow with n = 2
  exact Complex.norm_pow (w - z) 2

lemma lem_reverse_triangle (w z : ℂ) : norm w - norm z ≤ norm (w - z) := by
  -- Since norm is essentially the norm, use the reverse triangle inequality for norms
  -- Apply the reverse triangle inequality for norms
  exact norm_sub_norm_le w z

lemma lem_reverse_triangle3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z) := by
  -- First establish that |r_int * e^{it}| = r_int
  have h_mod : norm (r_int * Complex.exp (I * t)) = r_int := by
    have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
    exact lem_modulus_of_ae_it h_r_int_pos
  -- Apply the reverse triangle inequality from lem_reverse_triangle
  have h_triangle := lem_reverse_triangle (r_int * Complex.exp (I * t)) z
  -- Substitute h_mod into h_triangle
  rw [h_mod] at h_triangle
  exact h_triangle

lemma lem_zrr1 {R_analytic r_z r_int : ℝ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
0 < r_int - norm z := by
  -- From membership in closed ball, get bound on norm
  have h1 : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
  -- For complex numbers, dist z 0 = ‖z‖
  have h2 : dist z 0 = ‖z‖ := by
    rw [dist_eq_norm, sub_zero]
  -- So ‖z‖ ≤ r_z
  have h3 : ‖z‖ ≤ r_z := by rwa [← h2]
  -- For complex numbers, norm z = ‖z‖
  have h4 : norm z = ‖z‖ := rfl
  -- So norm z ≤ r_z
  have h5 : norm z ≤ r_z := by rwa [h4]
  -- Combined with r_z < r_int, we get norm z < r_int
  have h6 : norm z < r_int := lt_of_le_of_lt h5 h_r_z_lt_r_int
  -- Therefore 0 < r_int - norm z
  linarith

lemma lem_zrr2 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
r_int - r_z ≤ norm (r_int * Complex.exp (I * t) - z) := by
  -- From membership in closed ball, get bound on norm z
  have h1 : norm z ≤ r_z := by
    have h_dist : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm, sub_zero] at h_dist
    exact h_dist
  -- Since norm z ≤ r_z, we have r_int - r_z ≤ r_int - norm z
  have h2 : r_int - r_z ≤ r_int - norm z := by linarith [h1]
  -- Apply lem_reverse_triangle3 to get r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z)
  have h3 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
  -- Combine using transitivity
  exact le_trans h2 h3

lemma lem_zrr3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2 := by
  -- Use lem_zrr2 to get the inequality without squares
  have h_ineq := @lem_zrr2 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Show both sides are nonnegative
  have h_nonneg_left : 0 ≤ r_int - r_z := by linarith [h_r_z_lt_r_int]
  have h_nonneg_right : 0 ≤ norm (r_int * Complex.exp (I * t) - z) := norm_nonneg _
  -- Apply mul_self_le_mul_self to square both sides
  have h_sq := mul_self_le_mul_self h_nonneg_left h_ineq
  -- Convert from a * a to a ^ 2
  rw [pow_two, pow_two]
  exact h_sq

lemma lem_reverse_triangle4 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
0 < norm (r_int * Complex.exp (I * t) - z) := by
  -- Apply lem_zrr1 to get 0 < r_int - norm z
  have h1 := lem_zrr1 h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Apply lem_reverse_triangle3 to get r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z)
  have h2 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
  -- Combine using transitivity
  exact lt_of_lt_of_le h1 h2

lemma lem_wposneq0 (w : ℂ) : norm w > 0 → w ≠ 0 := by
  intro h
  -- Use contrapositive: if w = 0, then norm w = 0
  by_contra h_eq_zero
  -- If w = 0, then norm w = 0
  have h_abs_zero : norm w = 0 := by
    rw [h_eq_zero]
    simp
  -- But this contradicts h : norm w > 0
  rw [h_abs_zero] at h
  exact lt_irrefl 0 h

lemma lem_reverse_triangle5 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
r_int * Complex.exp (I * t) - z ≠ 0 := by
  -- Apply lem_reverse_triangle4 to get 0 < norm (r_int * Complex.exp (I * t) - z)
  have h_pos := @lem_reverse_triangle4 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Apply lem_wposneq0 to conclude the complex number is not zero
  exact lem_wposneq0 (r_int * Complex.exp (I * t) - z) h_pos

lemma lem_reverse_triangle6 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
  -- Apply lem_reverse_triangle5 as suggested in the informal proof
  have h_ne_zero := lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Apply pow_ne_zero (which is the Mathlib version of mul_self_ne_zero for powers)
  exact pow_ne_zero 2 h_ne_zero

lemma lem_absdiv {a b : ℂ} (hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
  -- norm is the norm, so we can use norm_div
  exact norm_div a b

lemma lem_modulus_of_integrand_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
  -- First show that the denominator is nonzero
  have h_neq_zero : r_int * Complex.exp (I * t) - z ≠ 0 :=
    lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Then show that the square is nonzero
  have h_sq_neq_zero : (r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_self_ne_zero.mpr h_neq_zero
  -- Apply lem_absdiv with the right arguments
  rw [lem_absdiv h_sq_neq_zero]
  -- Use lem_modulus_wz to handle the square of absolute value
  rw [lem_modulus_wz]

lemma lem_modulus_of_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
(r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
  -- First apply lem_modulus_of_integrand_product to split the absolute value of the quotient
  rw [lem_modulus_of_integrand_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
  -- Then apply lem_modulus_of_integrand_product3 to simplify the numerator
  rw [lem_modulus_of_integrand_product3 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]

lemma lem_modulus_of_product4 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤
(r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2) := by
  -- First rewrite using lem_modulus_of_product
  rw [lem_modulus_of_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
  -- Now we have: (r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2
  -- We need to show this ≤ (r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2)

  -- Use lem_zrr3 to get the key inequality: (r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2
  have h_ineq := @lem_zrr3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  -- Apply division monotonicity - when denominator increases, fraction decreases
  apply div_le_div_of_nonneg_left
  · -- Numerator is nonnegative
    apply mul_nonneg
    · linarith [h_r_z_pos, h_r_z_lt_r_int]
    · exact norm_nonneg _
  · -- Denominator (r_int - r_z)^2 is positive
    apply pow_pos
    linarith [h_r_z_lt_r_int]
  · -- The key inequality: (r_int - r_z)^2 ≤ Complex.abs(...) ^ 2
    exact h_ineq



lemma lem_bound_on_f_at_r_prime {M R_analytic r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (hr_int_pos : 0 < r_int)
    (hr_int_lt_R_analytic : r_int < R_analytic)
    (f : ℂ → ℂ)
    -- CORRECTED HYPOTHESIS:
    -- f is differentiable on an open set U containing the closed ball.
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ z ∈ Metric.closedBall 0 R_analytic, (f z).re ≤ M)
    (t : ℝ) :
norm (f (r_int * Complex.exp (I * t))) ≤ (2 * r_int * M) / (R_analytic - r_int) := by
  -- Deconstruct the corrected hypothesis
  obtain ⟨U, hU_open, h_subset, hf_diff_U⟩ := hf_domain

  -- Let z₀ be the point of interest
  let z₀ := r_int * Complex.exp (I * t)

  -- The theorem gives a bound on the supremum of |f(z)| over the closed ball of radius r_int.
  have h_sSup_bound := thm_BorelCaratheodoryI R_analytic M hR_analytic_pos hM_pos f
    -- Now we can prove the analyticity hypothesis for the theorem.
    (by
      -- f is analytic on the open set U
      have h_analytic_U : AnalyticOn ℂ f U := hf_diff_U.analyticOn hU_open
      -- Analyticity is preserved on subsets. Since the closed ball is a subset of U...
      -- ...f is analytic on the closed ball.
      rw [ballDR]
      convert h_analytic_U.mono h_subset
      -- ⊢ closure (Metric.ball 0 R_analytic) = Metric.closedBall 0 R_analytic
      apply closure_ball
      linarith
      )
    hf0
    (by rwa [lem_ballDR R_analytic hR_analytic_pos]) -- The sets are the same
    r_int hr_int_pos hr_int_lt_R_analytic

  have hz₀_in_ball : z₀ ∈ Metric.closedBall 0 r_int := by
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, sub_zero]
    -- Need to show: ‖r_int * Complex.exp (I * t)‖ ≤ r_int
    have h_norm : ‖r_int * Complex.exp (I * t)‖ = r_int := by
      rw [norm_mul]
      -- We need to show: ‖↑r_int‖ * ‖Complex.exp (I * ↑t)‖ = r_int
      -- First, ‖↑r_int‖ = |r_int| = r_int (since r_int > 0)
      have h1 : ‖(r_int : ℂ)‖ = r_int := by
        rw [Complex.norm_real]
        exact abs_of_pos hr_int_pos
      -- Second, ‖Complex.exp (I * ↑t)‖ = 1
      have h2 : ‖Complex.exp (I * ↑t)‖ = 1 := by
        -- We already have lem_modulus_of_e_it_is_one for this!
        exact lem_modulus_of_e_it_is_one t
      rw [h1, h2]
      ring
    rw [h_norm]

  -- Since z₀ is in the closed ball, |f(z₀)| is bounded by the supremum
  have hz₀_in_closure : z₀ ∈ closure (ballDR r_int) := by
    rw [lem_ballDR r_int hr_int_pos]
    exact hz₀_in_ball

  -- The image of z₀ under (norm ∘ f) is in the image set
  have h_in_image : norm (f z₀) ∈ (norm ∘ f) '' (closure (ballDR r_int)) := by
    use z₀, hz₀_in_closure
    rfl

  -- Apply the supremum bound
  have h_le_sSup : norm (f z₀) ≤ sSup ((norm ∘ f) '' (closure (ballDR r_int))) := by
    apply le_csSup
    -- Need to show the set is bounded above
    · use (2 * r_int / (R_analytic - r_int)) * M
      intros x hx
      obtain ⟨w, hw_in, hx_eq⟩ := hx
      rw [← hx_eq]
      -- Apply the bound from the theorem
      have hw_in_closed : w ∈ Metric.closedBall 0 r_int := by
        rwa [← lem_ballDR r_int hr_int_pos]
      -- Since w is in a smaller ball, it's also in the larger ball
      have hw_in_R : w ∈ Metric.closedBall 0 R_analytic := by
        have h_subset : Metric.closedBall (0 : ℂ) r_int ⊆ Metric.closedBall 0 R_analytic := by
          apply Metric.closedBall_subset_closedBall
          linarith [hr_int_lt_R_analytic]
        exact h_subset hw_in_closed
      -- Apply the theorem's bound through lem_BCI
      exact lem_BCI R_analytic M hR_analytic_pos hM_pos f
        (by
          rw [ballDR]
          have h_analytic_U : AnalyticOn ℂ f U := hf_diff_U.analyticOn hU_open
          convert h_analytic_U.mono h_subset
          apply closure_ball
          linarith)
        hf0
        (by rwa [lem_ballDR R_analytic hR_analytic_pos])
        r_int hr_int_pos hr_int_lt_R_analytic w
        (by aesop)
    -- The element is in the set
    · exact h_in_image

  -- Combine with the theorem's bound
  calc norm (f z₀)
    ≤ sSup ((norm ∘ f) '' (closure (ballDR r_int))) := h_le_sSup
    _ ≤ (2 * r_int / (R_analytic - r_int)) * M := h_sSup_bound
    _ = (2 * r_int * M) / (R_analytic - r_int) := by ring

lemma lem_bound_on_integrand_modulus {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z)
    (t : ℝ) :
norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
  -- Apply lem_modulus_of_product4 to get intermediate bound
  have h1 := lem_modulus_of_product4 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Apply lem_bound_on_f_at_r_prime to bound |f(r_int * e^{it})|
  have h2 := lem_bound_on_f_at_r_prime hM_pos hR_analytic_pos (lt_trans h_r_z_pos h_r_z_lt_r_int) h_r_int_lt_R_analytic f hf_domain hf0 hRe_f_le_M t

  -- Now we need to combine these bounds properly
  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  have h_denom_nonneg : 0 ≤ (r_int - r_z) ^ 2 := by
    apply sq_nonneg

  -- Multiply both sides of h2 by r_int and divide by (r_int - r_z)^2
  have h3 : (r_int * norm (f (r_int * Complex.exp (I * t)))) / (r_int - r_z) ^ 2 ≤
            (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 := by
    apply div_le_div_of_nonneg_right _ h_denom_nonneg
    apply mul_le_mul_of_nonneg_left h2
    linarith [h_r_int_pos]

  -- Simplify the right-hand side
  have h4 : (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 =
            (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
    have h_R_sub_r_pos : 0 < R_analytic - r_int := by linarith [h_r_int_lt_R_analytic]
    have h_r_sub_r_pos : 0 < r_int - r_z := by linarith [h_r_z_lt_r_int]
    field [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]

  -- Apply transitivity
  rw [h4] at h3
  exact le_trans h1 h3

lemma lem_integral_inequality_aux {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in a..b, g t ≤ ∫ t in a..b, C := by
  -- Apply monotonicity of interval integrals
  -- We need integrability of both functions and the pointwise inequality
  have h_const_integrable : IntervalIntegrable (fun _ => C) MeasureTheory.volume a b :=
    intervalIntegrable_const
  -- Transform h_bound to the right form: ∀ x ∈ Icc a b, g x ≤ (fun _ => C) x
  have h_pointwise : ∀ x ∈ Set.Icc a b, g x ≤ (fun _ => C) x := by
    intro x hx
    simp
    exact h_bound x hx
  -- Apply the monotonicity theorem
  exact intervalIntegral.integral_mono_on hab h_integrable h_const_integrable h_pointwise

lemma lem_integral_inequality {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in Set.Icc a b, g t ≤ ∫ t in Set.Icc a b, C := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact lem_integral_inequality_aux hab h_integrable h_bound

lemma continuous_real_parameterization (r : ℝ) : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := by
  -- Break down the function into continuous components
  -- Step 1: t ↦ (t : ℂ) is continuous
  have h1 : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal

  -- Step 2: z ↦ I * z is continuous (multiplication by constant)
  have h2 : Continuous (fun z : ℂ => I * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  -- Step 3: Complex.exp is continuous
  have h3 : Continuous Complex.exp := Complex.continuous_exp

  -- Step 4: z ↦ (r : ℂ) * z is continuous (multiplication by constant)
  have h4 : Continuous (fun z : ℂ => (r : ℂ) * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  -- Now compose all the steps
  -- fun t => r * Complex.exp (I * t) = h4 ∘ h3 ∘ h2 ∘ h1
  apply Continuous.comp h4
  apply Continuous.comp h3
  apply Continuous.comp h2
  exact h1

lemma continuous_f_parameterized {f : ℂ → ℂ} {R r : ℝ}     (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
 (hr_pos : 0 < r) (hr_lt_R : r < R) : Continuous (fun t : ℝ => f (r * Complex.exp (I * t))) := by
  -- f is continuous on the closed ball since it's differentiable there
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain
  have hf_cont : ContinuousOn f (Metric.closedBall 0 R) := by
    -- First restrict differentiability from U' to the closed ball
    have hf_on_closed : DifferentiableOn ℂ f (Metric.closedBall 0 R) :=
      hf_diff_U'.mono h_subset
    -- Then use the fact that differentiable implies continuous
    exact DifferentiableOn.continuousOn hf_on_closed

  -- The parameterization is continuous
  have hparam_cont : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := continuous_real_parameterization r

  -- Show that the parameterization maps into the closed ball
  have hparam_range : ∀ t : ℝ, r * Complex.exp (I * t) ∈ Metric.closedBall 0 R := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
    -- Convert norm to norm and use lem_modulus_of_ae_it
    change norm (r * Complex.exp (I * t)) ≤ R
    rw [lem_modulus_of_ae_it hr_pos]
    exact le_of_lt hr_lt_R

  -- Apply composition: f continuous on closed ball, parameterization continuous and maps into closed ball
  -- Use ContinuousOn.comp to get continuity on Set.univ
  have hcomp_on : ContinuousOn (fun t : ℝ => f (r * Complex.exp (I * t))) Set.univ := by
    apply ContinuousOn.comp hf_cont (Continuous.continuousOn hparam_cont)
    intro t _
    exact hparam_range t

  -- Convert ContinuousOn Set.univ to Continuous using the equivalence
  rwa [continuousOn_univ] at hcomp_on

lemma continuous_denominator_parameterized (r : ℝ) (z : ℂ) : Continuous (fun t : ℝ => (r * Complex.exp (I * t) - z) ^ 2) := by
  -- Break down the function: (fun t => (r * Complex.exp (I * t) - z) ^ 2)
  -- This is (fun x => x ^ 2) ∘ (fun t => r * Complex.exp (I * t) - z)

  -- First show that t ↦ r * Complex.exp (I * t) - z is continuous
  have h1 : Continuous (fun t : ℝ => r * Complex.exp (I * t) - z) := by
    -- This is the difference of two continuous functions
    apply Continuous.sub
    · -- t ↦ r * Complex.exp (I * t) is continuous by continuous_real_parameterization
      exact continuous_real_parameterization r
    · -- t ↦ z is continuous (constant function)
      exact continuous_const

  -- Then show that x ↦ x ^ 2 is continuous
  have h2 : Continuous (fun x : ℂ => x ^ 2) := continuous_pow 2

  -- Apply composition
  exact Continuous.comp h2 h1

lemma interval_integrable_cauchy_integrand {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} {z : ℂ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
  -- The integrand is continuous, so it's interval integrable
  apply Continuous.intervalIntegrable

  -- Show continuity of the integrand
  apply Continuous.comp continuous_norm

  -- Show the quotient is continuous (denominator never zero by lem_reverse_triangle6)
  apply Continuous.div₀

  -- Show numerator is continuous: t ↦ r_int * exp(I*t) * f(r_int * exp(I*t))
  · apply Continuous.mul
    -- First part: t ↦ r_int * exp(I*t) is continuous
    · exact continuous_real_parameterization r_int
    -- Second part: t ↦ f(r_int * exp(I*t)) is continuous
    · have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
      exact continuous_f_parameterized hf_domain h_r_int_pos h_r_int_lt_R_analytic

  -- Show denominator is continuous: t ↦ (r_int * exp(I*t) - z)^2
  · exact continuous_denominator_parameterized r_int z

  -- Show denominator is never zero (key insight from informal proof)
  · intro t
    exact lem_reverse_triangle6 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

lemma integral_const_over_interval (C : ℝ) :
∫ t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
  -- First convert from Set.Icc to Set.Ioc using integral_Icc_eq_integral_Ioc
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Then convert from Set.Ioc to interval integral using integral_of_le (in reverse)
  have h_le : (0 : ℝ) ≤ 2 * Real.pi := by
    apply mul_nonneg
    · norm_num
    · exact Real.pi_pos.le
  rw [← intervalIntegral.integral_of_le h_le]
  -- Apply the interval integral constant theorem
  rw [intervalIntegral.integral_const]
  -- Simplify: (2 * Real.pi - 0) • C = (2 * Real.pi) * C
  simp [sub_zero, smul_eq_mul]

lemma lem_f_prime_bound_by_integral_of_constant {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
  -- Apply lem_modulus_of_f_prime as stated in the informal proof
  have h1 := lem_modulus_of_f_prime hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  -- Apply lem_bound_on_integrand_modulus as stated in the informal proof
  -- with g(t) = |f(r'e^{it}) r'e^{it} / (r'e^{it} - z)^2| and C = 2(r')^2M/((R-r')(r'-r)^2)
  set C := (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2)

  have h_bound : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    exact lem_bound_on_integrand_modulus hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz t

  -- The integrand in h1 and h_bound are the same up to commutativity of multiplication
  have h_eq : ∀ t, norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
    intro t
    congr 2
    ring

  -- Convert the bound to apply to the integrand in h1
  have h_bound_h1 : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    rw [h_eq]
    exact h_bound t ht

  -- Apply lem_integral_inequality as stated in the informal proof
  have h_integrable : IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
    -- Use the added lemma for integrability
    exact interval_integrable_cauchy_integrand hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  have h2 := lem_integral_inequality ?_ h_integrable h_bound_h1

  -- The integral of constant C over [0, 2π] equals 2π * C
  have h_const_integral : ∫ t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
    -- Use the added lemma for integration of constants
    exact integral_const_over_interval C

  -- Apply the chain of inequalities
  rw [h_const_integral] at h2

  have h3 : (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤
    (1 / (2 * Real.pi)) * (2 * Real.pi * C) := by
    apply mul_le_mul_of_nonneg_left h2
    apply div_nonneg
    · norm_num
    · linarith [Real.pi_pos]

  -- Simplify (1/(2π)) * (2π * C) = C
  have h4 : (1 / (2 * Real.pi)) * (2 * Real.pi * C) = C := by
    have h_pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
    field_simp [h_pi_ne_zero]

  rw [h4] at h3
  exact le_trans h1 h3
  simp [Real.pi_nonneg]

lemma lem_f_prime_bound {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
  -- Use the lemma that has the same statement
  exact lem_f_prime_bound_by_integral_of_constant hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz

lemma lem_r_prime_lt_R {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(r + R) / 2 < R := by
  -- Use the theorem add_div_two_lt_right: (a + b) / 2 < b ↔ a < b
  rw [add_div_two_lt_right]
  exact h_r_lt_R

lemma lem_r_prime_is_intermediate {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
r < (r + R) / 2 ∧ (r + R) / 2 < R := by
  constructor
  · -- Prove r < (r + R) / 2
    rw [left_lt_add_div_two]
    exact h_r_lt_R
  · -- Prove (r + R) / 2 < R
    exact lem_r_prime_lt_R h_r_pos h_r_lt_R

lemma lem_calc_R_minus_r_prime {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
R - ((r + R) / 2) = (R - r) / 2 := by
  field_simp
  ring

lemma lem_calc_denominator_specific {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(R - ((r + R) / 2)) * (((r + R) / 2) - r) ^ 2 = ((R - r) ^ 3) / 8 := by
  -- Use lem_calc_R_minus_r_prime to rewrite the first term
  rw [lem_calc_R_minus_r_prime h_r_pos h_r_lt_R]
  -- Show that ((r + R) / 2) - r = (R - r) / 2
  have h_calc : ((r + R) / 2) - r = (R - r) / 2 := by
    field_simp
    ring
  -- Rewrite using this identity
  rw [h_calc]
  -- Now we have (R - r) / 2 * ((R - r) / 2) ^ 2 = ((R - r) ^ 3) / 8
  -- Simplify: (R - r) / 2 * (R - r)^2 / 4 = (R - r)^3 / 8
  ring

lemma lem_calc_numerator_specific {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
2 * (((r + R) / 2) ^ 2) * M = ((R + r) ^ 2 * M) / 2 := by
  -- Use ring to handle the algebraic manipulation
  ring

lemma lem_frac_simplify {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (((R + r) ^ 2 * M) / 2) / (((R - r) ^ 3) / 8) := by
  -- Unfold the definition of r_prime
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- Apply the numerator lemma
  have h_num := lem_calc_numerator_specific hM_pos hr_pos hr_lt_R
  -- Apply the denominator lemma
  have h_denom := lem_calc_denominator_specific hr_pos hr_lt_R
  -- Rewrite using both lemmas
  rw [← h_num, ← h_denom]

lemma lem_frac_simplify2 {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
((R + r) ^ 2 * M / 2) / ((R - r) ^ 3 / 8) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
  -- This is a division of fractions: (a/b) / (c/d) = (a/b) * (d/c) = ad/bc
  -- We have ((R + r)^2 * M / 2) / ((R - r)^3 / 8) = ((R + r)^2 * M / 2) * (8 / (R - r)^3)
  -- = (8 * (R + r)^2 * M) / (2 * (R - r)^3) = (4 * (R + r)^2 * M) / ((R - r)^3)

  -- First, we need to show that the denominators are nonzero
  have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  have h_eight_ne_zero : (8 : ℝ) ≠ 0 := by norm_num
  have h_R_minus_r_ne_zero : R - r ≠ 0 := by linarith [hr_lt_R]
  have h_R_minus_r_pow_ne_zero : (R - r) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    exact h_R_minus_r_ne_zero

  -- Use field_simp to clear denominators and then ring to simplify
  field_simp [h_two_ne_zero, h_eight_ne_zero, h_R_minus_r_pow_ne_zero]
  ring

lemma lem_frac_simplify3 {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
  -- Unfold the let definition
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- Apply lem_frac_simplify to get the intermediate form
  have h1 := lem_frac_simplify hM_pos hr_pos hr_lt_R
  -- Apply lem_frac_simplify2 to complete the transformation
  have h2 := lem_frac_simplify2 hM_pos hr_pos hr_lt_R
  -- Combine the two steps
  rw [h1, h2]

lemma lem_ineq_R_plus_r_lt_2R {r R : ℝ} (h_r_lt_R : r < R) :
R + r < 2 * R := by
  -- Rewrite 2 * R as R + R
  rw [two_mul]
  -- Now we want to show R + r < R + R, which follows from r < R
  linarith [h_r_lt_R]

lemma lem_R_plus_r_is_positive {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
0 < R + r := by
  -- Since r < R and r > 0, we have R > 0
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  -- Both R > 0 and r > 0, so R + r > 0
  exact add_pos hR_pos hr_pos

lemma lem_square_inequality_strict {a b : ℝ}
    (h_a_pos : 0 < a)
    (h_a_lt_b : a < b) :
a ^ 2 < b ^ 2 := by
  -- From 0 < a, we get 0 ≤ a
  have h_a_nonneg : 0 ≤ a := le_of_lt h_a_pos
  -- From 0 < a and a < b, we get 0 < b, hence 0 ≤ b
  have h_b_pos : 0 < b := lt_trans h_a_pos h_a_lt_b
  have h_b_nonneg : 0 ≤ b := le_of_lt h_b_pos
  -- Apply mul_self_lt_mul_self_iff
  have h_squares := mul_self_lt_mul_self_iff h_a_nonneg h_b_nonneg
  -- Use the forward direction: a < b → a * a < b * b
  have h_mult : a * a < b * b := h_squares.mp h_a_lt_b
  -- Convert from a * a to a ^ 2 and b * b to b ^ 2
  rw [← pow_two, ← pow_two] at h_mult
  exact h_mult

lemma lem_2R_sq_is_4R_sq {R : ℝ} (hR_pos : 0 < R) : (2 * R) ^ 2 = 4 * R ^ 2 := by
  -- Use ring to simplify the algebraic expression
  ring

lemma lem_ineq_R_plus_r_sq {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(R + r) ^ 2 < 4 * R ^ 2 := by
  -- Get R + r < 2 * R
  have h1 := lem_ineq_R_plus_r_lt_2R hr_lt_R
  -- Get 0 < R + r
  have h2 := lem_R_plus_r_is_positive hr_pos hr_lt_R
  -- Apply lem_square_inequality_strict to get (R + r)^2 < (2 * R)^2
  have h3 := lem_square_inequality_strict h2 h1
  -- Use lem_2R_sq_is_4R_sq to rewrite (2 * R)^2 = 4 * R^2
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  have h4 := lem_2R_sq_is_4R_sq hR_pos
  rw [h4] at h3
  exact h3

lemma lem_ineq_R_plus_r_sqM {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
4 * (R + r) ^ 2 * M < 16 * R ^ 2 * M := by
  -- Apply lem_ineq_R_plus_r_sq to get (R + r) ^ 2 < 4 * R ^ 2
  have h_ineq := lem_ineq_R_plus_r_sq hr_pos hr_lt_R
  -- Show that 4 * M > 0
  have h_4M_pos : 0 < 4 * M := by
    apply mul_pos
    · norm_num
    · exact hM_pos
  -- Multiply both sides by 4 * M
  have h_mult := mul_lt_mul_of_pos_right h_ineq h_4M_pos
  -- Rearrange to get the desired form
  convert h_mult using 1
  · ring
  · ring

lemma lem_simplify_final_bound {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) < (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
  -- Apply lem_ineq_R_plus_r_sqM to get the numerator inequality
  have h_num_ineq := lem_ineq_R_plus_r_sqM hM_pos hr_pos hr_lt_R
  -- Show that (R - r)^3 > 0
  have h_denom_pos : 0 < (R - r) ^ 3 := by
    apply pow_pos
    linarith [hr_lt_R]
  -- Apply division monotonicity
  exact div_lt_div_of_pos_right h_num_ineq h_denom_pos

lemma lem_bound_after_substitution {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
  -- Unfold the let binding
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- Apply lem_frac_simplify3 to rewrite the left side
  have h1 := lem_frac_simplify3 hM_pos hr_pos hr_lt_R
  -- Unfold the let in h1 as well
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl] at h1
  rw [h1]
  -- Apply lem_simplify_final_bound to get strict inequality
  have h2 := lem_simplify_final_bound hM_pos hr_pos hr_lt_R
  -- Since < implies ≤, we're done
  exact le_of_lt h2

theorem borel_caratheodory_II {f : ℂ → ℂ} {R M r : ℝ}
    (hR_pos : 0 < R)
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
norm (deriv f z) ≤ (16 * M * R ^ 2) / ((R - r) ^ 3) := by
  -- Set r' = (r + R) / 2 as suggested in the informal proof
  set r_prime := (r + R) / 2

  -- Show that r < r' < R using lem_r_prime_is_intermediate
  have h_intermediate := lem_r_prime_is_intermediate hr_pos hr_lt_R
  have h_r_lt_r_prime := h_intermediate.1
  have h_r_prime_lt_R := h_intermediate.2

  -- Apply lem_f_prime_bound with r_int = r_prime
  have h_bound := lem_f_prime_bound hM_pos hR_pos hr_pos h_r_lt_r_prime h_r_prime_lt_R hf_domain hf0 hRe_f_le_M hz

  -- Apply lem_bound_after_substitution to get the final bound
  have h_final := lem_bound_after_substitution hM_pos hr_pos hr_lt_R

  -- Combine the bounds using transitivity
  have h_combined : norm (deriv f z) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
    exact le_trans h_bound h_final

  -- Rearrange to match the target form: (16 * M * R ^ 2) / ((R - r) ^ 3)
  convert h_combined using 1
  ring

#print axioms borel_caratheodory_II

open Complex MeasureTheory intervalIntegral
open scoped Interval

/-- Definition 1: `I_f` defined along the taxicab (axis-aligned) path. -/
noncomputable def If_taxicab
    {r1 R R0: ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    (Metric.closedBall (0 : ℂ) r1) → ℂ :=
  fun z =>
    (∫ t in (0 : ℝ)..z.1.re, f (t : ℂ))
    + Complex.I * (∫ τ in (0 : ℝ)..z.1.im, f ((z.1.re : ℂ) + Complex.I * τ))

/-- Lemma: `I_f(z+h)` expands by definition. -/
lemma def_If_z_plus_h
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, f (( (z + h).re : ℂ) + Complex.I * τ)) := by
  rfl

/-- Lemma: `I_f(z)` expands by definition. -/
lemma def_If_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) := by
  rfl

/-- Lemma: `I_f(w)` with `w := (z+h).re + i*z.im`. -/
lemma def_If_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  simp [If_taxicab]

lemma continuous_vertical_line (a : ℂ) :
  Continuous (fun τ : ℝ => ((a.re : ℂ) + Complex.I * (τ : ℂ))) := by
  have hconst : Continuous (fun _ : ℝ => (a.re : ℂ)) := continuous_const
  have hmul : Continuous (fun τ : ℝ => (Complex.I : ℂ) * (τ : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  simpa using hconst.add hmul

lemma norm_re_add_I_mul_le_norm (a : ℂ) {τ : ℝ} (hτ : |τ| ≤ |a.im|) :
  ‖((a.re : ℂ) + Complex.I * (τ : ℂ))‖ ≤ ‖a‖ := by
  -- set the auxiliary complex number with same real part and imaginary part τ
  set z1 : ℂ := ((a.re : ℂ) + Complex.I * (τ : ℂ)) with hz1
  -- compute squares of norms via re/im
  have hsq_z1 : ‖z1‖ ^ 2 = z1.re ^ 2 + z1.im ^ 2 := by
    have hx : ‖z1‖ ^ 2 - z1.re ^ 2 = z1.im ^ 2 := Complex.sq_norm_sub_sq_re z1
    have hx' := congrArg (fun t : ℝ => t + z1.re ^ 2) hx
    -- rearrange to get the sum of squares
    have : ‖z1‖ ^ 2 = z1.im ^ 2 + z1.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
  have hsq_a : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    have hx : ‖a‖ ^ 2 - a.re ^ 2 = a.im ^ 2 := Complex.sq_norm_sub_sq_re a
    have hx' := congrArg (fun t : ℝ => t + a.re ^ 2) hx
    have : ‖a‖ ^ 2 = a.im ^ 2 + a.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
  -- simplify re and im of z1
  have hz1_re : z1.re = a.re := by
    simp [hz1, mul_comm]
  have hz1_im : z1.im = τ := by
    simp [hz1, mul_comm]
  -- turn the hypothesis into a squares inequality
  have hτ_sq : τ ^ 2 ≤ a.im ^ 2 := by
    simpa using (sq_le_sq.mpr hτ)
  -- compare squares
  have hsq_le : ‖z1‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have : a.re ^ 2 + τ ^ 2 ≤ a.re ^ 2 + a.im ^ 2 := by gcongr
    simpa [hsq_z1, hz1_re, hz1_im, hsq_a] using this
  -- deduce inequality of norms
  have hnonneg : 0 ≤ ‖a‖ := norm_nonneg _
  exact le_of_sq_le_sq hsq_le hnonneg

lemma closedBall_mono_center0 {r1 R : ℝ} (h : r1 ≤ R) :
  Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
  intro z hz
  have hz' : dist z (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp hz)
  exact Metric.mem_closedBall.mpr (le_trans hz' h)

lemma abs_le_abs_of_mem_uIcc_zero {b t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) b) : |t| ≤ |b| := by
  classical
  by_cases hb : 0 ≤ b
  · -- case 0 ≤ b: uIcc 0 b = Icc 0 b
    have ht' : t ∈ Set.Icc (0 : ℝ) b := by
      simpa [Set.uIcc_of_le hb] using ht
    have ht0 : 0 ≤ t := ht'.1
    have htb : t ≤ b := ht'.2
    have htabs : |t| = t := abs_of_nonneg ht0
    have hbabs : |b| = b := abs_of_nonneg hb
    simpa [htabs, hbabs] using htb
  · -- case b < 0: uIcc 0 b = Icc b 0
    have ht' : t ∈ Set.Icc b 0 := by
      simpa [Set.uIcc_of_not_le hb] using ht
    have hb_le : b ≤ 0 := le_trans ht'.1 ht'.2
    have ht_le0 : t ≤ 0 := ht'.2
    have hbabs : |b| = -b := abs_of_nonpos hb_le
    have htabs : |t| = -t := abs_of_nonpos ht_le0
    have hneg : -t ≤ -b := neg_le_neg ht'.1
    simpa [htabs, hbabs] using hneg

lemma vertical_intervalIntegrable_of_mem_ball
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {a : ℂ}
    (ha : a ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ : ℝ => f (((a.re : ℂ)) + Complex.I * τ)) volume (0 : ℝ) a.im := by
  classical
  -- Continuity of f on the larger closed ball
  have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
  -- Define the vertical line map
  let g : ℝ → ℂ := fun τ => ((a.re : ℂ) + Complex.I * (τ : ℂ))
  -- Continuity of the vertical line map on the interval
  have hg_cont : ContinuousOn g (Set.uIcc (0 : ℝ) a.im) := by
    simpa [g] using (continuous_vertical_line a).continuousOn
  -- The vertical segment stays within the closed ball of radius R
  have hg_maps : Set.MapsTo g (Set.uIcc (0 : ℝ) a.im) (Metric.closedBall (0 : ℂ) R) := by
    intro τ hτ
    have hτabs : |τ| ≤ |a.im| := abs_le_abs_of_mem_uIcc_zero hτ
    have hnorm_le_a : ‖g τ‖ ≤ ‖a‖ := by
      simpa [g] using norm_re_add_I_mul_le_norm a hτabs
    have ha_norm : ‖a‖ ≤ r1 := by
      have : dist a (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp ha)
      simpa [dist_eq_norm] using this
    have hnorm_le_r1 : ‖g τ‖ ≤ r1 := le_trans hnorm_le_a ha_norm
    have hg_mem_r1 : g τ ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le_r1
    exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) hg_mem_r1
  -- Compose continuity to get continuity of the integrand on the interval
  have hcomp : ContinuousOn (fun τ : ℝ => f (g τ)) (Set.uIcc (0 : ℝ) a.im) := by
    -- use `ContinuousOn.comp` with `g := f`, `f := g`
    simpa [Function.comp, g] using
      (ContinuousOn.comp (hg := hf_cont) (hf := hg_cont) (h := hg_maps))
  -- Continuous on the interval implies interval integrable
  have hInt : IntervalIntegrable (fun τ : ℝ => f (g τ)) volume (0 : ℝ) a.im :=
    ContinuousOn.intervalIntegrable (u := fun τ : ℝ => f (g τ)) (a := 0) (b := a.im) hcomp
  simpa [g] using hInt

lemma helper_mul_sub_complex (x y : ℂ) : Complex.I * x - Complex.I * y = Complex.I * (x - y) := by
  simp [mul_sub]

/-- Lemma: `I_f(z+h) - I_f(w)` equals the vertical integral piece. -/
lemma diff_If_zh_w
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  classical
  intro w
  -- Common vertical integrand
  let g : ℝ → ℂ := fun τ => f (((z + h).re : ℂ) + Complex.I * τ)
  -- Interval integrability for the interval subtraction lemma
  have hInt1 : IntervalIntegrable g volume (0 : ℝ) ((z + h).im) := by
    simpa [g] using
      (vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (a := z + h) hzh)
  have hInt2 : IntervalIntegrable g volume (0 : ℝ) (z.im) := by
    have hInt2' :
        IntervalIntegrable
          (fun τ : ℝ => f (((( (((z + h).re : ℂ) + Complex.I * z.im)).re : ℂ)) + Complex.I * τ))
          volume (0 : ℝ) (((((z + h).re : ℂ) + Complex.I * z.im)).im) :=
      vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf
        (a := (((z + h).re : ℂ) + Complex.I * z.im)) hw
    simpa [g] using hInt2'
  have hinterval :
      ((∫ τ in (0 : ℝ)..(z + h).im, g τ) - ∫ τ in (0 : ℝ)..z.im, g τ)
      = ∫ τ in z.im..(z + h).im, g τ :=
    intervalIntegral.integral_interval_sub_left (μ := volume) (f := g) hInt1 hInt2
  -- Expand definitions of If at z+h and w
  have h1 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ) := by
    have hzph := def_If_z_plus_h hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf (z := z) (h := h) hz hzh
    simpa [g] using hzph
  have h2 :
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
          + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ) := by
    have hwdef := def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
    simpa [g, w] using hwdef
  -- Compute the difference and cancel the horizontal piece
  calc
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
        = ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
            + Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [h1, h2]
    _ = (Complex.I * (∫ τ in (0 : ℝ)..(z + h).im, g τ))
          - (Complex.I * (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = Complex.I *
          ((∫ τ in (0 : ℝ)..(z + h).im, g τ)
            - (∫ τ in (0 : ℝ)..z.im, g τ)) := by
      simp [helper_mul_sub_complex]
    _ = Complex.I * (∫ τ in z.im..(z + h).im, g τ) := by
      simpa using congrArg (fun t => Complex.I * t) hinterval
    _ = Complex.I * (∫ τ in z.im..(z + h).im,
          f (((z + h).re : ℂ) + Complex.I * τ)) := by
      simp [g]

lemma diff_If_w_z_initial_form
  {r1 R R0 : ℝ}
  (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z h : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
  (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..w.re, f (t : ℂ))
      + Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (w.re + Complex.I * τ) - f (z.re + Complex.I * τ))) := by
  intro w

  -- Apply def_If_w and def_If_z as suggested in the informal proof
  rw [def_If_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
  rw [def_If_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz]

  -- Note that w.re = (z + h).re and w.im = z.im (key insight from informal proof)
  have hw_re : w.re = (z + h).re := by simp [w]
  have hw_im : w.im = z.im := by simp [w]

  -- Rearrange algebraically to separate horizontal and vertical parts
  have step1 :
    ((∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
      - ((∫ t in (0 : ℝ)..z.re, f (t : ℂ))
        + Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    = (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
      + Complex.I * ((∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
        - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))) := by ring
  rw [step1]

  -- For horizontal integrals, need integrability - use existing infrastructure
  have horizontal_integrable_zh : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) (z + h).re := by
    -- Since f is analytic, it's continuous, hence integrable on intervals
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
    -- Need to show |t| ≤ R, use that t ∈ [0, (z+h).re] and bounds
    have : ‖z + h‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hzh
    have : |(z + h).re| ≤ ‖z + h‖ := Complex.abs_re_le_norm (z + h)
    have : |t| ≤ |(z + h).re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  have horizontal_integrable_z : IntervalIntegrable (fun t : ℝ => f (t : ℂ)) volume (0 : ℝ) z.re := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.comp hf.continuousOn Complex.continuous_ofReal.continuousOn
    intro t ht
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real]
    have : ‖z‖ ≤ r1 := by simp [← dist_zero_right]; exact Metric.mem_closedBall.mp hz
    have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have : |t| ≤ |z.re| := abs_le_abs_of_mem_uIcc_zero ht
    linarith [le_of_lt hr1_lt_R]

  -- Apply interval integral subtraction for horizontal part
  have horizontal_eq :
    (∫ t in (0 : ℝ)..(z + h).re, f (t : ℂ)) - (∫ t in (0 : ℝ)..z.re, f (t : ℂ))
    = ∫ t in z.re..(z + h).re, f (t : ℂ) := by
    rw [← intervalIntegral.integral_interval_sub_left horizontal_integrable_zh horizontal_integrable_z]

  -- For vertical integrals, use the existing integrability lemmas from context directly
  have vertical_integrable_zh : IntervalIntegrable (fun τ : ℝ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
    -- Use w = (z+h).re + I*z.im which is in the ball
    rw [← hw_re, ← hw_im]
    exact vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hw

  have vertical_integrable_z : IntervalIntegrable (fun τ : ℝ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im :=
    vertical_intervalIntegrable_of_mem_ball hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz

  -- Apply integral subtraction for vertical part - "combine integrals" from informal proof
  have vertical_eq :
    (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
      - (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = ∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)) := by
    rw [← intervalIntegral.integral_sub vertical_integrable_zh vertical_integrable_z]

  -- Combine the results using w.re = (z + h).re
  rw [horizontal_eq, vertical_eq, hw_re]

lemma algebraic_rearrangement_four_terms (a b c d : ℂ) :
    a - b + c - d = 0 → c - d = b - a := by
  intro h
  -- From a - b + c - d = 0, directly solve for c - d
  -- We have: a - b + c - d = 0
  -- Rearranging: c - d = 0 - (a - b) = -(a - b) = b - a
  calc c - d
    = (a - b + c - d) - (a - b) := by ring
    _ = 0 - (a - b) := by rw [h]
    _ = -(a - b) := by ring
    _ = b - a := by ring

lemma real_between_as_convex_combination (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ t = (1 - lam) * b₁ + lam * b₂ := by
  -- Use trichotomy to consider cases b₁ ≤ b₂ or b₂ ≤ b₁
  rcases le_total b₁ b₂ with h₁|h₂
  case inl =>
    -- Case: b₁ ≤ b₂
    -- From our hypothesis h, we must have b₁ ≤ t ≤ b₂ (since b₁ ≤ b₂)
    have ht : b₁ ≤ t ∧ t ≤ b₂ := by
      rcases h with h_left|h_right
      · exact h_left
      · -- If b₂ ≤ t ≤ b₁ but b₁ ≤ b₂, then combining gives the right inequalities
        exact ⟨le_trans h₁ h_right.1, le_trans h_right.2 h₁⟩

    -- Set λ = (t - b₁)/(b₂ - b₁)
    by_cases heq : b₁ = b₂
    · -- If b₁ = b₂, then t = b₁ = b₂, so use λ = 0
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [heq] at ht ⊢
        have : t = b₂ := le_antisymm ht.2 ht.1
        rw [this]
        ring
    · -- If b₁ ≠ b₂, then b₁ < b₂
      have hlt : b₁ < b₂ := lt_of_le_of_ne h₁ heq
      let lam := (t - b₁) / (b₂ - b₁)
      use lam
      constructor
      · -- 0 ≤ lam
        apply div_nonneg
        · linarith [ht.1]
        · linarith [hlt]
      constructor
      · -- lam ≤ 1, using div_le_iff₀
        rw [div_le_iff₀]
        · linarith [ht.2]  -- t - b₁ ≤ b₂ - b₁ follows from t ≤ b₂
        · linarith [hlt]   -- b₂ - b₁ > 0
      · -- t = (1 - lam) * b₁ + lam * b₂
        unfold lam
        have h_nonzero : b₂ - b₁ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero]
        ring
  case inr =>
    -- Case: b₂ ≤ b₁
    -- From our hypothesis h, we must have b₂ ≤ t ≤ b₁
    have ht : b₂ ≤ t ∧ t ≤ b₁ := by
      rcases h with h_left|h_right
      · -- If b₁ ≤ t ≤ b₂ but b₂ ≤ b₁, then combining gives the right inequalities
        exact ⟨le_trans h₂ h_left.1, le_trans h_left.2 h₂⟩
      · exact h_right

    -- Set λ = (b₁ - t)/(b₁ - b₂)
    by_cases heq : b₁ = b₂
    · -- If b₁ = b₂, then t = b₁ = b₂, so use λ = 0
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [← heq] at ht ⊢
        have : t = b₁ := le_antisymm ht.2 ht.1
        rw [this, heq]
        ring
    · -- If b₁ ≠ b₂, then b₂ < b₁
      have hlt : b₂ < b₁ := lt_of_le_of_ne h₂ (Ne.symm heq)
      let lam := (b₁ - t) / (b₁ - b₂)
      use lam
      constructor
      · -- 0 ≤ lam
        apply div_nonneg
        · linarith [ht.2]  -- b₁ - t ≥ 0 from t ≤ b₁
        · linarith [hlt]   -- b₁ - b₂ > 0
      constructor
      · -- lam ≤ 1, using div_le_iff₀
        rw [div_le_iff₀]
        · linarith [ht.1]  -- b₁ - t ≤ b₁ - b₂ follows from b₂ ≤ t
        · linarith [hlt]   -- b₁ - b₂ > 0
      · -- t = (1 - lam) * b₁ + lam * b₂
        unfold lam
        have h_nonzero : b₁ - b₂ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero]
        ring

lemma convex_combination_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : E) (t : ℝ)
  (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
  (1 - t) • x + t • y ∈ segment ℝ x y := by
  -- By definition, segment ℝ x y = {z | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = z}
  -- We need to show there exist a, b with the right properties
  -- Let a = 1 - t and b = t
  use (1 - t), t
  constructor
  · -- 0 ≤ 1 - t
    linarith [h₁]
  constructor
  · -- 0 ≤ t
    exact h₀
  constructor
  · -- (1 - t) + t = 1
    ring
  · -- (1 - t) • x + t • y = (1 - t) • x + t • y
    rfl

lemma vertical_line_in_segment (a : ℂ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  a + Complex.I * t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
  -- Get convex combination representation for t
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h

  -- Show that a + I*t is a convex combination of the endpoints
  have h_convex : a + Complex.I * t = (1 - lam) • (a + Complex.I * b₁) + lam • (a + Complex.I * b₂) := by
    -- Use scalar multiplication definition
    simp only [Complex.real_smul]
    -- Substitute t = (1 - lam) * b₁ + lam * b₂
    rw [h_t_eq]
    -- Convert to complex numbers
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    -- Use distributivity: I * ((1-lam)*b₁ + lam*b₂) = I*(1-lam)*b₁ + I*lam*b₂
    rw [mul_add]
    -- Rearrange using commutativity and associativity
    ring

  -- Apply convex_combination_mem_segment
  rw [h_convex]
  exact convex_combination_mem_segment (a + Complex.I * b₁) (a + Complex.I * b₂) lam h_lam_nonneg h_lam_le_one

lemma horizontal_line_in_segment (a : ℝ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  (t : ℂ) + Complex.I * a ∈ segment ℝ ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) := by
  -- Represent t as a convex combination of b₁ and b₂
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h
  -- Show the point is the corresponding convex combination of endpoints
  have h_convex : (t : ℂ) + Complex.I * a
      = (1 - lam) • ((b₁ : ℂ) + Complex.I * a) + lam • ((b₂ : ℂ) + Complex.I * a) := by
    simp only [Complex.real_smul]
    -- substitute t
    rw [h_t_eq]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  -- Conclude membership in the segment
  simpa [h_convex] using
    (convex_combination_mem_segment ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) lam h_lam_nonneg h_lam_le_one)

lemma intervalIntegrable_of_continuousOn_range (f : ℂ → ℂ) (g : ℝ → ℂ) (a b : ℝ) (S : Set ℂ)
  (hf : ContinuousOn f S) (hg : Continuous g)
  (hrange : ∀ t ∈ Set.uIcc a b, g t ∈ S) :
  IntervalIntegrable (f ∘ g) volume a b := by
  -- Apply the composition theorem for continuous functions
  have h_comp : ContinuousOn (f ∘ g) (Set.uIcc a b) := by
    apply ContinuousOn.comp hf (hg.continuousOn) hrange
  -- Continuous functions on closed intervals are interval integrable
  exact h_comp.intervalIntegrable

lemma intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {a : ℂ} {b₁ b₂ : ℝ}
  (h₁ : ‖a + Complex.I * b₁‖ ≤ r1) (h₂ : ‖a + Complex.I * b₂‖ ≤ r1) :
  IntervalIntegrable (fun t => f (a + Complex.I * t)) volume b₁ b₂ := by
  -- Use the existing lemma intervalIntegrable_of_continuousOn_range
  apply intervalIntegrable_of_continuousOn_range f (fun t => a + Complex.I * ↑t) b₁ b₂ (Metric.closedBall (0 : ℂ) R)
  · -- f is continuous on the closed ball of radius R (since it's analytic there)
    exact AnalyticOnNhd.continuousOn hf
  · -- The path function t ↦ a + I*t is continuous
    exact Continuous.add continuous_const (Continuous.mul continuous_const continuous_ofReal)
  · -- The range is contained in the closed ball of radius R
    intro t ht
    -- First show the point is in the ball of radius r1 using convexity
    have h_in_r1 : ‖a + Complex.I * ↑t‖ ≤ r1 := by
      -- The point lies on the segment between the endpoints
      have h_segment : a + Complex.I * ↑t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
        apply vertical_line_in_segment
        exact Set.mem_uIcc.mp ht
      -- Convert endpoint conditions to closed ball membership
      have h₁_mem : a + Complex.I * b₁ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : a + Complex.I * b₂ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      -- Use convexity of the closed ball
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
    -- Since r1 < R, the point is also in the ball of radius R
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

/-- Cauchy–Goursat for rectangles with mixed-corner hypotheses ensuring containment. -/
lemma cauchy_for_rectangles
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r1)
    (hzw : ((w.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1)
    (hwz : ((z.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (z.im)))
    - (∫ x in z.re..w.re, f ((x : ℂ) + Complex.I * (w.im)))
    + Complex.I * (∫ y in z.im..w.im, f ((w.re : ℂ) + Complex.I * y))
    - Complex.I * (∫ y in z.im..w.im, f ((z.re : ℂ) + Complex.I * y)) = 0 := by
  classical
  -- 1) Four corners are in the small closed ball r1 by hypotheses hz, hw, hzw, hwz.
  have hA : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
    -- This point equals z
    have hz_eq : z = (z.re : ℂ) + Complex.I * z.im := by
      exact (lem_wReIm z)
    rwa [← hz_eq]
  have hC : ((w.re : ℂ) + Complex.I * w.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
    -- This point equals w
    have hw_eq : w = (w.re : ℂ) + Complex.I * w.im := by
      exact (lem_wReIm w)
    rwa [← hw_eq]
  -- 2) Any horizontal or vertical segment between these corners stays in the ball by convexity.
  have h_left_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (z.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im) ((z.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (z.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hA hwz hseg
  have h_right_in_ball : ∀ y ∈ Set.uIcc z.im w.im,
      ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro y hy
    have hseg : (w.re : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((w.re : ℂ) + Complex.I * z.im) ((w.re : ℂ) + Complex.I * w.im) := by
      simpa using vertical_line_in_segment (a := (w.re : ℂ)) (b₁ := z.im) (b₂ := w.im) (t := y)
        (h := Set.mem_uIcc.mp hy)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hzw hC hseg
  have h_point_in_ball : ∀ x ∈ Set.uIcc z.re w.re, ∀ y ∈ Set.uIcc z.im w.im,
      ((x : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := by
    intro x hx y hy
    have hL : ((z.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_left_in_ball y hy
    have hR' : ((w.re : ℂ) + Complex.I * (y : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 := h_right_in_ball y hy
    -- x between the horizontal endpoints → point on the segment
    obtain ⟨lam, hlam0, hlam1, hx_eq⟩ := real_between_as_convex_combination z.re w.re x (Set.mem_uIcc.mp hx)
    have hseg_horiz : (x : ℂ) + Complex.I * (y : ℂ)
        ∈ segment ℝ ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
      -- write as convex combination
      have : (x : ℂ) + Complex.I * (y : ℂ)
          = (1 - lam) • ((z.re : ℂ) + Complex.I * (y : ℂ)) + lam • ((w.re : ℂ) + Complex.I * (y : ℂ)) := by
        simp only [Complex.real_smul]
        -- Use the convex combination equation for x
        rw [hx_eq]
        simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      simpa [this] using
        (convex_combination_mem_segment ((z.re : ℂ) + Complex.I * (y : ℂ)) ((w.re : ℂ) + Complex.I * (y : ℂ)) lam hlam0 hlam1)
    exact (convex_closedBall (0 : ℂ) r1).segment_subset hL hR' hseg_horiz
  -- 3) Turn pointwise bound into subset for the whole rectangle
  set S := ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
  have hS_subset_r1 : S ⊆ Metric.closedBall (0 : ℂ) r1 := by
    intro p hp
    have hx : p.re ∈ [[z.re, w.re]] := hp.1
    have hy : p.im ∈ [[z.im, w.im]] := hp.2
    -- Rebuild p from its components and apply pointwise bound
    have : ((p.re : ℂ) + Complex.I * (p.im : ℂ)) ∈ Metric.closedBall (0 : ℂ) r1 :=
      h_point_in_ball p.re hx p.im hy
    -- Use lem_wReIm to rewrite p = (p.re : ℂ) + Complex.I * (p.im : ℂ)
    have hp_eq : p = (p.re : ℂ) + Complex.I * (p.im : ℂ) := lem_wReIm p
    rwa [hp_eq]
  have hS_subset_R : S ⊆ Metric.closedBall (0 : ℂ) R :=
    fun p hp => (closedBall_mono_center0 (le_of_lt hr1_lt_R)) (hS_subset_r1 hp)
  -- 4) DifferentiableOn on the rectangle from AnalyticOnNhd on the bigger ball
  have Hdiff : DifferentiableOn ℂ f S := by
    intro p hp
    have hpR : p ∈ Metric.closedBall (0 : ℂ) R := hS_subset_R hp
    exact (hf p hpR).differentiableAt.differentiableWithinAt
  -- 5) Apply Cauchy–Goursat theorem and normalize scalars
  simpa [smul_eq_mul, smul_eq_mul, mul_comm] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w Hdiff

/-- Horizontal-strip Cauchy identity specialized to `w := (z+h).re + i z.im`. -/
lemma cauchy_for_horizontal_strip
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    - (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    + Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)) = 0 := by
  -- Specialize rectangle lemma to z₀ := (z.re : ℂ) and w₀ := (z+h).re + I*z.im
  let z₀ : ℂ := (z.re : ℂ)
  let w₀ : ℂ := (z + h).re + Complex.I * z.im
  -- Endpoint memberships
  have hz₀ : z₀ ∈ Metric.closedBall (0 : ℂ) r1 := by
    have hz_norm : ‖z‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzre_le : ‖(z.re : ℂ)‖ ≤ ‖z‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm z
    have : ‖z₀‖ ≤ r1 := le_trans hzre_le hz_norm
    simpa [z₀, Metric.mem_closedBall, dist_eq_norm] using this
  have hw₀ : w₀ ∈ Metric.closedBall (0 : ℂ) r1 := hw
  -- Mixed-corner memberships: simplified approach
  have hzw : ((w₀.re : ℂ) + Complex.I * z₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
    -- This equals (((z+h).re : ℂ) + I*0) = ((z+h).re : ℂ)
    have h1 : ((w₀.re : ℂ) + Complex.I * z₀.im) = ((z + h).re : ℂ) := by
      simp [w₀, z₀, Complex.ofReal_im, mul_zero, add_zero]
    rw [h1]
    have h2 : ‖((z + h).re : ℂ)‖ ≤ ‖z + h‖ := by
      rw [Complex.norm_real]
      exact Complex.abs_re_le_norm (z + h)
    have h3 : ‖z + h‖ ≤ r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzh
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_trans h2 h3
  have hwz : ((z₀.re : ℂ) + Complex.I * w₀.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
    -- This equals ((z.re : ℂ) + I*z.im) = z
    have h1 : ((z₀.re : ℂ) + Complex.I * w₀.im) = z := by
      simp [z₀, w₀, Complex.ofReal_re]
      exact (lem_wReIm z).symm
    rw [h1]
    exact hz
  -- Apply rectangle Cauchy–Goursat
  have H := cauchy_for_rectangles (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz₀ hw₀ hzw hwz

  -- Now we simplify H using the fact that:
  -- z₀.re = z.re, z₀.im = 0, w₀.re = (z+h).re, w₀.im = z.im
  rw [(show z₀.re = z.re by simp [z₀])] at H
  rw [(show z₀.im = (0 : ℝ) by simp [z₀])] at H
  rw [(show w₀.re = (z + h).re by simp [w₀])] at H
  rw [(show w₀.im = z.im by simp [w₀])] at H

  -- Simplify Complex.I * ↑0 = 0 and ↑x + 0 = ↑x in the integrands
  convert H using 1
  simp only [Complex.ofReal_zero, mul_zero, add_zero]


lemma integrability_from_cauchy_horizontal_strip
    {r1 R R0 : ℝ} (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r1) (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im ∧
    IntervalIntegrable (fun τ => f ((z.re : ℂ) + Complex.I * τ)) volume (0 : ℝ) z.im := by
  constructor
  · -- First integrand: f (((z + h).re : ℂ) + Complex.I * τ)
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    · -- ‖((z + h).re : ℂ) + Complex.I * 0‖ ≤ r1
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hzh
      exact le_trans (Complex.abs_re_le_norm (z + h)) hzh
    · -- ‖((z + h).re : ℂ) + Complex.I * z.im‖ ≤ r1
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact hw
  · -- Second integrand: f ((z.re : ℂ) + Complex.I * τ)
    apply intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball hr1_lt_R hf
    · -- ‖(z.re : ℂ) + Complex.I * 0‖ ≤ r1
      simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.norm_real]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact le_trans (Complex.abs_re_le_norm z) hz
    · -- ‖(z.re : ℂ) + Complex.I * z.im‖ ≤ r1
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [← lem_wReIm z]
      exact hz

lemma cauchy_rearrangement_step1
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ)))
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) - (∫ t in z.re..(z + h).re, f (t : ℂ)) := by
  -- Start with the Cauchy identity
  have H := cauchy_for_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  -- Get integrability conditions
  have integrable := integrability_from_cauchy_horizontal_strip hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  -- Use the available algebraic rearrangement lemma
  have rearrange := algebraic_rearrangement_four_terms
    (∫ t in z.re..(z + h).re, f (t : ℂ))
    (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ)))
    (Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ)))
    H

  -- Now use linearity to combine the vertical integrals on the right side of rearrange
  have vertical_linearity :
    Complex.I * (∫ τ in (0 : ℝ)..z.im, f (((z + h).re : ℂ) + Complex.I * τ))
    - Complex.I * (∫ τ in (0 : ℝ)..z.im, f ((z.re : ℂ) + Complex.I * τ))
    = Complex.I * (∫ τ in (0 : ℝ)..z.im, (f (((z + h).re : ℂ) + Complex.I * τ) - f ((z.re : ℂ) + Complex.I * τ))) := by
    rw [← mul_sub]
    rw [← intervalIntegral.integral_sub integrable.1 integrable.2]

  -- Combine the results
  rw [← vertical_linearity]
  exact rearrange

lemma diff_If_w_z
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
    If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
      - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
      = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by

  -- Following the informal proof exactly:
  -- Step 1: Apply diff_If_w_z_initial_form (mentioned in informal proof)
  have initial_form := diff_If_w_z_initial_form hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  -- Step 2: Apply cauchy_rearrangement_step1 (mentioned in informal proof)
  have rearrange_step := cauchy_rearrangement_step1 hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  -- Step 3: Note that w.re = (z + h).re by definition
  have w_re_eq : (((z + h).re : ℂ) + Complex.I * z.im).re = (z + h).re := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]

  -- Step 4: Work directly with the expressions - use simp_rw to handle let binding
  simp_rw [initial_form, w_re_eq, rearrange_step]

  -- Step 5: Now we have: ∫ f(t) dt + (∫ f(t + i z.im) dt - ∫ f(t) dt) = ∫ f(t + i z.im) dt
  -- The terms cancel: a + (b - a) = b
  ring

/-- Sum of the two differences gives the L-shaped path integral from `z` to `z+h`. -/
lemma If_difference_is_L_path_integral
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
      + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by
  -- According to the informal proof, we use the identity:
  -- I_f(z+h) - I_f(z) = (I_f(w) - I_f(z)) + (I_f(z+h) - I_f(w))
  -- where w = ((z + h).re : ℂ) + Complex.I * z.im
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im

  -- Split the difference using the telescoping identity
  calc If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
       - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩
     = (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
        - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩)
       + (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩
          - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩) := by ring
     _ = Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ))
       + (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im)) := by
       rw [diff_If_zh_w hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw,
           diff_If_w_z hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw]
     _ = (∫ t in z.re..(z + h).re, f (t + Complex.I * z.im))
       + Complex.I * (∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ)) := by ring

/-- Add–subtract `f z` inside each integrand (pure algebra). -/
lemma If_diff_add_sub_identity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z) + f z)
    + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) := by
  -- Start from `If_difference_is_L_path_integral` and rewrite integrands as `(g - f z) + f z`.
  have H :=
    If_difference_is_L_path_integral (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one) hf hz hzh hw
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using H

lemma intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {im_part : ℝ} {a b : ℝ}
  (h₁ : ‖(a : ℂ) + Complex.I * im_part‖ ≤ r1) (h₂ : ‖(b : ℂ) + Complex.I * im_part‖ ≤ r1) :
  IntervalIntegrable (fun t => f ((t : ℂ) + Complex.I * im_part)) volume a b := by
  -- Use the existing lemma intervalIntegrable_of_continuousOn_range
  apply intervalIntegrable_of_continuousOn_range f (fun t => (t : ℂ) + Complex.I * im_part) a b (Metric.closedBall (0 : ℂ) R)
  · -- f is continuous on the closed ball of radius R (since it's analytic there)
    exact AnalyticOnNhd.continuousOn hf
  · -- The path function t ↦ (t : ℂ) + Complex.I * im_part is continuous
    exact Continuous.add continuous_ofReal continuous_const
  · -- The range is contained in the closed ball of radius R
    intro t ht
    -- First show the point is in the ball of radius r1 using convexity
    have h_in_r1 : ‖(t : ℂ) + Complex.I * im_part‖ ≤ r1 := by
      -- The point lies on the segment between the endpoints
      have h_segment : (t : ℂ) + Complex.I * im_part ∈ segment ℝ ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) := by
        -- Use horizontal line in segment (implement inline)
        -- Get convex combination representation for t
        obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination a b t (Set.mem_uIcc.mp ht)

        -- Show that (t : ℂ) + Complex.I * im_part is a convex combination of the endpoints
        have h_convex : (t : ℂ) + Complex.I * im_part = (1 - lam) • ((a : ℂ) + Complex.I * im_part) + lam • ((b : ℂ) + Complex.I * im_part) := by
          -- Use scalar multiplication definition
          simp only [Complex.real_smul]
          -- Substitute t = (1 - lam) * a + lam * b
          rw [h_t_eq]
          -- Convert to complex numbers
          simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
          -- Use distributivity and rearrange
          ring

        -- Apply convex_combination_mem_segment
        rw [h_convex]
        exact convex_combination_mem_segment ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) lam h_lam_nonneg h_lam_le_one

      -- Convert endpoint conditions to closed ball membership
      have h₁_mem : (a : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : (b : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      -- Use convexity of the closed ball
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
    -- Since r1 < R, the point is also in the ball of radius R
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

/-- Apply linearity of the integral to split the two addends. -/
lemma If_diff_linearity
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    =
    ((∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
     + (∫ t in z.re..(z + h).re, f z))
    + Complex.I *
      ((∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))
       + (∫ τ in z.im..(z + h).im, f z)) := by
  -- Start with the identity from If_diff_add_sub_identity as mentioned in the informal proof
  have H := If_diff_add_sub_identity hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw

  -- Set up integrability conditions needed for linearity
  -- Convert membership to norm bounds
  have hz_norm : ‖z‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
  have hzh_norm : ‖z + h‖ ≤ r1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzh
  have hw_norm : ‖((z + h).re : ℂ) + Complex.I * z.im‖ ≤ r1 := by
    rwa [Metric.mem_closedBall, dist_zero_right] at hw

  -- Use the identity w = w.re + I * w.im
  have h_z_eq : z = (z.re : ℂ) + Complex.I * z.im := lem_wReIm z
  have h_zh_eq : z + h = ((z + h).re : ℂ) + Complex.I * (z + h).im := lem_wReIm (z + h)

  -- Establish integrability for horizontal direction
  have hz_endpoint : ‖(z.re : ℂ) + Complex.I * z.im‖ ≤ r1 := by rwa [← h_z_eq]
  have h_horiz_integrable := intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
    hr1_lt_R hf hz_endpoint hw_norm

  -- Establish integrability for vertical direction
  have hzh_endpoint : ‖((z + h).re : ℂ) + Complex.I * (z + h).im‖ ≤ r1 := by rwa [← h_zh_eq]
  have h_vert_integrable := intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
    hr1_lt_R hf hw_norm hzh_endpoint

  -- Constant functions are always integrable
  have h_const_horiz : IntervalIntegrable (fun _ => f z) volume z.re (z + h).re := intervalIntegrable_const
  have h_const_vert : IntervalIntegrable (fun _ => f z) volume z.im (z + h).im := intervalIntegrable_const

  -- Differences are integrable since both components are
  have h_diff_horiz : IntervalIntegrable (fun t => f (t + Complex.I * z.im) - f z) volume z.re (z + h).re :=
    IntervalIntegrable.sub h_horiz_integrable h_const_horiz

  have h_diff_vert : IntervalIntegrable (fun τ => f (((z + h).re : ℂ) + Complex.I * τ) - f z) volume z.im (z + h).im :=
    IntervalIntegrable.sub h_vert_integrable h_const_vert

  -- Apply the key linearity property ∫(g+k) = ∫g + ∫k as mentioned in informal proof
  have h1 : ∫ t in z.re..(z + h).re, ((f (t + Complex.I * z.im) - f z) + f z) =
           (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)) + (∫ t in z.re..(z + h).re, f z) :=
    intervalIntegral.integral_add h_diff_horiz h_const_horiz

  have h2 : ∫ τ in z.im..(z + h).im, ((f (((z + h).re : ℂ) + Complex.I * τ) - f z) + f z) =
           (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)) + (∫ τ in z.im..(z + h).im, f z) :=
    intervalIntegral.integral_add h_diff_vert h_const_vert

  -- Combine the results using H and the linearity results, then distribute multiplication
  rw [H, h1, h2, mul_add]

/-- Integrating the constant function along the L-path yields `f z * h`. -/
lemma integral_of_constant_over_L_path
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ t in z.re..(z + h).re, f z) + Complex.I * (∫ τ in z.im..(z + h).im, f z)
      = f z * h := by
  -- Step 1: Apply integral_const to evaluate the integrals
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const]

  -- Step 2: Simplify the differences using complex addition properties
  rw [Complex.add_re, Complex.add_im]
  simp only [add_sub_cancel_left]

  -- Convert scalar multiplication to regular multiplication
  rw [Complex.real_smul, Complex.real_smul]

  -- Use associativity: Complex.I * (h.im * f z) = (Complex.I * h.im) * f z
  rw [← mul_assoc]

  -- Factor out f z using right distributivity
  rw [← add_mul]

  -- Use commutativity to swap I * ↑h.im to ↑h.im * I to match Complex.re_add_im pattern
  rw [mul_comm Complex.I (↑h.im)]

  -- Now use complex decomposition: ↑h.re + ↑h.im * I = h
  rw [Complex.re_add_im h]

  -- Apply commutativity to get f z * h
  rw [mul_comm]

/-- Final decomposition with an explicit error term. -/
noncomputable def Err
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (z h : ℂ) : ℂ :=
  (∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
  + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))

lemma If_diff_decomposition_final
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
    (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
    = f z * h
      + Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
  -- Step 1: horizontal/vertical decomposition via the horizontal-path Cauchy identity
  have H :=
    If_diff_linearity (hr1_pos) (hr1_lt_R) (hR_lt_R0) (hR0_lt_one)
      (f := f) (hf := hf)
      (z := z) (h := h)
      (hz := hz) (hzh := hzh) (hw := hw)
  -- Step 2: introduce the four auxiliary integrals for readability
  let A : ℂ := ∫ t in z.re..(z + h).re, f (t + Complex.I * z.im) - f z
  let B : ℂ := ∫ t in z.re..(z + h).re, f z
  let C : ℂ := ∫ τ in z.im..(z + h).im, f (((z + h).re : ℂ) + Complex.I * τ) - f z
  let D : ℂ := ∫ τ in z.im..(z + h).im, f z
  -- Step 3: rewrite RHS from the previous lemma in terms of A,B,C,D
  have hH' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + B) + Complex.I * (C + D) := by
    simpa [A, B, C, D, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using H
  -- Step 4: algebraic rearrangement: (A+B) + i(C+D) = (A + iC) + (B + iD)
  have hsplit : (A + B) + Complex.I * (C + D)
      = (A + Complex.I * C) + (B + Complex.I * D) := by ring
  have hH'' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + (B + Complex.I * D) := by
    simpa [hsplit] using hH'
  -- Step 5: replace B + iD by f z * h (constant-path integral)
  have hBD : (B + Complex.I * D) = f z * h := by
    simpa [B, D] using
      integral_of_constant_over_L_path (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh
  have hH''' : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = (A + Complex.I * C) + f z * h := by
    simpa [hBD] using hH''
  -- Step 6: replace (A + iC) by Err and reorder to match target
  have hH4 : (If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩
     - If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩)
     = Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h + f z * h := by
    simpa [Err, A, C, add_comm, add_left_comm, add_assoc] using hH'''
  -- Step 7: finish by reordering sums to the stated form
  simpa [Err, add_comm, add_left_comm, add_assoc] using hH4

noncomputable def S_horiz (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
        r = ‖f (t + Complex.I * z.im) - f z‖}

noncomputable def S_vert (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
        r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}

noncomputable def S_max (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  max (S_horiz z h f) (S_vert z h f)

lemma bound_on_Err
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖
      ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := by
  -- Unfold the error term and prepare to bound each piece
  unfold Err
  -- Triangle inequality for the sum
  have hsplit :
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
      ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
        + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ :=
    norm_add_le _ _

  -- Pull out the factor ‖I‖ = 1 on the vertical term
  have hI : ‖Complex.I‖ = (1 : ℝ) := by simp
  have hvertnorm :
      ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
        = ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by
    simp [norm_mul, hI, one_mul]

  -- Show the sets defining S_horiz/S_vert are bounded above via compactness of images
  set SH : Set ℝ := {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
      r = ‖f (t + Complex.I * z.im) - f z‖}
  have hbdd_SH : BddAbove SH := by
    classical
    -- continuous map r(t) on a compact interval
    have hK : IsCompact (Set.uIcc z.re (z + h).re) := isCompact_uIcc
    -- path into the closed ball R
    let γ : ℝ → ℂ := fun t => (t : ℂ) + Complex.I * z.im
    have hγ_cont : Continuous γ := by
      simpa [γ] using (Complex.continuous_ofReal.add continuous_const)
    have hz_mem : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show (z.re : ℂ) + Complex.I * z.im = z.re + z.im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have hw_mem : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hw
    have hseg_subset :
        (γ '' Set.uIcc z.re (z + h).re) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim
      rcases hwim with ⟨t, ht, rfl⟩
      -- point on the horizontal segment between the two endpoints
      have hseg : ((t : ℂ) + Complex.I * z.im)
          ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * z.im) := by
        -- reparametrize uIcc as a segment in ℝ, then map affinely
        -- use the helper from earlier, massaging membership with Set.mem_uIcc
        have := horizontal_line_in_segment (a := z.im) (b₁ := z.re) (b₂ := (z + h).re)
          (t := t) (by simpa [Set.mem_uIcc] using ht)
        simpa using this
      have hz_in : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hz_mem
      have hw_in : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hw_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simpa [Metric.mem_closedBall, dist_zero_right] using hw'
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
    -- compose with continuous path (restricted to uIcc)
    have hmaps : Set.MapsTo γ (Set.uIcc z.re (z + h).re) (Metric.closedBall (0 : ℂ) R) := by
      intro t ht
      have himg_r1 : γ t ∈ Metric.closedBall (0 : ℂ) r1 := by
        exact hseg_subset (Set.mem_image_of_mem _ ht)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) himg_r1
    have hcont_on : ContinuousOn (fun t => f (γ t)) (Set.uIcc z.re (z + h).re) := by
      simpa [Function.comp, γ] using
        (ContinuousOn.comp (hf_cont) (hγ_cont.continuousOn) hmaps)
    -- real-valued continuous map r(t) := ‖f (γ t) - f z‖
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun t => ‖f (γ t) - f z‖) (Set.uIcc z.re (z + h).re) := by
      -- first get continuity of f (γ t) - f z
      have h_cont_sub : ContinuousOn (fun t => f (γ t) - f z) (Set.uIcc z.re (z + h).re) :=
        hcont_on.sub continuousOn_const
      -- then apply norm
      exact h_cont_sub.norm
    -- image is compact, hence bounded above
    have himage_compact : IsCompact ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      IsCompact.image_of_continuousOn hK hR_cont
    -- Now, SH equals this image set
    have hSH_eq : SH = (fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re := by
      ext r; constructor
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    -- Compact subset of ℝ is bounded above
    have : BddAbove ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      himage_compact.bddAbove
    simpa [hSH_eq] using this

  set SV : Set ℝ := {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
      r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}
  have hbdd_SV : BddAbove SV := by
    classical
    -- compactness of the vertical segment
    have hK : IsCompact (Set.uIcc z.im (z + h).im) := isCompact_uIcc
    let γv : ℝ → ℂ := fun τ => ((z + h).re : ℂ) + Complex.I * τ
    have hγv_cont : Continuous γv := by
      have hmul : Continuous (fun τ : ℝ => Complex.I * (τ : ℂ)) := by
        exact continuous_const.mul Complex.continuous_ofReal
      simp only [γv]
      exact continuous_const.add hmul
    have hw_mem' : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have hzh_mem : (((z + h).re : ℂ) + Complex.I * (z + h).im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show ((z + h).re : ℂ) + Complex.I * (z + h).im = (z + h).re + (z + h).im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hzh
    have hseg_subset :
        (γv '' Set.uIcc z.im (z + h).im) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim; rcases hwim with ⟨τ, hτ, rfl⟩
      have hseg : (((z + h).re : ℂ) + Complex.I * τ)
          ∈ segment ℝ (((z + h).re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * (z + h).im) := by
        have := vertical_line_in_segment (((z + h).re : ℂ)) (b₁ := z.im) (b₂ := (z + h).im) (t := τ)
          (by simpa [Set.mem_uIcc] using hτ)
        simpa using this
      have hz_in := hw_mem'
      have hw_in := hzh_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simp only [γv, Metric.mem_closedBall, dist_zero_right] at hw'
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hmaps : Set.MapsTo γv (Set.uIcc z.im (z + h).im) (Metric.closedBall (0 : ℂ) R) := by
      intro τ hτ; have : γv τ ∈ Metric.closedBall (0 : ℂ) r1 := hseg_subset (Set.mem_image_of_mem _ hτ)
      exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) this
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
    have hcont_on : ContinuousOn (fun τ => f (γv τ)) (Set.uIcc z.im (z + h).im) := by
      simpa [Function.comp, γv] using
        (ContinuousOn.comp (hf_cont) (hγv_cont.continuousOn) hmaps)
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun τ => ‖f (γv τ) - f z‖) (Set.uIcc z.im (z + h).im) := by
      have h1 : ContinuousOn (fun τ => f (γv τ) - f z) (Set.uIcc z.im (z + h).im) := by
        exact hcont_on.sub continuousOn_const
      exact h1.norm
    have himage_compact : IsCompact ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      IsCompact.image_of_continuousOn hK hR_cont
    have hSV_eq : SV = (fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im := by
      ext r; constructor
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
    have : BddAbove ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      himage_compact.bddAbove
    simpa [hSV_eq] using this

  -- Pointwise bounds via membership in the sup-sets
  have hC_horiz : ∀ t ∈ Set.uIcc z.re (z + h).re,
      ‖(f (t + Complex.I * z.im) - f z)‖ ≤ S_horiz z h f := by
    intro t ht
    have hx : ‖f (t + Complex.I * z.im) - f z‖ ∈ SH := ⟨t, ht, rfl⟩
    -- S_horiz is the sSup of SH by definition
    have : S_horiz z h f = sSup SH := rfl
    simpa [this] using (le_csSup hbdd_SH hx)

  have hC_vert : ∀ τ ∈ Set.uIcc z.im (z + h).im,
      ‖(f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ S_vert z h f := by
    intro τ hτ
    have hx : ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖ ∈ SV := ⟨τ, hτ, rfl⟩
    have : S_vert z h f = sSup SV := rfl
    simpa [this] using (le_csSup hbdd_SV hx)

  -- Apply ML-type bounds on both integrals
  have hH : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            ≤ |(z + h).re - z.re| * S_horiz z h f := by
    -- Convert from uIcc to interval bounds
    have h_bound : ∀ t, t ∈ [[z.re, (z + h).re]] → ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht; exact hC_horiz t ht
    have h_int : ∀ t ∈ Ι z.re (z + h).re, ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht
      have ht_uIcc : t ∈ Set.uIcc z.re (z + h).re := by
        -- uIoc_subset_uIcc: Ι a b ⊆ uIcc a b
        exact Set.uIoc_subset_uIcc ht
      exact h_bound t ht_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    convert this using 1
    ring

  have hV : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
            ≤ |(z + h).im - z.im| * S_vert z h f := by
    have h_bound : ∀ τ, τ ∈ [[z.im, (z + h).im]] → ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ; exact hC_vert τ hτ
    have h_int : ∀ τ ∈ Ι z.im (z + h).im, ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ
      have hτ_uIcc : τ ∈ Set.uIcc z.im (z + h).im := by
        -- uIoc_subset_uIcc: Ι a b ⊆ uIcc a b
        exact Set.uIoc_subset_uIcc hτ
      exact h_bound τ hτ_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    rwa [mul_comm] at this

  -- Simplify the interval lengths
  have hre' : (z + h).re - z.re = h.re := by
    simp [Complex.add_re, add_comm, add_left_comm, add_assoc, add_sub_cancel]
  have him' : (z + h).im - z.im = h.im := by
    simp [Complex.add_im, add_comm, add_left_comm, add_assoc, add_sub_cancel]
  have hre : |(z + h).re - z.re| = |h.re| := by simp [hre']
  have him : |(z + h).im - z.im| = |h.im| := by simp [him']

  -- Compare with S_max
  have hH' : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
                ≤ |h.re| * S_max z h f := by
    have : S_horiz z h f ≤ S_max z h f := by exact le_max_left _ _
    -- First rewrite hH using hre
    have hH_rewritten : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖ ≤ |h.re| * S_horiz z h f := by
      rwa [hre] at hH
    -- Then apply the bound
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.re))
    exact le_trans hH_rewritten h_bound

  have hV' : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
                ≤ |h.im| * S_max z h f := by
    have : S_vert z h f ≤ S_max z h f := by exact le_max_right _ _
    -- First rewrite hV using him
    have hV_rewritten : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ |h.im| * S_vert z h f := by
      rwa [him] at hV
    -- Then apply the bound
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.im))
    exact le_trans hV_rewritten h_bound

  -- Final combination
  have :=
    calc
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
          ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ := hsplit
      _ = ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by simp [hvertnorm]
      _ ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := add_le_add hH' hV'

  simpa [Err] using this

lemma S_horiz_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_horiz z h f := by
  -- All elements of the set are norms, hence nonnegative
  unfold S_horiz
  apply Real.sSup_nonneg
  intro r hr; rcases hr with ⟨t, ht, rfl⟩; exact norm_nonneg _

lemma S_max_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_max z h f := by
  unfold S_max
  have h1 : 0 ≤ S_horiz z h f := S_horiz_nonneg z h f
  exact le_trans h1 (le_max_left _ _)

lemma bound_on_Err_ratio
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1)
    (hh : h ≠ 0) :
    ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤ 2 * S_max z h f := by
  -- Since norm z = ‖z‖, rewrite goal using norm
  -- change norm to norm
  have h_abs_eq : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ = ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ := rfl

  -- Start with the inequality from bound_on_Err (as mentioned in informal proof)
  have h1 := bound_on_Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
  -- Factor out S_max: |h.re| * S_max + |h.im| * S_max = (|h.re| + |h.im|) * S_max
  rw [← add_mul] at h1
  -- Now h1: ‖Err‖ ≤ (|h.re| + |h.im|) * S_max

  -- Since h ≠ 0, we have ‖h‖ > 0 (as mentioned in informal proof)
  have h_norm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh

  -- Divide the inequality by |h| (as mentioned in informal proof)
  have h2 : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖ / ‖h‖ ≤
            (|h.re| + |h.im|) * S_max z h f / ‖h‖ := by
    exact div_le_div_of_nonneg_right h1 (le_of_lt h_norm_pos)

  -- Use the property |A/B| = |A|/|B| (as mentioned in informal proof)
  -- The left side becomes ‖Err/h‖
  rw [← norm_div] at h2

  -- Rearrange the right side to get (|h.re| + |h.im|) / ‖h‖ * S_max
  -- We need: (a * b) / c = (a / c) * b
  have h2' : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤
             (|h.re| + |h.im|) / ‖h‖ * S_max z h f := by
    rw [← div_mul_eq_mul_div] at h2
    exact h2

  -- Use the bound |h.re| + |h.im| ≤ 2‖h‖ (as mentioned in informal proof)
  have h3 : |h.re| + |h.im| ≤ 2 * ‖h‖ := by
    -- "For any complex number h, |h.re| ≤ |h| and |h.im| ≤ |h|"
    calc |h.re| + |h.im|
      ≤ ‖h‖ + ‖h‖ := add_le_add (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
      _ = 2 * ‖h‖ := by ring

  -- Therefore (|h.re| + |h.im|) / ‖h‖ ≤ 2 (as mentioned in informal proof)
  have h4 : (|h.re| + |h.im|) / ‖h‖ ≤ 2 := by
    -- "This gives us a bound for the fraction: (|h.re| + |h.im|) / |h| ≤ 2|h| / |h| = 2"
    rw [div_le_iff₀ h_norm_pos]
    exact h3

  -- Final step: combine everything (as mentioned in informal proof)
  calc ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖
    ≤ (|h.re| + |h.im|) / ‖h‖ * S_max z h f := h2'
    _ ≤ 2 * S_max z h f := mul_le_mul_of_nonneg_right h4 (S_max_nonneg z h f)
open Filter Topology

lemma abs_horizontal_diff_eq_abs_real (z : ℂ) (t : ℝ) : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := by
  -- Show that the complex expression equals (t - z.re : ℂ)
  have h : (t : ℂ) + Complex.I * z.im - z = (t - z.re : ℂ) := by
    apply Complex.ext_iff.mpr
    constructor
    · -- Real part: t + 0 - z.re = t - z.re
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                 Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring
    · -- Imaginary part: 0 + z.im - z.im = 0
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
                 Complex.I_re, Complex.I_im, Complex.ofReal_re]
      ring

  -- Use the equality
  rw [h]
  -- Convert to the form that norm_real expects: ↑t - ↑z.re = ↑(t - z.re)
  rw [← Complex.ofReal_sub]
  -- Now apply: norm_real converts norm of real to real norm, real norm = abs
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma abs_sub_le_of_mem_uIcc (a b t : ℝ) (ht : t ∈ Set.uIcc a b) : |t - a| ≤ |b - a| ∧ |b - t| ≤ |b - a| := by
  -- Reduce to cases using uIcc and abs_sub_le_iff
  have h1 : a ≤ b ∨ b ≤ a := le_total a b
  rcases h1 with hle | hle
  · -- a ≤ b: uIcc a b = Icc a b
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : a ≤ t ∧ t ≤ b := by simpa using ht'
    constructor
    · have h_ta : |t - a| = t - a := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.left)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_right h_bounds.right a
    · have h_bt : |b - t| = b - t := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.right)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_left h_bounds.left b
  · -- b ≤ a: symmetric case
    have ht' : t ∈ Set.Icc b a := by
      rw [Set.uIcc_comm] at ht
      simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : b ≤ t ∧ t ≤ a := by simpa using ht'
    constructor
    · have h_ta : |t - a| = a - t := by simp [abs_of_nonpos (sub_nonpos.mpr h_bounds.right)]
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_left h_bounds.left a
    · have h_bt : |b - t| = t - b := by
        rw [abs_of_nonpos (sub_nonpos.mpr h_bounds.left)]
        ring
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_right h_bounds.right b

lemma abs_vertical_core (z h : ℂ) (τ : ℝ) : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| := by
  -- Use the triangle inequality for complex numbers: ‖z‖ ≤ |z.re| + |z.im|
  have h1 : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |((h.re : ℝ) + Complex.I * (τ - z.im)).re| + |((h.re : ℝ) + Complex.I * (τ - z.im)).im| := by
    apply Complex.norm_le_abs_re_add_abs_im

  -- Simplify the real and imaginary parts
  have h2 : ((h.re : ℝ) + Complex.I * (τ - z.im)).re = h.re := by simp
  have h3 : ((h.re : ℝ) + Complex.I * (τ - z.im)).im = τ - z.im := by simp

  rw [h2, h3] at h1
  exact h1

lemma mem_closedBall_mono_radius {z : ℂ} {r R : ℝ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) (h : r ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using le_trans (by simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz) h

lemma tendsto_of_nonneg_local_bound {g : ℂ → ℝ}
  (h_nonneg : ∀ h, 0 ≤ g h)
  (h_loc : ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ < δ → g h ≤ ε) :
  Tendsto g (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  -- Use ε/2 in the hypothesis to get strict inequality
  have hε_half : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ, hδ_pos, hδ⟩ := h_loc (ε / 2) hε_half
  use δ
  exact ⟨hδ_pos, fun h hh_dist => by
    rw [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (h_nonneg h)]
    have : g h ≤ ε / 2 := hδ h (by rwa [Complex.dist_eq, sub_zero] at hh_dist)
    linarith⟩

lemma sum_abs_le_two_mul {x y A : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ A) : |x| + |y| ≤ (2:ℝ) * A := by
  have := add_le_add hx hy
  simpa [two_mul] using this

lemma two_norm_lt_of_norm_lt_half {h : ℂ} {δ : ℝ} (_hpos : 0 < δ) (hbound : ‖h‖ < δ/2) : (2:ℝ) * ‖h‖ < δ := by
  have := mul_lt_mul_of_pos_left hbound (by norm_num : (0:ℝ) < 2)
  simpa [two_mul, add_halves] using this

lemma limit_of_S_is_zero
    {r1 R R0 : ℝ}
  (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) := by
  -- Use the continuity of f at z (which follows from analyticity)
  have f_cont_at_z : ContinuousAt f z := by
    -- z is in the closed ball r1 which is contained in closed ball R
    have hz_in_R : z ∈ Metric.closedBall (0 : ℂ) R :=
      mem_closedBall_mono_radius hz (le_of_lt hr1_lt_R)
    -- Analytic functions are continuous
    exact (hf z hz_in_R).continuousAt

  -- Apply tendsto_of_nonneg_local_bound
  apply tendsto_of_nonneg_local_bound
  · -- Show S_max z h f ≥ 0 for all h
    exact fun h => S_max_nonneg z h f
  · -- Show local bound: for ε > 0, ∃ δ > 0, ‖h‖ < δ → S_max z h f ≤ ε
    intro ε hε_pos
    -- Use continuity of f at z to get δ
    rw [Metric.continuousAt_iff] at f_cont_at_z
    obtain ⟨δ₁, hδ₁_pos, hf_bound⟩ := f_cont_at_z ε hε_pos

    -- Choose δ = δ₁ / 2 (to handle the factor of 2 in the vertical case)
    use δ₁ / 2
    constructor
    · exact half_pos hδ₁_pos
    · intro h hh_norm
      -- Need to show S_max z h f ≤ ε
      -- S_max = max of S_horiz and S_vert, so bound both
      unfold S_max
      apply max_le

      -- Bound S_horiz following the informal proof
      · unfold S_horiz
        -- Use Real.sSup_le to bound the supremum
        apply Real.sSup_le
        · -- Show all elements in the set are ≤ ε
          intro r hr
          obtain ⟨t, ht, rfl⟩ := hr
          -- Show norm (f(t + I*z.im) - f z) ≤ ε
          -- Key insight: show dist ((t : ℂ) + Complex.I * z.im) z < δ₁
          have key_dist : dist ((t : ℂ) + Complex.I * z.im) z < δ₁ := by
            -- Use the horizontal distance lemma and bound |t - z.re|
            rw [dist_eq]
            -- Since norm = ‖·‖, we can use the horizontal distance lemma
            have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := abs_horizontal_diff_eq_abs_real z t
            simp [eq_transform]
            -- Bound |t - z.re| by |(z+h).re - z.re| then by ‖h‖
            have t_bound : |t - z.re| ≤ |(z + h).re - z.re| := (abs_sub_le_of_mem_uIcc z.re (z + h).re t ht).1
            have re_diff_le : |(z + h).re - z.re| ≤ ‖h‖ := by
              -- (z+h).re - z.re = h.re
              simpa [Complex.add_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Complex.abs_re_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            calc |t - z.re|
              _ ≤ |(z + h).re - z.re| := t_bound
              _ ≤ ‖h‖ := re_diff_le
              _ < δ₁ / 2 := h_bound
              _ < δ₁ := by linarith
          -- Apply continuity to get the bound
          have f_dist := hf_bound key_dist
          -- Convert dist back to norm for the conclusion
          rw [dist_eq] at f_dist
          -- Already in norm form
          exact le_of_lt f_dist
        · -- Show 0 ≤ ε
          exact le_of_lt hε_pos

      -- Bound S_vert following the informal proof
      · unfold S_vert
        apply Real.sSup_le
        · -- Show all elements in the set are ≤ ε
          intro r hr
          obtain ⟨τ, hτ, rfl⟩ := hr
          -- Show norm (f((z+h).re + I*τ) - f z) ≤ ε
          have key_dist : dist (((z + h).re : ℂ) + Complex.I * τ) z < δ₁ := by
            rw [dist_eq]
            -- The key insight: ‖w_τ - z‖ ≤ |h.re| + |τ - z.im| ≤ |h.re| + |h.im| ≤ 2‖h‖
            -- First, express the difference in terms of h.re and (τ - z.im)
            have h_eq : (((z + h).re : ℂ) + Complex.I * τ - z) = (h.re : ℝ) + Complex.I * (τ - z.im) := by
              apply Complex.ext_iff.mpr
              constructor
              · simp [Complex.add_re, Complex.sub_re]
              · simp [Complex.add_im, Complex.sub_im]
            rw [h_eq]
            -- Bound |τ - z.im| by |(z+h).im - z.im| = |h.im|
            have τ_bound0 : |τ - z.im| ≤ |(z + h).im - z.im| := (abs_sub_le_of_mem_uIcc z.im (z + h).im τ hτ).1
            have im_diff_eq : |(z + h).im - z.im| = |h.im| := by
              simp [Complex.add_im, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            have τ_bound : |τ - z.im| ≤ |h.im| := by simpa [im_diff_eq] using τ_bound0
            -- Use the triangle inequality bound from the context
            have vertical_bound : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| :=
              abs_vertical_core z h τ
            have sum_bound : |h.re| + |τ - z.im| ≤ |h.re| + |h.im| := by
              gcongr
            have norm_bound := sum_abs_le_two_mul (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            have final_bound := two_norm_lt_of_norm_lt_half hδ₁_pos h_bound
            calc ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖
              _ ≤ |h.re| + |τ - z.im| := vertical_bound
              _ ≤ |h.re| + |h.im| := sum_bound
              _ ≤ (2 : ℝ) * ‖h‖ := norm_bound
              _ < δ₁ := final_bound
          -- Apply continuity to get the bound
          have f_dist := hf_bound key_dist
          rw [dist_eq] at f_dist
          -- Already in norm form
          exact le_of_lt f_dist
        · -- Show 0 ≤ ε
          exact le_of_lt hε_pos

lemma eventually_corner_and_sum_in_closedBall {z : ℂ} {R' : ℝ}
  (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    (z + h) ∈ Metric.closedBall (0 : ℂ) R' ∧
    (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) R' := by
  -- Let ρ = R' - ‖z‖ > 0
  have hρ_pos : 0 < R' - ‖z‖ := sub_pos.mpr hz
  have h_small : ∀ᶠ h in 𝓝 (0:ℂ), h ∈ Metric.ball (0 : ℂ) (R' - ‖z‖) :=
    Metric.ball_mem_nhds (0 : ℂ) hρ_pos
  refine h_small.mono ?_
  intro h hhball
  have hnorm_lt : ‖h‖ < R' - ‖z‖ := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hhball
  -- First membership: z + h ∈ closedBall 0 R'
  have hsum_lt : ‖z‖ + ‖h‖ < R' := by
    have htemp : ‖z‖ + ‖h‖ < ‖z‖ + (R' - ‖z‖) := by gcongr
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htemp
  have hzph_le : ‖z + h‖ ≤ R' :=
    le_of_lt (lt_of_le_of_lt (norm_add_le _ _) hsum_lt)
  have hzph_mem : (z + h) ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hzph_le
  -- Second membership: w ∈ closedBall 0 R' for w = ((z+h).re) + I z.im
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
  -- Triangle inequality relative to z: ‖w‖ ≤ ‖w - z‖ + ‖z‖
  have tri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    have := norm_add_le (w - z) z
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Compute and bound ‖w - z‖ ≤ ‖h‖ via horizontal distance
  let t : ℝ := (z + h).re
  have hwz_eq : w - z = (t : ℂ) + Complex.I * z.im - z := by
    simp [w, t, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| :=
    abs_horizontal_diff_eq_abs_real z t
  have t_sub_re : t - z.re = h.re := by
    simp [t, Complex.add_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hwz_abs2 : ‖w - z‖ = |h.re| := by
    simpa [hwz_eq, t_sub_re] using eq_transform
  have hwz_le : ‖w - z‖ ≤ ‖h‖ := by
    simpa [hwz_abs2] using (Complex.abs_re_le_norm h)
  have hw_le'' : ‖w‖ ≤ ‖h‖ + ‖z‖ := by
    exact le_trans tri (add_le_add_left hwz_le _)
  have hw_lt : ‖w‖ < R' := by
    have : ‖h‖ + ‖z‖ < R' := by simpa [add_comm] using hsum_lt
    exact lt_of_le_of_lt hw_le'' this
  have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [w, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using (le_of_lt hw_lt)
  exact And.intro hzph_mem hw_mem


lemma limit_of_Err_ratio_is_zero
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
  -- Define the target function g(h) = Err(z,h)/h
  set g : ℂ → ℂ := fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h
  -- S_max → 0 as h → 0 (given)
  have hS : Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) :=
    limit_of_S_is_zero (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz
  -- Hence |2 * S_max| → 0 by continuity
  have h_upper : Tendsto (fun h => |(2 : ℝ) * S_max z h f|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun x : ℝ => |(2 : ℝ) * x| :=
      (continuous_const.mul continuous_id).abs
    have h0 := hcont.tendsto (0 : ℝ)
    simpa [mul_zero, abs_zero] using h0.comp hS
  -- Lower bound: 0 ≤ ‖g h‖ holds everywhere
  have h_lower_nonneg : ∀ᶠ h in 𝓝 0, 0 ≤ ‖g h‖ :=
    Filter.Eventually.of_forall (fun _ => by simpa [g] using (norm_nonneg (g _)))
  -- Choose δ = (R - r1)/2 > 0 and set R' = r1 + δ so that r1 < R' < R
  let δ : ℝ := (R - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
    simpa [δ] using half_pos this
  let R' : ℝ := r1 + δ
  have hR'_pos : 0 < R' := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R'] using this
  have hR'_lt_R : R' < R := by
    have hδlt : δ < R - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R))
    have : r1 + δ < r1 + (R - r1) := by gcongr
    simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- z lies in the R'-closed ball
  have hz_le_r1 : ‖z‖ ≤ r1 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hr1_le_R' : r1 ≤ R' := by
      have : 0 ≤ δ := le_of_lt hδ_pos
      simpa [R'] using (le_add_of_nonneg_right this : r1 ≤ r1 + δ)
    have : ‖z‖ ≤ R' := le_trans hz_le_r1 hr1_le_R'
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
  -- Eventual upper bound: for small h, z + h ∈ closedBall 0 R', then apply bound_on_Err_ratio with R'
  have h_event : ∀ᶠ h in 𝓝 0, ‖g h‖ ≤ |(2 : ℝ) * S_max z h f| := by
    -- Use the event that ensures both z+h and the mixed corner lie in the smaller ball R'
    have hcorner := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') (hz := by
      -- from ‖z‖ ≤ r1 and r1 < R', we have ‖z‖ < R'
      have : ‖z‖ ≤ r1 := hz_le_r1
      exact lt_of_le_of_lt this (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos)))
    refine hcorner.mono ?_
    intro h hh
    have hzh' : z + h ∈ Metric.closedBall (0 : ℂ) R' := hh.1
    have hw' : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) R' := hh.2
    by_cases hh0 : h = 0
    · have : 0 ≤ |(2 : ℝ) * S_max z h f| := abs_nonneg _
      simp [g, hh0, div_zero, norm_zero]
    · -- apply the ratio bound with radius R'
      have hb :=
        bound_on_Err_ratio (r1:=R') (R:=R) (R0:=R0)
          hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (h:=h) hz' hzh' hw' hh0
      have hb' : ‖g h‖ ≤ 2 * S_max z h f := by
        simpa [g, norm, Err] using hb
      exact le_trans hb' (le_abs_self ((2 : ℝ) * S_max z h f))
  -- Apply squeeze theorem to the norm
  have h_norm_tendsto : Tendsto (fun h => ‖g h‖) (𝓝 0) (𝓝 0) := by
    refine Filter.Tendsto.squeeze' tendsto_const_nhds h_upper h_lower_nonneg h_event
  -- Convert from norm convergence to complex convergence
  have h_dist_tendsto : Tendsto (fun h => dist (g h) 0) (𝓝 0) (𝓝 0) := by
    simpa [dist_eq_norm] using h_norm_tendsto
  simpa [g] using (tendsto_iff_dist_tendsto_zero).2 h_dist_tendsto

open Classical
/-- Extend `If_taxicab` to a total function on `ℂ` by zero outside the closed ball. -/
noncomputable def If_ext
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) : ℂ → ℂ :=
  fun w =>
    if h : w ∈ Metric.closedBall (0 : ℂ) r1 then
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, h⟩
    else
      0

lemma If_ext_eq_taxicab_of_mem {r1 R R0 : ℝ} (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) r1) :
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
      = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
  classical
  simp [If_ext, hw]

lemma If_taxicab_param_invariance {r1₁ r1₂ R R0 : ℝ}
    (hr1₁_pos : 0 < r1₁) (hr1₁_lt_R : r1₁ < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (hr1₂_pos : 0 < r1₂) (hr1₂_lt_R : r1₂ < R)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ}
    (hw₁ : w ∈ Metric.closedBall (0 : ℂ) r1₁)
    (hw₂ : w ∈ Metric.closedBall (0 : ℂ) r1₂) :
    If_taxicab hr1₁_pos hr1₁_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₁⟩
    = If_taxicab hr1₂_pos hr1₂_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₂⟩ := by
  -- The definition of If_taxicab depends only on the underlying complex number w
  -- and not on the radius parameter; unfolding both sides gives identical expressions.
  simp [If_taxicab]


lemma eventually_decomposition_for_ext
  {R' R R0 : ℝ} (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  (z : ℂ) (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
    g (z + h) - g z = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
  -- Eventually, both z+h and the corner lie in the closed ball of radius R'.
  have h_event := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') hz
  refine h_event.mono ?_
  intro h hh
  -- Define g
  let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
  -- z is in the closed ball of radius R' since ‖z‖ < R'
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
  -- Rewrite g at the two points using the definition of If_ext on the ball
  have hgzh : g (z + h)
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z + h) hh.1
  have hgz : g z
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z) hz'
  -- Apply the decomposition lemma for If_taxicab on radius R'
  have H :=
    If_diff_decomposition_final (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one (f:=f) (hf:=hf)
      (z:=z) (h:=h)
      (hz:=hz') (hzh:=hh.1) (hw:=hh.2)
  -- Conclude by rewriting g using hgzh and hgz
  calc
    g (z + h) - g z
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩
          - If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
            simp [hgzh, hgz]
    _ = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
      simpa using H

lemma tendsto_Err_ratio_radius (R' R R0 : ℝ) (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z : ℂ} (hz : ‖z‖ < R') :
  Tendsto (fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
  -- From ‖z‖ < R', we have z ∈ closedBall 0 R'
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
  -- Apply the general limit lemma with radius R'
  simpa using
    (limit_of_Err_ratio_is_zero (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (hz:=hz'))

lemma hasDerivWithinAt_congr_eqOn {f g : ℂ → ℂ} {s : Set ℂ} {z f' : ℂ}
  (hEq : Set.EqOn f g s) (hz : z ∈ s) :
  HasDerivWithinAt g f' s z → HasDerivWithinAt f f' s z := by
  intro hg
  have hfg : ∀ x ∈ s, f x = g x := fun x hx => hEq hx
  simpa using (HasDerivWithinAt.congr_of_mem (h := hg) (hs := hfg) (hx := hz))

lemma differentiableOn_of_hasDerivWithinAt {f : ℂ → ℂ} {s : Set ℂ} {F : ℂ → ℂ}
  (h : ∀ z ∈ s, HasDerivWithinAt f (F z) s z) : DifferentiableOn ℂ f s := by
  intro z hz
  exact (h z hz).differentiableWithinAt

lemma If_ext_agree_on_smallBall {r1 R' R R0 : ℝ}
  (hr1_pos : 0 < r1) (hR'_pos : 0 < R') (hr1_lt_R : r1 < R) (hR'_lt_R : R' < R) (hr1_lt_R' : r1 < R') (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
  Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
           (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
           (Metric.closedBall (0 : ℂ) r1) := by
  intro w hw
  -- From hw : w ∈ closedBall 0 r1 and r1 < R', we also have w ∈ closedBall 0 R'
  have hw' : w ∈ Metric.closedBall (0 : ℂ) R' :=
    mem_closedBall_mono_radius (z:=w) (r:=r1) (R:=R') hw (le_of_lt hr1_lt_R')
  -- Rewrite both sides using the definition of If_ext on the ball
  have hleft :
      If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=r1) (R:=R) (R0:=R0)
        hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw)
  have hright :
      If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0)
        hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw')
  -- Use parameter invariance of If_taxicab
  have hparam :=
    If_taxicab_param_invariance (r1₁:=r1) (r1₂:=R') (R:=R) (R0:=R0)
      hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hR'_pos hR'_lt_R hf (w:=w) hw hw'
  -- Chain equalities
  calc
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := hleft
    _ = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := hparam
    _ = If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w := by
          simpa using hright.symm

lemma hasDerivAt_of_local_decomposition' (g : ℂ → ℂ) (z F : ℂ)
  (Err_func : ℂ → ℂ)
  (hdecomp : ∀ᶠ h in 𝓝 (0:ℂ), g (z + h) - g z = F * h + Err_func h)
  (hErr : Tendsto (fun h => Err_func h / h) (𝓝 (0:ℂ)) (𝓝 (0:ℂ))) :
  HasDerivAt g F z := by
  -- Restrict the decomposition to the punctured neighborhood
  have hdecomp_within : ∀ᶠ h in 𝓝[≠] (0:ℂ), g (z + h) - g z = F * h + Err_func h :=
    (hdecomp.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ)))
  -- On the punctured neighborhood, we also have eventually h ≠ 0
  have h_ne0 : ∀ᶠ h in 𝓝[≠] (0:ℂ), h ≠ 0 := by
    simpa [Set.mem_setOf_eq] using
      (self_mem_nhdsWithin : {h : ℂ | h ≠ 0} ∈ 𝓝[{h : ℂ | h ≠ 0}] (0:ℂ))
  -- On (nhds[≠] 0), the slope equals F + Err h / h
  have h_eq_slope : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      h⁻¹ • (g (z + h) - g z) = F + Err_func h / h := by
    refine (hdecomp_within.and h_ne0).mono ?_
    intro h hh
    rcases hh with ⟨hEq, hne⟩
    -- Start from the decomposition and divide by h
    have H0 : h⁻¹ • (g (z + h) - g z) = h⁻¹ • (F * h + Err_func h) := by
      simpa using congrArg (fun x => h⁻¹ • x) hEq
    -- Simplify the RHS algebraically
    have h1 : h⁻¹ * (F * h) = F := by
      have hne' : h ≠ 0 := hne
      calc
        h⁻¹ * (F * h) = F * (h⁻¹ * h) := by
          ac_rfl
        _ = F * 1 := by simp [hne']
        _ = F := by simp
    have h2 : h⁻¹ * Err_func h = Err_func h / h := by
      simp [div_eq_mul_inv, mul_comm]
    calc
      h⁻¹ • (g (z + h) - g z)
          = h⁻¹ • (F * h + Err_func h) := H0
      _ = h⁻¹ * (F * h + Err_func h) := by simp [smul_eq_mul]
      _ = h⁻¹ * (F * h) + h⁻¹ * (Err_func h) := by simp [mul_add]
      _ = F + Err_func h / h := by simp [h1, h2]
  -- Limit of the RHS: F + Err h / h → F
  have hErr_within : Tendsto (fun h => Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) :=
    hErr.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
  have h_const : Tendsto (fun _ : ℂ => F) (𝓝[≠] (0:ℂ)) (𝓝 F) := tendsto_const_nhds
  have h_sum : Tendsto (fun h => F + Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (F + 0)) :=
    h_const.add hErr_within
  have h_target : Tendsto (fun h => h⁻¹ • (g (z + h) - g z)) (𝓝[≠] (0:ℂ)) (𝓝 F) := by
    have := (Filter.tendsto_congr' h_eq_slope).2 h_sum
    simpa [zero_add] using this
  -- Conclude by the slope characterization of the derivative
  exact (hasDerivAt_iff_tendsto_slope_zero).2 h_target

lemma uniqueDiffWithinAt_convex_complex {s : Set ℂ} (hconv : Convex ℝ s)
    (hs : (interior s).Nonempty) {x : ℂ} (hx : x ∈ closure s) :
    UniqueDiffWithinAt ℂ s x := by
  -- Use the real-field result for the underlying real vector space
  have hR : UniqueDiffWithinAt ℝ s x :=
    uniqueDiffWithinAt_convex (E := ℂ) (conv := hconv) (hs := hs) (x := x) (hx := hx)
  -- Density for the real-span of the real tangent cone
  have dR : Dense ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ) := by
    simpa using (hR.dense_tangentConeAt)
  -- The real tangent cone is included in the complex tangent cone
  have h_tc_subset : tangentConeAt ℝ s x ⊆ tangentConeAt ℂ s x := by
    intro y hy
    rcases exists_fun_of_mem_tangentConeAt hy with ⟨_, l, _, c, d, hmem, hctend, hsmullim⟩
    refine mem_tangentConeAt_of_seq l (fun n => (c n : ℂ)) d hmem ?_ ?_
    · -- norms are preserved under coercion ℝ → ℂ
      simpa [Complex.norm_real] using hctend
    · -- scalar multiplications agree when viewing ℂ as an ℝ-module
      simpa [Complex.real_smul] using hsmullim
  -- Compare spans: the ℝ-span is included in the ℝ-restriction of the ℂ-span
  set TC : Set ℂ := tangentConeAt ℂ s x
  set Sℂ : Submodule ℂ ℂ := Submodule.span ℂ TC
  set Sℝ : Submodule ℝ ℂ := Sℂ.restrictScalars ℝ
  have h_span_le : (Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) ≤ Sℝ := by
    -- it suffices to show the generators are in Sℝ
    refine Submodule.span_le.mpr ?_
    intro v hv
    have hv' : v ∈ TC := h_tc_subset hv
    have : v ∈ Sℂ := Submodule.subset_span hv'
    simpa [Sℝ] using this
  -- From density of the smaller set, deduce density of the larger (as sets)
  have hsubset_sets :
      ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ)
        ⊆ ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := by
    intro z hz
    have hz' : z ∈ Sℝ := h_span_le hz
    simpa [Sℝ] using hz'
  have dC : Dense ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := dR.mono hsubset_sets
  -- Conclude the complex version
  exact ⟨dC, hx⟩

lemma interior_closedBall_nonempty_of_pos {R : ℝ} (hR_pos : 0 < R) :
    (interior (Metric.closedBall (0 : ℂ) R)).Nonempty := by
  -- 0 belongs to the open ball of radius R around 0 when R > 0
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hR_pos
  -- The open ball is contained in the interior of the closed ball
  have hsub : Metric.ball (0 : ℂ) R ⊆ interior (Metric.closedBall (0 : ℂ) R) :=
    Metric.ball_subset_interior_closedBall
  -- Hence the interior is nonempty
  exact ⟨0, hsub h0mem⟩

lemma mem_closure_of_mem_closedBall {R : ℝ} {z : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  z ∈ closure (Metric.closedBall (0 : ℂ) R) := by
  exact subset_closure hz

lemma uniqueDiffWithinAt_closedBall_complex_of_mem {R : ℝ} {z : ℂ}
  (hR_pos : 0 < R) (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) R) z :=
by
  -- The closed ball is convex
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) R) :=
    convex_closedBall (0 : ℂ) R
  -- Its interior is nonempty since R > 0
  have hnonempty : (interior (Metric.closedBall (0 : ℂ) R)).Nonempty :=
    interior_closedBall_nonempty_of_pos (R := R) hR_pos
  -- z belongs to the closure of the closed ball
  have hz_cl : z ∈ closure (Metric.closedBall (0 : ℂ) R) :=
    mem_closure_of_mem_closedBall (R := R) (z := z) hz
  -- Apply the general convex-set lemma over ℂ
  exact uniqueDiffWithinAt_convex_complex hconv hnonempty hz_cl

lemma If_is_differentiable_on
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    DifferentiableOn ℂ (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1)
    ∧
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      derivWithin (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1) z = f z := by
  set s : Set ℂ := Metric.closedBall (0 : ℂ) r1
  have hHasDerivWithinAt : ∀ z ∈ s,
      HasDerivWithinAt (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (f z) s z := by
    intro z hz
    -- Choose an intermediate radius R' with r1 < R' < R
    let δ : ℝ := (R - r1) / 2
    have hδ_pos : 0 < δ := by
      have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
      simpa [δ] using half_pos this
    let R' : ℝ := r1 + δ
    have hR'_pos : 0 < R' := by
      have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
      simpa [R'] using this
    have hR'_lt_R : R' < R := by
      have hδlt : δ < R - r1 := by
        have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
        simpa [δ] using (half_lt_self this)
      have : r1 + δ < r1 + (R - r1) := by gcongr
      simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hr1_lt_R' : r1 < R' := by
      have : r1 < r1 + δ := by simpa [add_comm, add_left_comm, add_assoc, R', δ] using (lt_of_le_of_lt (le_of_eq rfl) (add_lt_add_left hδ_pos r1))
      simpa [R'] using this
    -- z is strictly inside the R'-ball
    have hz_le_r1 : ‖z‖ ≤ r1 := by
      simpa [s, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
    have hz_lt_R' : ‖z‖ < R' := lt_of_le_of_lt hz_le_r1 (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos))
    -- Define g as the extension at radius R'
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
    -- Local decomposition for g around z
    have hdecomp := eventually_decomposition_for_ext (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf z hz_lt_R'
    -- Error ratio tends to zero
    have hErr := tendsto_Err_ratio_radius (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf hz_lt_R'
    -- Conclude derivative exists for g at z with derivative f z
    have hDerivAt_g : HasDerivAt g (f z) z :=
      hasDerivAt_of_local_decomposition' (g := g) (z := z) (F := f z)
        (Err_func := fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h)
        (hdecomp := by
          -- adjust the eventual decomposition to match hasDerivAt_of_local_decomposition'
          simpa [g] using hdecomp)
        (hErr := by
          -- convert real-valued limit to complex-valued (same statement)
          simpa using hErr)
    -- Turn into a within-derivative on s for g
    have hWithin_g : HasDerivWithinAt g (f z) s z := hDerivAt_g.hasDerivWithinAt
    -- Use equality of If_ext on s for radii r1 and R'
    have hEq : Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
                        (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
                        s :=
      If_ext_agree_on_smallBall (r1:=r1) (R':=R') (R:=R) (R0:=R0)
        hr1_pos hR'_pos hr1_lt_R hR'_lt_R hr1_lt_R' hR_lt_R0 hR0_lt_one hf
    -- Transfer the derivative along equality on s
    exact hasDerivWithinAt_congr_eqOn (f := If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
      (g := g) (s := s) (z := z) (f' := f z) hEq hz hWithin_g
  -- First goal: DifferentiableOn
  refine And.intro ?hdiff ?hderiv
  · -- differentiability on s from existence of derivative within at each point
    apply differentiableOn_of_hasDerivWithinAt
    intro z hz
    exact hHasDerivWithinAt z hz
  · -- compute the derivative within s
    intro z hz
    have hUD : UniqueDiffWithinAt ℂ s z :=
      uniqueDiffWithinAt_closedBall_complex_of_mem (R := r1) hr1_pos (z := z) (hz := by simpa [s] using hz)
    have hD := hHasDerivWithinAt z hz
    simpa using hD.derivWithin hUD


open scoped Topology

theorem AnalyticOnNhd.mono_closedBall {B : ℂ → ℂ} {R : ℝ} (R' : ℝ)
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall 0 R)) (hR' : R' < R) :
    AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
  -- The proof follows by applying `AnalyticOnNhd.mono` to the fact that the
  -- smaller ball is a subset of the larger one.
  exact hB.mono (Metric.closedBall_subset_closedBall (le_of_lt hR'))

/-- Lemma: There exists J analyticOnNhd with J(0) = 0 and J'(z) = B'(z)/B(z). -/
lemma I_is_antiderivative
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J : ℂ → ℂ, AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) ∧
      J 0 = 0 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z := by
  classical
  -- L := B'/B is analytic on closedBall R'
  have hB_on_R' : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.mono_closedBall R' hB hR'_lt_R
  have hderiv_on_R' : AnalyticOnNhd ℂ (deriv B) (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.deriv hB_on_R'
  let L : ℂ → ℂ := fun z => deriv B z / B z
  have hL_on_R' : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) R') := by
    simpa [L] using AnalyticOnNhd.div hderiv_on_R' hB_on_R' hB_ne_zero
  -- Choose R_mid with r1 < R_mid < R'
  let δ : ℝ := (R' - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R' - r1 := sub_pos.mpr hr1_lt_R'
    simpa [δ] using half_pos this
  let R_mid : ℝ := r1 + δ
  have hR_mid_pos : 0 < R_mid := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R_mid] using this
  have hr1_lt_R_mid : r1 < R_mid := by
    have : 0 < δ := hδ_pos
    simpa [R_mid] using (lt_add_of_pos_right r1 this)
  have hR_mid_lt_R' : R_mid < R' := by
    have hδlt : δ < R' - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R'))
    have : r1 + δ < r1 + (R' - r1) := by gcongr
    simpa [R_mid, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Define J as the primitive of L on radius R_mid with outer radius R'
  let J : ℂ → ℂ :=
    If_ext (r1 := R_mid) (R := R') (R0 := R) hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one L hL_on_R'
  -- If_is_differentiable_on gives differentiability on closedBall R_mid and
  -- the within-derivative there equals L
  have hIf :=
    (If_is_differentiable_on (r1 := R_mid) (R := R') (R0 := R)
      hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one (f := L) hL_on_R')
  have hDiffOn_mid : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) R_mid) := by
    simpa [J] using hIf.1
  -- Differentiable on the open ball R_mid by restriction
  have hDiffOn_ball_R_mid : DifferentiableOn ℂ J (Metric.ball (0 : ℂ) R_mid) :=
    hDiffOn_mid.mono Metric.ball_subset_closedBall
  -- 1) J is analytic on a neighborhood of every point of closedBall r1
  have hJ_analyticOnNhd : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) := by
    intro z hz
    -- z is strictly inside radius R_mid since ‖z‖ ≤ r1 < R_mid
    have hz_le : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
    -- Differentiability on the open ball of radius R_mid yields AnalyticAt at z
    exact (DifferentiableOn.analyticAt (s := Metric.ball (0 : ℂ) R_mid)
      (f := J) hDiffOn_ball_R_mid (Metric.isOpen_ball.mem_nhds hz_ball))
  -- 2) J(0) = 0
  have h0_in_mid : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R_mid := by
    simpa [Metric.mem_closedBall, dist_self] using (le_of_lt hR_mid_pos)
  have hJ0 : J 0 = 0 := by
    simp [J, If_ext, If_taxicab, h0_in_mid]
  -- 3) For each z in closedBall r1, deriv J z = L z = B'/B
  have hderiv_eq : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = L z := by
    intro z hz
    -- z is strictly inside radius R_mid
    have hz_le : dist z (0 : ℂ) ≤ r1 := by simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
    have hz_cb_mid : z ∈ Metric.closedBall (0 : ℂ) R_mid := Metric.ball_subset_closedBall hz_ball
    -- closedBall R_mid is a neighborhood of z since it contains an open ball around z
    have h_cb_nhds : Metric.closedBall (0 : ℂ) R_mid ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz_ball) Metric.ball_subset_closedBall
    -- We have: derivWithin J (closedBall R_mid) z = L z from If_is_differentiable_on
    have hDW_eq_L : derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z = L z := by
      simpa [J] using hIf.2 z hz_cb_mid
    -- From differentiability within on closedBall R_mid, get a HasDerivWithinAt with derivative L z
    have hHasWithin : HasDerivWithinAt J (derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z)
        (Metric.closedBall (0 : ℂ) R_mid) z :=
      (hDiffOn_mid z hz_cb_mid).hasDerivWithinAt
    have hHasWithinL : HasDerivWithinAt J (L z) (Metric.closedBall (0 : ℂ) R_mid) z := by
      simpa [hDW_eq_L]
        using hHasWithin
    -- Since closedBall R_mid is a neighborhood of z, upgrade to HasDerivAt
    have hHasDerivAt : HasDerivAt J (L z) z :=
      HasDerivWithinAt.hasDerivAt hHasWithinL h_cb_nhds
    -- Conclude the equality of derivatives
    simpa using hHasDerivAt.deriv
  -- Package the result
  refine ⟨J, hJ_analyticOnNhd, hJ0, ?_⟩
  intro z hz
  simpa [L] using hderiv_eq z hz

/-- Definition: H(z) := exp(J(z))/B(z) where J is from I_is_antiderivative. -/
noncomputable def H_auxiliary
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    (J : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (J z) / B z

/-- Lemma: H(0) = 1/B(0). -/
lemma H_at_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 1 / B 0 := by
  simp [H_auxiliary, hJ_zero]

/-- Lemma: J'(z)B(z) = B'(z). -/
lemma log_deriv_id
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z = deriv B z := by
  intro z hz
  -- z ∈ closedBall 0 r1 implies z ∈ closedBall 0 R
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR'_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR'_le
    simpa using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hJd := hJ_deriv z hz
  have hmult := congrArg (fun t => t * B z) hJd
  have hR2 : (deriv B z / B z) * B z = deriv B z * B z / B z := by
    simpa using (div_mul_eq_mul_div (deriv B z) (B z) (B z))
  have hmult' : deriv J z * B z = deriv B z * B z / B z := by
    simpa [hR2] using hmult
  have hdiv' : deriv B z * B z / B z = deriv B z := by
    field_simp [hBnz]
  calc
    deriv J z * B z = deriv B z * B z / B z := hmult'
    _ = deriv B z := by simpa using hdiv'

/-- Lemma: J'(z)B(z) - B'(z) = 0. -/
lemma log_deriv_identity
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z - deriv B z = 0 := by
  intro z hz
  have h_eq := log_deriv_id hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ_deriv z hz
  rw [h_eq]
  simp

/-- Lemma: Derivative of H(z) using quotient rule. -/
lemma H_derivative_quotient_rule
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv (fun w => Complex.exp (J w)) z * B z - deriv B z * Complex.exp (J z)) / (B z)^2 := by
  intro z hz
  -- z belongs to the larger closed ball
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa using hzR''
  -- differentiability and nonvanishing of denominator
  have hB_nz : B z ≠ 0 := hB_ne_zero z hzR
  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
    apply AnalyticOnNhd.mono_closedBall R' hB
    assumption
  have hB_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hF_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z := hJ_diff.cexp
  -- apply the quotient rule for derivatives
  have h := deriv_div (hc := hF_diff) (hd := hB_diff) (hx := hB_nz)
  simpa [H_auxiliary, mul_comm] using h

lemma exp_I_derivative_chain_rule
    {r1 : ℝ}
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (fun w => Complex.exp (J w)) z = deriv J z * Complex.exp (J z) := by
  intro z hz
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hJ_has : HasDerivAt J (deriv J z) z := hJ_diff.hasDerivAt
  have hcomp := (Complex.hasDerivAt_exp (J z)).comp z hJ_has
  -- extract the derivative
  simpa [mul_comm] using hcomp.deriv

lemma H_derivative_calc
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv J z * B z - deriv B z) * Complex.exp (J z) / (B z)^2 := by
  intro z hz
  -- Get the quotient rule result
  have hquot := H_derivative_quotient_rule hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ z hz
  -- Get the chain rule result for exp(J(z))
  have hchain := exp_I_derivative_chain_rule hJ z hz
  -- Substitute chain rule into quotient rule
  rw [hquot, hchain]
  -- Now we have: (deriv J z * Complex.exp (J z) * B z - deriv B z * Complex.exp (J z)) / (B z)^2
  -- Factor out Complex.exp (J z)
  have h1 : deriv J z * Complex.exp (J z) * B z - deriv B z * Complex.exp (J z) =
           Complex.exp (J z) * (deriv J z * B z - deriv B z) := by ring
  rw [h1]
  -- Rearrange: Complex.exp (J z) * (deriv J z * B z - deriv B z) / (B z)^2 =
  --           (deriv J z * B z - deriv B z) * Complex.exp (J z) / (B z)^2
  ring

lemma H_derivative_is_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  intro z hz
  have hcalc :=
    H_derivative_calc hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ z hz
  have hident :=
    log_deriv_identity hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ_deriv z hz
  simpa [hident] using hcalc

lemma zero_mem_closedBall_zero_radius {r1 : ℝ} (hr1 : 0 ≤ r1) : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using hr1

lemma H_deriv_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  simpa using
    (H_derivative_is_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_deriv)

lemma H_auxiliary_differentiableOn_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
by
  -- closedBall r1 is a subset of closedBall R
  have hsubset : Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    have hz' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hle : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    have : dist z (0 : ℂ) ≤ R := le_trans hz' hle
    simpa [Metric.mem_closedBall] using this
  -- differentiability of J and B on the closed ball
  have hJ_diff : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) r1) :=
    hJ.differentiableOn
  have hB_diff_r1 : DifferentiableOn ℂ B (Metric.closedBall (0 : ℂ) r1) :=
    (hB.differentiableOn).mono hsubset
  -- differentiability of exp on ℂ and composition with J
  have hExp_diff : DifferentiableOn ℂ Complex.exp (Set.univ : Set ℂ) :=
    (Complex.differentiable_exp.differentiableOn)
  have hExp_comp : DifferentiableOn ℂ (fun z => Complex.exp (J z)) (Metric.closedBall (0 : ℂ) r1) := by
    refine hExp_diff.comp hJ_diff ?_
    intro x hx; simp
  -- B is nonvanishing on the smaller closed ball
  have hB_ne_zero_r1 : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z ≠ 0 := by
    intro z hz; exact hB_ne_zero z (by
    have x : Metric.closedBall 0 r1 ⊆ Metric.closedBall 0 R' := Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R')
    simp [x]
    simp at hz
    linarith
    )
  -- quotient rule for differentiability on sets
  have hdiv : DifferentiableOn ℂ (fun z => Complex.exp (J z) / B z)
      (Metric.closedBall (0 : ℂ) r1) :=
    hExp_comp.div hB_diff_r1 hB_ne_zero_r1
  -- unfold definition of H_auxiliary
  simpa [H_auxiliary] using hdiv

lemma hasDerivAt_H_auxiliary_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0 z := by
  intro z hz
  -- z ∈ closedBall r1 implies z ∈ closedBall R
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa [Metric.mem_closedBall] using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z (hzR)
  -- Differentiability at z of exp ∘ J and of B
  have hJ_anal : AnalyticAt ℂ J z := hJ z hz
  have hExp_diff_at_Jz : DifferentiableAt ℂ Complex.exp (J z) :=
    Complex.differentiableAt_exp
  have hc_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z :=
    hExp_diff_at_Jz.comp z hJ_anal.differentiableAt

  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') := by
    apply AnalyticOnNhd.mono_closedBall R' hB
    assumption
  have hd_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
  -- DifferentiableAt for H and then HasDerivAt with deriv coefficient
  have hH_diff : DifferentiableAt ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z := by
    simpa [H_auxiliary] using hc_diff.div hd_diff hBnz
  have hH_has : HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z) z :=
    hH_diff.hasDerivAt
  have hderiv0 : deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 :=
    H_deriv_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_deriv z hz
  simpa [hderiv0] using hH_has

lemma fderivWithin_eq_zero_of_derivWithin_eq_zero {s : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (hderiv : derivWithin f s x = 0) :
    fderivWithin ℂ f s x = 0 := by
  -- Relate fderivWithin and derivWithin in the scalar case
  have h₁ : fderivWithin ℂ f s x =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (derivWithin f s x) := by
    simpa using
      (toSpanSingleton_derivWithin (𝕜 := ℂ) (f := f) (s := s) (x := x)).symm
  have h₂ : fderivWithin ℂ f s x =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (0 : ℂ) := by
    simpa [hderiv] using h₁
  have hsmul0 : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (0 : ℂ) = 0 := by
    ext; simp [ContinuousLinearMap.smulRight_apply]
  exact h₂.trans hsmul0

lemma hasDerivWithinAt_of_hasDerivAt {f : ℂ → ℂ} {s : Set ℂ} {x : ℂ}
    (h : HasDerivAt f 0 x) : HasDerivWithinAt f 0 s x := by
  simpa using h.hasDerivWithinAt

lemma H_auxiliary_fderivWithin_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 :=
by
  intro z hz
  -- classical derivative at z is zero, hence within derivative exists with value 0
  have hHasAt :=
    hasDerivAt_H_auxiliary_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero
      hJ hJ_deriv z hz
  have hHasWithin :
      HasDerivWithinAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0
        (Metric.closedBall (0 : ℂ) r1) z :=
    hasDerivWithinAt_of_hasDerivAt hHasAt
  -- obtain differentiability within at z
  have hdiff : DifferentiableWithinAt ℂ
      (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) z :=
    hHasWithin.differentiableWithinAt
  -- compute the scalar derivative within equals 0 (with/without uniqueness)
  classical
  have hderivWithin0 :
      derivWithin (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 := by
    by_cases hUDc : UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) r1) z
    · simpa using hHasWithin.derivWithin hUDc
    · simpa using
        (derivWithin_zero_of_not_uniqueDiffWithinAt
          (𝕜 := ℂ)
          (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (s := Metric.closedBall (0 : ℂ) r1) (x := z) hUDc)
  -- conclude on the Fréchet derivative within
  exact fderivWithin_eq_zero_of_derivWithin_eq_zero hderivWithin0

/-- Lemma: H is constant on the closed ball. -/
lemma H_is_constant
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z =
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 := by
  intro z hz
  -- The closed ball is convex
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) r1) := by
    simpa using (convex_closedBall (0 : ℂ) r1)
  -- Differentiability of H on the closed ball
  have hdiff : DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
    H_auxiliary_differentiableOn_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ
  -- fderivWithin is zero on the closed ball
  have hfderiv0 : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) x = 0 :=
    H_auxiliary_fderivWithin_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_deriv
  -- 0 belongs to the closed ball
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 :=
    zero_mem_closedBall_zero_radius (le_of_lt hr1_pos)
  -- Apply mean value inequality with C = 0
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      ‖fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (Metric.closedBall (0 : ℂ) r1) x‖ ≤ 0 := by
    intro x hx
    simp [hfderiv0 x hx]
  have hineq :=
    Convex.norm_image_sub_le_of_norm_fderivWithin_le (𝕜 := ℂ)
      (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (s := Metric.closedBall (0 : ℂ) r1) (x := (0 : ℂ)) (y := z)
      hdiff hbound hs h0mem hz
  have hzero : H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z -
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 0 := by
    have : ‖H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z -
        H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0‖ ≤ 0 := by
      simpa using hineq
    simpa [norm_le_zero_iff] using this
  simpa [sub_eq_add_neg] using sub_eq_zero.mp hzero

lemma H_is_one
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z = 1 / B 0 := by
  intro z hz
  have hconst := H_is_constant hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_deriv z hz
  have h0 := H_at_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
  simpa [h0] using hconst

/-- Lemma: B(z) = B(0) * exp(J(z)). -/
lemma analytic_log_exists
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z = B 0 * Complex.exp (J z) := by
  intro z hz
  -- Use H_is_one to get that H(z) = 1 / B(0)
  have hH_const := H_is_one hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- Unfold the definition of H_auxiliary
  unfold H_auxiliary at hH_const
  -- Now we have: exp(J z) / B z = 1 / B 0
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    exact le_trans hzR' (by linarith)
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hR_pos : 0 < R := lt_trans (lt_trans hr1_pos hr1_lt_R') hR'_lt_R
  have hB0nz : B 0 ≠ 0 := hB_ne_zero 0 (by
    simp [Metric.closedBall, dist_zero_right]
    exact le_of_lt (by linarith))
  -- From exp(J z) / B z = 1 / B 0, cross multiply
  have heq : Complex.exp (J z) * B 0 = B z := by
    field_simp [hBnz, hB0nz] at hH_const
    exact hH_const
  -- Use commutativity to get the desired form
  rw [← heq, mul_comm]

/-- Lemma: |B(z)| = |B(0)| * |exp(J(z))|. -/
lemma modulus_of_B_product_form
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * norm (Complex.exp (J z)) := by
  intro z hz
  have hBform := analytic_log_exists hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- B z = B 0 * exp (J z)
  simpa [norm_mul] using (congrArg norm hBform)

/-- Lemma: |B(z)| = |B(0)| * exp(Re(J(z))). -/
lemma modulus_of_exp_log
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * Real.exp (Complex.re (J z)) := by
  intro z hz
  rw [modulus_of_B_product_form hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]
  rw [Complex.norm_exp]

/-- Lemma: log|B(z)| = log|B(0)| + log(exp(Re(J(z)))). -/
lemma log_modulus_as_sum
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) =
      Real.log (norm (B 0)) + Real.log (Real.exp (Complex.re (J z))) := by
  intro z hz
  -- Get the equation |B(z)| = |B(0)| * exp(Re(J(z)))
  have h_eq := modulus_of_exp_log hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- Apply logarithm and use log(a * b) = log(a) + log(b)
  rw [h_eq, Real.log_mul]
  · -- Show norm (B 0) ≠ 0
    -- Since norm z = ‖z‖, we need ‖B 0‖ ≠ 0, which is equivalent to B 0 ≠ 0
    simp [norm_ne_zero_iff]
    apply hB_ne_zero
    -- Show 0 ∈ Metric.closedBall (0 : ℂ) R
    rw [Metric.mem_closedBall, dist_self]
    linarith
  · -- Show Real.exp (Complex.re (J z)) ≠ 0
    exact Real.exp_ne_zero _

/-- Lemma: log|B(z)| - log|B(0)| = Re(J(z)). -/
lemma real_log_of_modulus_difference
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J z) := by
  intro z hz
  -- Use the lemma log_modulus_as_sum
  have h_sum := log_modulus_as_sum hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- Rearrange to get the difference
  rw [h_sum]
  -- Simplify Real.log (Real.exp (Complex.re (J z))) = Complex.re (J z)
  rw [Real.log_exp]
  ring

theorem log_of_analytic
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.closedBall (0 : ℂ) r1) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  have hB_ne_zero_R' : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0 := hB_ne_zero
  obtain ⟨J_B, hJ, hJ0, hJderiv⟩ :=
    I_is_antiderivative hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero_R'
  refine ⟨J_B, hJ, hJ0, hJderiv, ?_⟩
  intro z hz
  simpa using
    (real_log_of_modulus_difference hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ0 hJderiv z hz)
