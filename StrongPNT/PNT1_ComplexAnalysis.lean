import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
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

lemma lem_notinDR (R : ℝ) (w : ℂ) (hw : w ∉ ballDR R) : norm w ≥ R := by
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

lemma lem_circleDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : w ∈ closure (ballDR R)) (hw2 : w ∉ ballDR R) : norm w = R := by
  have h1 : norm w ≤ R := lem_inDR R hR w hw1
  have h2 : norm w ≥ R := lem_notinDR R w hw2
  linarith

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

lemma lem_AnalCont {R : ℝ} (H : ℂ → ℂ) (h_analytic : AnalyticOn ℂ H (closure (ballDR R))) :
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
    lem_AnalCont h h_analytic
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

lemma lem_MaxModP (R : ℝ) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) := by
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
    lem_MaxModP R h h_analytic w hw_in_DR hw_max
  -- Show that R (as complex number) is in the closure
  have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
  -- Apply the constant property at z = R
  exact h_const (R : ℂ) hR_in_closure

lemma lem_MaxModRR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) :
∀ z ∈ closure (ballDR R), norm (h R) ≥ norm (h z) := by
  intro z hz
  -- Apply lem_MaxModP to get |h(z)| = |h(w)| for all z ∈ closure (ballDR R)
  have h1 := lem_MaxModP R h h_analytic w hw_in_DR hw_max z hz
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

lemma lem_MaxModv4 (R B : ℝ) (hR : R > 0)
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

lemma lem_HardMMP (R B : ℝ) (hR : R > 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B := by
  intro w hw
  -- Apply lem_MaxModv4 to get a point v with |v| = R where |h(v)| is maximal and |h(v)| ≤ B
  obtain ⟨v, hv_abs, hv_max, hv_bound⟩ := lem_MaxModv4 R B hR h h_analytic h_boundary_bound
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
    (r : ℝ) (hr_lt_R : r < R)
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
    exact lem_BCI R M hR hM f h_analytic h_zero h_re_bound r hr_lt_R z hz_bound
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
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi * I)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(I * r_int * Complex.exp (I * t) * ((r_int * Complex.exp (I * t)) - z)⁻¹ ^ 2) * f (r_int * Complex.exp (I * t))) := by
  -- Apply cauchy_formula_deriv to get the circle integral form
  rw [cauchy_formula_deriv hf_domain h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

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
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
  -- Apply lem_CIF_deriv_param
  rw [lem_CIF_deriv_param hf_domain h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

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
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) = norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
  -- Apply the simplified Cauchy integral formula for derivatives
  rw [lem_CIF_deriv_simplified hf_domain h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

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

lemma abs_integral_le_integral_abs {a b : ℝ} {g : ℝ → ℂ}  : norm (∫ (t : ℝ) in Set.Icc a b, g t) ≤ ∫ (t : ℝ) in Set.Icc a b, norm (g t) := by
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
    exact abs_integral_le_integral_abs
  · exact le_of_lt one_div_two_pi_pos

lemma lem_modulus_of_f_prime {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
  -- Apply lem_modulus_of_f_prime0 to get the equality form
  rw [lem_modulus_of_f_prime0 hf_domain h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
  -- Apply lem_integral_modulus_inequality to get the desired inequality
  exact lem_integral_modulus_inequality

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

lemma lem_modulus_of_integrand_product3 {f : ℂ → ℂ} {r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int) :
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) = r_int * norm (f (r_int * Complex.exp (I * t))) := by
  rw [norm_mul]
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

lemma lem_reverse_triangle3 {r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int) :
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

lemma lem_zrr1 {r_z r_int : ℝ}
    (h_r_z_lt_r_int : r_z < r_int)
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

lemma lem_zrr2 {r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
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
  have h3 := @lem_reverse_triangle3 r_z r_int t z h_r_z_pos h_r_z_lt_r_int
  -- Combine using transitivity
  exact le_trans h2 h3

lemma lem_zrr3 {r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2 := by
  -- Use lem_zrr2 to get the inequality without squares
  have h_ineq := @lem_zrr2 r_z r_int t z h_r_z_pos h_r_z_lt_r_int hz
  -- Show both sides are nonnegative
  have h_nonneg_left : 0 ≤ r_int - r_z := by linarith [h_r_z_lt_r_int]
  have h_nonneg_right : 0 ≤ norm (r_int * Complex.exp (I * t) - z) := norm_nonneg _
  -- Apply mul_self_le_mul_self to square both sides
  have h_sq := mul_self_le_mul_self h_nonneg_left h_ineq
  -- Convert from a * a to a ^ 2
  rw [pow_two, pow_two]
  exact h_sq

lemma lem_reverse_triangle4 {r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (hz : z ∈ Metric.closedBall 0 r_z) :
0 < norm (r_int * Complex.exp (I * t) - z) := by
  -- Apply lem_zrr1 to get 0 < r_int - norm z
  have h1 := lem_zrr1 h_r_z_lt_r_int hz
  -- Apply lem_reverse_triangle3 to get r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z)
  have h2 := @lem_reverse_triangle3 r_z r_int t z h_r_z_pos h_r_z_lt_r_int
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

lemma lem_reverse_triangle5 {r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
r_int * Complex.exp (I * t) - z ≠ 0 := by
  -- Apply lem_reverse_triangle4 to get 0 < norm (r_int * Complex.exp (I * t) - z)
  have h_pos := @lem_reverse_triangle4 r_z r_int t z h_r_z_pos h_r_z_lt_r_int hz
  -- Apply lem_wposneq0 to conclude the complex number is not zero
  exact lem_wposneq0 (r_int * Complex.exp (I * t) - z) h_pos

lemma lem_reverse_triangle6 {r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
  -- Apply lem_reverse_triangle5 as suggested in the informal proof
  have h_ne_zero := lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int hz
  -- Apply pow_ne_zero (which is the Mathlib version of mul_self_ne_zero for powers)
  exact pow_ne_zero 2 h_ne_zero

lemma lem_modulus_of_integrand_product {f : ℂ → ℂ} {r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
  -- First show that the denominator is nonzero
  have h_neq_zero : r_int * Complex.exp (I * t) - z ≠ 0 :=
    lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int hz
  -- Then show that the square is nonzero
  have h_sq_neq_zero : (r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_self_ne_zero.mpr h_neq_zero
  rw [norm_div]
  -- Use lem_modulus_wz to handle the square of absolute value
  rw [lem_modulus_wz]

lemma lem_modulus_of_product {f : ℂ → ℂ} {r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
(r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
  -- First apply lem_modulus_of_integrand_product to split the absolute value of the quotient
  rw [lem_modulus_of_integrand_product t h_r_z_pos h_r_z_lt_r_int hz]
  -- Then apply lem_modulus_of_integrand_product3 to simplify the numerator
  rw [lem_modulus_of_integrand_product3 t h_r_z_pos h_r_z_lt_r_int]

lemma lem_modulus_of_product4 {f : ℂ → ℂ} {r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤
(r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2) := by
  -- First rewrite using lem_modulus_of_product
  rw [lem_modulus_of_product t h_r_z_pos h_r_z_lt_r_int hz]
  -- Now we have: (r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2
  -- We need to show this ≤ (r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2)

  -- Use lem_zrr3 to get the key inequality: (r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2
  have h_ineq := @lem_zrr3 r_z r_int t z h_r_z_pos h_r_z_lt_r_int hz

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
        r_int  hr_int_lt_R_analytic w
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
  have h1 := lem_modulus_of_product4 t h_r_z_pos h_r_z_lt_r_int hz (f := f)
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
∫ t in a..b, g t ≤ ∫ _ in a..b, C := by
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
∫ t in Set.Icc a b, g t ≤ ∫ _ in Set.Icc a b, C := by
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
    exact lem_reverse_triangle6 t h_r_z_pos h_r_z_lt_r_int hz

lemma integral_const_over_interval (C : ℝ) :
∫ _ in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
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
  have h1 := lem_modulus_of_f_prime hf_domain h_r_z_lt_r_int h_r_int_lt_R_analytic hz

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

lemma lem_r_prime_is_intermediate {r R : ℝ}
    (h_r_lt_R : r < R) :
r < (r + R) / 2 ∧ (r + R) / 2 < R := by
  constructor <;> linarith

lemma lem_calc_R_minus_r_prime {r R : ℝ} :
R - ((r + R) / 2) = (R - r) / 2 := by
  field_simp
  ring

lemma lem_calc_denominator_specific {r R : ℝ} :
(R - ((r + R) / 2)) * (((r + R) / 2) - r) ^ 2 = ((R - r) ^ 3) / 8 := by
  -- Use lem_calc_R_minus_r_prime to rewrite the first term
  rw [lem_calc_R_minus_r_prime]
  -- Show that ((r + R) / 2) - r = (R - r) / 2
  have h_calc : ((r + R) / 2) - r = (R - r) / 2 := by
    field_simp
    ring
  -- Rewrite using this identity
  rw [h_calc]
  -- Now we have (R - r) / 2 * ((R - r) / 2) ^ 2 = ((R - r) ^ 3) / 8
  -- Simplify: (R - r) / 2 * (R - r)^2 / 4 = (R - r)^3 / 8
  ring

lemma lem_calc_numerator_specific {M r R : ℝ} :
2 * (((r + R) / 2) ^ 2) * M = ((R + r) ^ 2 * M) / 2 := by
  -- Use ring to handle the algebraic manipulation
  ring

lemma lem_frac_simplify {M r R : ℝ} :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (((R + r) ^ 2 * M) / 2) / (((R - r) ^ 3) / 8) := by
  -- Unfold the definition of r_prime
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- Apply the numerator lemma
  have h_num := lem_calc_numerator_specific (r := r) (R := R) (M := M)
  -- Apply the denominator lemma
  have h_denom := lem_calc_denominator_specific (r := r) (R := R)
  -- Rewrite using both lemmas
  rw [← h_num, ← h_denom]

lemma lem_frac_simplify2 {M r R : ℝ}
    (hM_pos : 0 < M)
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
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
  -- Unfold the let definition
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- Apply lem_frac_simplify to get the intermediate form
  have h1 := lem_frac_simplify (r := r) (R := R) (M := M)
  -- Apply lem_frac_simplify2 to complete the transformation
  have h2 := lem_frac_simplify2 hM_pos hr_lt_R
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

lemma lem_2R_sq_is_4R_sq {R : ℝ}  : (2 * R) ^ 2 = 4 * R ^ 2 := by
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
  have h4 := lem_2R_sq_is_4R_sq (R := R)
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
  have h1 := lem_frac_simplify3 hM_pos hr_lt_R
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
  have h_intermediate := lem_r_prime_is_intermediate hr_lt_R
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

open Filter Topology


open Classical

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
    (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
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
  obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball <| hL_on_R'.mono Metric.ball_subset_closedBall|>.differentiableOn
  refine ⟨(fun z ↦ J z - J 0), ?_, (by simp), ?_⟩
  · apply AnalyticOnNhd.sub _ analyticOnNhd_const
    refine AnalyticOnNhd.mono ?_ <| Metric.closedBall_subset_ball hr1_lt_R'
    exact DifferentiableOn.analyticOnNhd (fun z hz ↦ DifferentiableAt.differentiableWithinAt (hJ z hz |>.differentiableAt)) Metric.isOpen_ball
  · intro z hz
    rw [deriv_sub_const]
    refine hJ z ?_|>.deriv
    exact Set.mem_of_subset_of_mem (Metric.closedBall_subset_ball hr1_lt_R') hz

/-- Definition: H(z) := exp(J(z))/B(z) where J is from I_is_antiderivative. -/
noncomputable def H_auxiliary
    (B : ℂ → ℂ)
    (J : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (J z) / B z

/-- Lemma: H(0) = 1/B(0). -/
lemma H_at_zero
    {B : ℂ → ℂ}
    {J : ℂ → ℂ}
    (hJ_zero : J 0 = 0) :
    H_auxiliary B J 0 = 1 / B 0 := by
  simp [H_auxiliary, hJ_zero]

/-- Lemma: J'(z)B(z) = B'(z). -/
lemma log_deriv_id
    {r1 R' : ℝ}
    (hr1_lt_R' : r1 < R')
    {B : ℂ → ℂ}
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
    {r1 R' : ℝ}
    (hr1_lt_R' : r1 < R')
    {B : ℂ → ℂ}
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z - deriv B z = 0 := by
  intro z hz
  have h_eq := log_deriv_id hr1_lt_R' hB_ne_zero hJ_deriv z hz
  rw [h_eq]
  simp

/-- Lemma: Derivative of H(z) using quotient rule. -/
lemma H_derivative_quotient_rule
    {r1 R' R : ℝ}
    (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary B J) z =
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
    (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary B J) z =
      (deriv J z * B z - deriv B z) * Complex.exp (J z) / (B z)^2 := by
  intro z hz
  -- Get the quotient rule result
  have hquot := H_derivative_quotient_rule hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ z hz
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
    (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary B J) z = 0 := by
  intro z hz
  have hcalc :=
    H_derivative_calc hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ z hz
  have hident :=
    log_deriv_identity hr1_lt_R' hB_ne_zero hJ_deriv z hz
  simpa [hident] using hcalc

lemma zero_mem_closedBall_zero_radius {r1 : ℝ} (hr1 : 0 ≤ r1) : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using hr1

lemma H_deriv_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary B J) z = 0 := by
  simpa using
    (H_derivative_is_zero hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_deriv)

lemma H_auxiliary_differentiableOn_closedBall
    {r1 R' R : ℝ}
    (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    DifferentiableOn ℂ (H_auxiliary B J)
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
    (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      HasDerivAt (H_auxiliary B J) 0 z := by
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
  have hH_diff : DifferentiableAt ℂ (H_auxiliary B J) z := by
    simpa [H_auxiliary] using hc_diff.div hd_diff hBnz
  have hH_has : HasDerivAt (H_auxiliary B J)
      (deriv (H_auxiliary B J) z) z :=
    hH_diff.hasDerivAt
  have hderiv0 : deriv (H_auxiliary B J) z = 0 :=
    H_deriv_zero_on_closedBall hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_deriv z hz
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
    (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary B J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 :=
by
  intro z hz
  -- classical derivative at z is zero, hence within derivative exists with value 0
  have hHasAt :=
    hasDerivAt_H_auxiliary_zero_on_closedBall hr1_lt_R' hR'_lt_R hB hB_ne_zero
      hJ hJ_deriv z hz
  have hHasWithin :
      HasDerivWithinAt (H_auxiliary B J) 0
        (Metric.closedBall (0 : ℂ) r1) z :=
    hasDerivWithinAt_of_hasDerivAt hHasAt
  -- obtain differentiability within at z
  have hdiff : DifferentiableWithinAt ℂ
      (H_auxiliary B J)
      (Metric.closedBall (0 : ℂ) r1) z :=
    hHasWithin.differentiableWithinAt
  -- compute the scalar derivative within equals 0 (with/without uniqueness)
  classical
  have hderivWithin0 :
      derivWithin (H_auxiliary B J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 := by
    by_cases hUDc : UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) r1) z
    · simpa using hHasWithin.derivWithin hUDc
    · simpa using
        (derivWithin_zero_of_not_uniqueDiffWithinAt
          (𝕜 := ℂ)
          (f := H_auxiliary B J)
          (s := Metric.closedBall (0 : ℂ) r1) (x := z) hUDc)
  -- conclude on the Fréchet derivative within
  exact fderivWithin_eq_zero_of_derivWithin_eq_zero hderivWithin0

/-- Lemma: H is constant on the closed ball. -/
lemma H_is_constant
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary B J z =
      H_auxiliary B J 0 := by
  intro z hz
  -- The closed ball is convex
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) r1) := by
    simpa using (convex_closedBall (0 : ℂ) r1)
  -- Differentiability of H on the closed ball
  have hdiff : DifferentiableOn ℂ (H_auxiliary B J)
      (Metric.closedBall (0 : ℂ) r1) :=
    H_auxiliary_differentiableOn_closedBall hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ
  -- fderivWithin is zero on the closed ball
  have hfderiv0 : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary B J)
        (Metric.closedBall (0 : ℂ) r1) x = 0 :=
    H_auxiliary_fderivWithin_zero_on_closedBall hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_deriv
  -- 0 belongs to the closed ball
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r1 :=
    zero_mem_closedBall_zero_radius (le_of_lt hr1_pos)
  -- Apply mean value inequality with C = 0
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      ‖fderivWithin ℂ (H_auxiliary B J)
          (Metric.closedBall (0 : ℂ) r1) x‖ ≤ 0 := by
    intro x hx
    simp [hfderiv0 x hx]
  have hineq :=
    Convex.norm_image_sub_le_of_norm_fderivWithin_le (𝕜 := ℂ)
      (f := H_auxiliary B J)
      (s := Metric.closedBall (0 : ℂ) r1) (x := (0 : ℂ)) (y := z)
      hdiff hbound hs h0mem hz
  have hzero : H_auxiliary B J z -
      H_auxiliary B J 0 = 0 := by
    have : ‖H_auxiliary B J z -
        H_auxiliary B J 0‖ ≤ 0 := by
      simpa using hineq
    simpa [norm_le_zero_iff] using this
  simpa [sub_eq_add_neg] using sub_eq_zero.mp hzero

lemma H_is_one
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary B J z = 1 / B 0 := by
  intro z hz
  have hconst := H_is_constant hr1_pos hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_deriv z hz
  have h0 := H_at_zero hJ_zero (B := B)
  simpa [h0] using hconst

/-- Lemma: B(z) = B(0) * exp(J(z)). -/
lemma analytic_log_exists
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
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
  have hH_const := H_is_one hr1_pos hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
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
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
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
  have hBform := analytic_log_exists hr1_pos hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- B z = B 0 * exp (J z)
  simpa [norm_mul] using (congrArg norm hBform)

/-- Lemma: |B(z)| = |B(0)| * exp(Re(J(z))). -/
lemma modulus_of_exp_log
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
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
  rw [modulus_of_B_product_form hr1_pos hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]
  rw [Complex.norm_exp]

/-- Lemma: log|B(z)| = log|B(0)| + log(exp(Re(J(z)))). -/
lemma log_modulus_as_sum
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
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
  have h_eq := modulus_of_exp_log hr1_pos hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
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
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R)
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
  have h_sum := log_modulus_as_sum hr1_pos hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- Rearrange to get the difference
  rw [h_sum]
  -- Simplify Real.log (Real.exp (Complex.re (J z))) = Complex.re (J z)
  rw [Real.log_exp]
  ring

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
  have hB_ne_zero_R' : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0 := hB_ne_zero
  obtain ⟨J_B, hJ, hJ0, hJderiv⟩ :=
    I_is_antiderivative hr1_lt_R' hR'_lt_R hB hB_ne_zero_R'
  refine ⟨J_B, hJ, hJ0, hJderiv, ?_⟩
  intro z hz
  simpa using
    (real_log_of_modulus_difference hr1_pos hr1_lt_R' hR'_lt_R hB hB_ne_zero hJ hJ0 hJderiv z hz)
