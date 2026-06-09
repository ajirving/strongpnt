import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Compactness.Lindelof
import StrongPNT.PNT2_LogDerivative
import PrimeNumberTheoremAnd.ZetaBounds


open scoped BigOperators Topology
abbrev ℙ := Nat.Primes


-- Lemma abs_zeta_prod_prime
lemma abs_zeta_prod_prime (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : ℙ) ↦ (norm (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)))⁻¹) (norm (riemannZeta s)) := by
  have := riemannZeta_eulerProduct_hasProd hs|>.norm
  simp_rw [norm_inv] at this
  exact this

theorem HasProd.inv₀ {α β : Type*} {f : α → β} {a : β} [CommGroupWithZero β] [TopologicalSpace β]
    [ContinuousInv₀ β] (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun x ↦ (f x )⁻¹) a⁻¹ := by
  unfold HasProd
  convert Filter.Tendsto.inv₀ h ha
  rw [Finset.prod_inv_distrib]

theorem HasProd.div₀ {α : Type*} {f g : α → ℂ} {a b : ℂ}
    (hf : HasProd f a) (hg : HasProd g b) (hb : b ≠ 0) :
    HasProd (fun x ↦ f x / g x) (a / b) := by
  simp only [div_eq_mul_inv]
  exact hf.mul <| hg.inv₀ hb



-- Theorem zeta_ratio_identity
theorem zeta_ratio_identity (s : ℂ) (hs : 1 < s.re) : HasProd (fun (p : ℙ) ↦ (1 + ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) (riemannZeta (2 * s) / riemannZeta s ) := by
  have zeta2s := riemannZeta_eulerProduct_hasProd (show (2 * s).re > 1 by simp; linarith)
  have := zeta2s.div₀ (riemannZeta_eulerProduct_hasProd hs) (riemannZeta_ne_zero_of_one_lt_re hs)
  convert this using 1
  symm
  ext p
  field_simp
  calc
  _ = (1 - (p : ℂ)^(-s)) / (1 - ((p : ℂ)^(-s)) ^ 2) := by
    rw [← Complex.cpow_nat_mul, Nat.cast_ofNat, mul_neg]
  _ = (1 - (p : ℂ)^(-s)) / ((1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s))) := by ring
  _ = _ := by
    field [Complex.one_sub_prime_cpow_ne_zero p.property hs]

-- Lemma zeta_ratio_at_3_2
lemma zeta_ratio_at_3_2 :  HasProd (fun (p : ℙ) ↦ (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹) (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) := by
  convert zeta_ratio_identity (s := 3 / 2) (by norm_num)
  norm_num

-- Lemma abs_zeta_inequality
lemma hasProd_le_of_nonneg {α : Type*} {f g : α → ℝ} {a b : ℝ}
    (hf : HasProd f a) (hg : HasProd g b) (h_nonneg : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ g i)
    : a ≤ b :=
  le_of_tendsto_of_tendsto' hf hg fun _ ↦ Finset.prod_le_prod (fun i _ ↦ h_nonneg i) (fun i _ ↦ h i )

-- Theorem zeta_lower_bound

lemma abs_zeta_ratio_eval : HasProd (fun (p : ℙ) ↦ (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹) (norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)))  := by
  -- Start from the Euler product identity at 3/2
  have hratio := zeta_ratio_at_3_2.norm
  convert hratio using 1
  ext p
  rw [norm_inv]
  congr
  simp only [Complex.ofReal_ofNat]
  symm
  calc
  _ = ‖1 + ((((p : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ)‖ := by
    congr
    rw [Complex.ofReal_cpow]
    · simp
    · norm_cast
      exact p.property.pos.le
  _ = _ := by
    norm_cast
    simp only [Real.norm_eq_abs, abs_eq_self]
    positivity

theorem zeta_lower_bound (t : ℝ) :
  norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) ≤
    norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  have hs : 1 < (((3 : ℝ) / 2 : ℂ) + t * Complex.I).re := by
    simp
    norm_num
  have := abs_zeta_prod_prime (((3 : ℝ) / 2 : ℂ) + t * Complex.I) hs
  apply hasProd_le_of_nonneg abs_zeta_ratio_eval this fun _ ↦ (by positivity)
  intro p
  gcongr
  · apply norm_pos_iff.mpr
    exact Complex.one_sub_prime_cpow_ne_zero p.property (by simp; norm_num)
  · grw [norm_sub_le]
    simp only [norm_one, Complex.ofReal_ofNat, neg_add_rev, add_le_add_iff_left]
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (mod_cast p.property.pos)]
    simp


lemma zeta_low_332 : ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, a ≤ norm (riemannZeta (((3 : ℝ) / 2) + t * Complex.I)) := by
  refine ⟨norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)), ?_, zeta_lower_bound⟩
  apply norm_pos_iff.mpr
  apply div_ne_zero <;> apply riemannZeta_ne_zero_of_one_lt_re <;> norm_num

open Real Set Filter Topology MeasureTheory
open scoped BigOperators Topology


/-- Lemma: Zeta bound 2. -/
lemma lem_zetaBound2 (s : ℂ) (hs_re : 1 / 10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
  have zeta_formula : riemannZeta s = 1 / 2 + 1 / (s - 1) + s * ∫ (x : ℝ) in Ioi 1, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
    have : s ≠ 0 := by
      intro h
      have : s.re = 0 := by simp [h]
      linarith
    rw [← Zeta0EqZeta (by norm_num : 0 < 1) (by linarith) hs_ne, riemannZeta0_apply,
      Finset.sum_range_succ]
    simp  [Complex.zero_cpow this]
    grind
  grw [zeta_formula, norm_add_le, norm_add_le, norm_mul]
  gcongr
  · norm_num
  · simp
  conv => rhs; rw [div_eq_mul_inv]
  gcongr
  have := ZetaBnd_aux1b 1 (by norm_num) (σ := s.re) (t := s.im) (by linarith)
  convert this using 1
  swap
  · simp
  simp only [one_div, neg_add_rev, Nat.cast_one, Complex.re_add_im]
  congr
  ext
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  ring_nf



/-- Lemma: Final bound combination. -/
lemma lem_finalBoundCombination (s : ℂ) (hs_re : (1 / 2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : ‖riemannZeta s‖ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by
  -- First show s ≠ 1 since |s.im| ≥ 1 > 0, so s.im ≠ 0, but 1 has imaginary part 0
  have hs_ne : s ≠ 1 := by
    intro h
    rw [h] at hs_im
    simp at hs_im
    linarith
  grw [lem_zetaBound2 s (by linarith) hs_ne]
  apply add_lt_add_of_le_of_lt
  · gcongr
    have h2 : (1 : ℝ) ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simp at this
      linarith
    exact div_le_one (by linarith)|>.mpr h2
  rw [← mul_one_div]
  apply mul_lt_mul_of_lt_of_le_of_pos_of_nonneg
  · grw [Complex.norm_le_abs_re_add_abs_im]
    gcongr
    exact abs_lt.mpr (by grind)
  · exact one_div_le (by linarith) (by norm_num)|>.mpr hs_re.1
  · exact div_pos (by norm_num) (by linarith)
  · positivity

/-- Lemma: Upper bound on zeta in the vertical strip. -/
lemma lem_zetaUppBd (z : ℂ) (hz_re : z.re ∈ Ico (1 / 2 : ℝ) (3 : ℝ)) (hz_im : (1 : ℝ) ≤ |z.im|) : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| := by
  apply lt_of_lt_of_le <| lem_finalBoundCombination z (by grind) hz_im
  ring_nf
  rfl

/-- Lemma: Final zeta upper bound with shift. -/
lemma lem_zetaUppBound :
    ∀ t : ℝ, ∀ s : ℂ, ‖s‖ ≤ (1 : ℝ) → (2 : ℝ) < |t| →
      ‖riemannZeta (s + (3/2 : ℝ) + I * t)‖ < (10 : ℝ) + 2 * |t| := by
  intro t s hs ht
  set z := s + (3/2 : ℝ) + I * t with hz_def
  -- Apply lem_zfroms_conditions to get conditions on z
  have hz_cond : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im| := by
    simp [hz_def, I, -one_div]
    have re_bound := Complex.abs_re_le_norm s|>.trans hs
    have im_bound := Complex.abs_im_le_norm s|>.trans hs
    grind
  -- Apply lem_zetaUppBd
  have h_bound : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| :=
    lem_zetaUppBd z hz_cond.1 hz_cond.2
  have h_im_bound : |z.im| ≤ 1 + |t| := by
    simp only [hz_def, Complex.ofReal_div, Complex.ofReal_ofNat, I, Complex.add_im,
      Complex.div_ofNat_im, Complex.im_ofNat, zero_div, add_zero, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
    grw [abs_add_le]
    gcongr
    exact Complex.abs_im_le_norm s|>.trans hs
  linarith

open Metric Set Filter Asymptotics BigOperators

noncomputable def logDerivZeta (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

-- Define the set of zeros in a ball centered at c
def zerosetKfRc (R : ℝ) (c : ℂ) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall c R ∧ f ρ = 0}

-- Lemma 7: zetaanalOnnot1
lemma zetaanalOnnot1 : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  exact DifferentiableOn.analyticOnNhd (fun s hs ↦ (differentiableAt_riemannZeta (by simp_all)).differentiableWithinAt)  isOpen_compl_singleton

lemma D1cinTt_pre (t : ℝ) (ht : |t| > 1) :
    ∀ s ∈ closedBall (3/2 + I * t : ℂ) 1, s ≠ 1 := by
  intro s hs h
  simp only [h, mem_closedBall, Complex.dist_eq] at hs
  have := le_trans (Complex.abs_im_le_norm (1 - (3 / 2 + I * ↑t))) hs
  simp [I] at this
  linarith

-- Lemma 10: D1cinTt
lemma D1cinTt (t : ℝ) (ht : |t| > 1) :
    closedBall (3/2 + I * t : ℂ) 1 ⊆ {s : ℂ | s ≠ 1} := by
  -- This follows directly from D1cinTt_pre
  exact fun s hs => D1cinTt_pre t ht s hs

-- Lemma 11: zetaanalOnD1c
lemma zetaanalOnD1c (t : ℝ) (ht : |t| > 1) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (3/2 + I * t : ℂ) 1) := by
  apply zetaanalOnnot1.mono
  exact D1cinTt t ht


-- Lemma 13: zetacnot0
lemma zetacnot0 (t : ℝ) : riemannZeta (3/2 + I * t) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  simp [I]
  norm_num

-- Lemma: fc_analytic_normalized
lemma fc_analytic_normalized (c : ℂ) (f : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0) :
    (AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (closedBall (0 : ℂ) 1)) ∧ (fun z => f (z + c) / f c) 0 = 1 := by
  refine ⟨AnalyticOnNhd.div ?_ analyticOnNhd_const (by simp_all), (by simpa)⟩
  exact h_analytic.comp (analyticOnNhd_id.add analyticOnNhd_const) (fun _ _ ↦ (by simp_all))

lemma frac_cancel_const {x y c : ℂ} (hc : c ≠ 0) (hy : y ≠ 0) : (x / c) / (y / c) = x / y := by
  field_simp [hc, hy]

-- Lemma: fc_bound
lemma fc_bound (B : ℝ) (R : ℝ) (c : ℂ) (f : ℂ → ℂ)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ := by
  intro z hz
  simp only [Complex.norm_div]
  gcongr
  apply h_bound
  simp_all

-- Lemma: fc_zeros (relation between zeros of f_c and zeros of f)
lemma fc_zeros (r : ℝ) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0) :
    (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  ext ρ'; constructor
  · intro hmem
    use ρ' + c
    simp_all [zerosetKfRc]
  · intro him
    simp_all [zerosetKfRc, Complex.dist_eq]
    rcases him with ⟨x, hx1, rfl⟩
    simp_all

-- Lemma: fc_m_order (orders of zeros are preserved under the shift)

lemma analyticOrderAt_mul_const_eq (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => f z * a) z0 = analyticOrderAt f z0 := by
  -- Rewrite right-multiplication by a as left-multiplication
  have hcomm : (fun z => f z * a) = (fun z => a * f z) := by
    funext z; simp [mul_comm]
  have hrew : analyticOrderAt (fun z => f z * a) z0 =
      analyticOrderAt (fun z => a * f z) z0 := by
    simp [hcomm]
  by_cases hf : AnalyticAt ℂ f z0
  · -- Analytic case: use additivity of analytic order under multiplication
    have hadd : analyticOrderAt (fun z => a * f z) z0
        = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := by
      exact analyticOrderAt_mul analyticAt_const hf
    -- order of a nonzero constant is zero
    have hconst_zero : analyticOrderAt (fun _ : ℂ => a) z0 = 0 := by
      exact AnalyticAt.analyticOrderAt_eq_zero analyticAt_const|>.mpr ha
    rw [hrew, hadd, hconst_zero, zero_add]
  · rw [hrew, analyticOrderAt_eq_zero.mpr, analyticOrderAt_eq_zero.mpr]
    · simp [hf]
    · left
      contrapose hf
      exact analyticAt_iff_analytic_fun_mul analyticAt_const ha|>.mpr hf

lemma fc_m_order (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
    {ρ' : ℂ} :
    analyticOrderAt (fun z => f (z + c) / f c) ρ' = analyticOrderAt f (ρ' + c) := by
  simp only [div_eq_mul_inv]
  rw [analyticOrderAt_mul_const_eq _ _ _ <| inv_ne_zero h_nonzero]
  by_cases hfA : AnalyticAt ℂ f (ρ' + c)
  · rw [(by rfl : (fun z ↦ f (z + c)) = (f ∘ fun z ↦ z + c)),
      hfA.analyticOrderAt_comp (g := (fun z ↦  z + c)) (by fun_prop)]
    simp only [add_sub_add_right_eq_sub]
    suffices analyticOrderAt (fun x ↦ x - ρ') ρ' = 1  by simp_all
    apply AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)|>.mpr
    exact ⟨(fun _ ↦ 1), analyticAt_const, (by simp), (by simp)⟩
  · -- If f is not analytic at ρ' + c, then g0 is not analytic at ρ' either
    have hg_not : ¬ AnalyticAt ℂ (fun z ↦ f (z + c)) ρ' := by
      contrapose! hfA
      convert hfA.comp_sub c
      ring
    -- In the non-analytic case, both sides reduce to 0 by definition
    simp [analyticOrderAt, hfA, hg_not]

-- Lemma: DminusK (characterization of points in shifted domain minus shifted zeros)
lemma DminusK (r1 : ℝ) (R1 : ℝ) (c : ℂ) (f : ℂ → ℂ)
    (h_nonzero : f c ≠ 0) :
    ∀ z : ℂ, z ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun w => f (w + c) / f c) ↔
             z + c ∈ closedBall c r1 \ zerosetKfRc R1 c f := by
  intro z
  constructor
  · simp +contextual [zerosetKfRc]
  · simp_all [zerosetKfRc]

lemma shifted_zeros_correspondence (R1 : ℝ) (c z : ℂ)
    (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
    (hfin_orig : (zerosetKfRc R1 c f).Finite)
    (hfin_shift : (zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c)).Finite) :
    ∑ ρ ∈ hfin_orig.toFinset, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) =
    ∑ ρ' ∈ hfin_shift.toFinset, ((analyticOrderNatAt (fun u => f (u + c) / f c) ρ') : ℂ) / ((z - c) - ρ') := by
  -- Use fc_zeros to establish the bijection between zero sets
  have h_bij : (zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
    fc_zeros R1 c f h_nonzero

  -- Apply Finset.sum_bij with the bijection ρ ↦ ρ - c
  apply Finset.sum_bij (fun ρ _ => ρ - c)

  -- Show that the image is in the target finset
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ ⊢
    rw [h_bij]
    use ρ, hρ

  -- Show injectivity: if ρ₁ - c = ρ₂ - c then ρ₁ = ρ₂
  · intro ρ₁ hρ₁ ρ₂ hρ₂ h_eq
    grind
  -- Show surjectivity
  · intro ρ' hρ'
    simp only [Set.Finite.mem_toFinset] at hρ'
    rw [h_bij] at hρ'
    obtain ⟨ρ, hρ_mem, hρ_eq⟩ := hρ'
    use ρ
    simp only [Set.Finite.mem_toFinset]
    exact ⟨hρ_mem, hρ_eq⟩

  -- Show the function values are equal after transformation
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ
    -- Use fc_m_order to relate the analytic orders
    have h_shift_mem : ρ - c ∈ zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c) := by
      rw [h_bij]
      use ρ, hρ

    have h_order := fc_m_order c f h_nonzero (ρ' := ρ - c)
    -- Since (ρ - c) + c = ρ
    have h_add : (ρ - c) + c = ρ := by ring
    rw [h_add] at h_order
    rw [analyticOrderNatAt, ← h_order]
    -- The coordinate transformation: (z - c) - (ρ - c) = z - ρ
    unfold analyticOrderNatAt
    ring

-- Lemma: final_ineq2 (shifted version of final_ineq1)
lemma final_ineq2
    (B : ℝ) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (c : ℂ) (f : ℂ → ℂ) (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ < B)
    (hfin : (zerosetKfRc R1 (0 : ℂ) (fun z => f (z + c) / f c)).Finite) :
    ∀ z ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun z => f (z + c) / f c),
    ‖(deriv (fun z => f (z + c) / f c) z / (f (z + c) / f c)) - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderNatAt (fun w => f (w + c) / f c) ρ) : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖f c‖) := by
  intro z hz
  let g : ℂ → ℂ := fun w => f (w + c) / f c
  apply final_ineq1 (B / ‖f c‖) _ r1 r R R1 hr1pos hr1_lt_r hr_lt_R1 hR1_lt_R
  · exact (fc_analytic_normalized c f h_analytic h_nonzero).1.mono (by gcongr)
  · exact (fc_analytic_normalized c f h_analytic h_nonzero).2
  · apply fc_bound B R c f
    intro w hw
    exact le_of_lt (h_bound w hw)
  · apply hz
  · rw [one_lt_div <| norm_pos_iff.mpr h_nonzero]
    exact h_bound _ (by simp; linarith)

lemma log_Deriv_Expansion_Zeta (t : ℝ) (ht : |t| > 2)
    (r1 r R1 R : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) :
    let c := (3/2 : ℂ) + I * t
    ∀ B > 1, (∀ z ∈ closedBall c R, ‖riemannZeta z‖ < B) →
    ∀ (hfin : (zerosetKfRc R1 c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderNatAt riemannZeta ρ) : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖riemannZeta c‖) := by
  intro c B hB h_bound hfin z hzmem
  -- From |t| > 3, deduce |t| > 1
  have ht1 : |t| > 1 := lt_trans (by norm_num : (1 : ℝ) < 2) (by simpa using ht)
  -- ζ is analytic on a neighborhood of the closed ball and nonzero at c
  have hζ_analytic : AnalyticOnNhd ℂ riemannZeta (closedBall c 1) := by
    simpa [c] using zetaanalOnD1c t ht1
  have hζ_c_ne : riemannZeta c ≠ 0 := by simpa [c] using zetacnot0 t
  -- Finite zero set for the shifted/normalized function g(u) = ζ(u+c)/ζ(c)
  have hfin_shift : (zerosetKfRc R1 (0 : ℂ) (fun u => riemannZeta (u + c) / riemannZeta c)).Finite := by
    have h_bij := fc_zeros R1 c riemannZeta hζ_c_ne
    have himg : ((fun ρ => ρ - c) '' (zerosetKfRc R1 c riemannZeta)).Finite := hfin.image _
    simpa [h_bij] using himg
  -- Move the domain point to shifted coordinates z0 = z - c
  have hz0mem : (z - c) ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun u => riemannZeta (u + c) / riemannZeta c) := by
    have hiff := DminusK r1 R1 c riemannZeta hζ_c_ne (z - c)
    exact (hiff).mpr (by simpa [sub_add_cancel] using hzmem)
  -- Apply the shifted inequality (final_ineq2) to g at z0 = z - c
  have hineq0 :=
    (final_ineq2 B r1 r R R1 hr1_pos hr1_lt_r hr_lt_R1 hR1_lt_R hR_lt_1 c riemannZeta
      hζ_analytic hζ_c_ne h_bound hfin_shift) (z - c) hz0mem
  -- Show ζ z ≠ 0 using z ∉ zerosetKfRc R1 c ζ
  rcases hzmem with ⟨hz_ball, hz_notin⟩
  have hr1_lt_R1' : r1 < R1 := lt_trans hr1_lt_r hr_lt_R1
  have hz_in_ball_R1 : z ∈ closedBall c R1 := by
    have hz_le_r1 : dist z c ≤ r1 := by simpa [mem_closedBall] using hz_ball
    have hr1_le_R1 : r1 ≤ R1 := le_of_lt hr1_lt_R1'
    have hz_le_R1 : dist z c ≤ R1 := le_trans hz_le_r1 hr1_le_R1
    simpa [mem_closedBall] using hz_le_R1
  have hzeta_ne : riemannZeta z ≠ 0 := by
    intro hz0
    exact hz_notin ⟨hz_in_ball_R1, hz0⟩
  -- Cancel the constant ζ(c) in the double quotient
  have hcancel_frac : (deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta c)
        / (riemannZeta z / riemannZeta c)
        = deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta z := by
    have hc : riemannZeta c ≠ 0 := hζ_c_ne
    have hy : riemannZeta z ≠ 0 := hzeta_ne
    simpa using (frac_cancel_const (x := deriv (fun x => riemannZeta (x + c)) (z - c))
              (y := riemannZeta z) (c := riemannZeta c) hc hy)
  have hcancel_all : (deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta c)
        / (riemannZeta z / riemannZeta c)
        = deriv riemannZeta z / riemannZeta z := by
    simpa [deriv_comp_add_const, sub_add_cancel] using hcancel_frac
  -- Rewrite the inequality's first term using the cancellation identity
  have hineq1 : ‖(deriv riemannZeta z / riemannZeta z)
        - ∑ ρ ∈ hfin_shift.toFinset,
            ((analyticOrderNatAt (fun u => riemannZeta (u + c) / riemannZeta c) ρ) : ℂ)
              / ((z - c) - ρ)‖
        ≤ (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) *
            Real.log (B / ‖riemannZeta c‖) := by
    simpa [hcancel_all] using hineq0
  -- Relate the two sums over zeros via the correspondence lemma
  have hsum_eq := shifted_zeros_correspondence R1 c z riemannZeta hζ_c_ne hfin hfin_shift
  -- Replace the sum over shifted zeros with the sum over original zeros
  have hineq2 : ‖(deriv riemannZeta z / riemannZeta z)
        - ∑ ρ ∈ hfin.toFinset,
            ((analyticOrderNatAt riemannZeta ρ) : ℂ) / (z - ρ)‖
        ≤ (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) *
            Real.log (B / ‖riemannZeta c‖) := by
    simpa [hsum_eq] using hineq1
  -- Replace derivative quotient by logDerivZeta
  simpa [logDerivZeta] using hineq2


lemma zeta32lower : ∃ a > 0, ∀ t : ℝ, ‖riemannZeta (3/2 + I * t)‖ ≥ a := by
  rcases zeta_low_332 with ⟨a, ha_pos, hbound⟩
  refine ⟨a, ha_pos, ?_⟩
  intro t
  simpa [mul_comm] using (hbound t)

-- Lemma 17: zeta32lower_log
lemma zeta32lower_log : ∃ A > 1, ∀ t : ℝ,
    Real.log (1 / ‖riemannZeta (3/2 + I * t)‖) ≤ A := by
  obtain ⟨a, ha_pos, hbound⟩ := zeta32lower
  refine ⟨max (2 : ℝ) (Real.log (1 / a)), ?_, ?_⟩
  · have h1 : (1 : ℝ) < 2 := by norm_num
    have h2 : (2 : ℝ) ≤ max (2 : ℝ) (Real.log (1 / a)) := by exact le_max_left _ _
    exact lt_of_lt_of_le h1 h2
  · intro t
    set x := ‖riemannZeta (3/2 + I * t)‖ with hx
    have hax : a ≤ x := by
      simpa [hx] using (hbound t)
    have hxpos : 0 < x := lt_of_lt_of_le ha_pos hax
    have hxy : 1 / x ≤ 1 / a := by
      -- from a ≤ x and a > 0, we get 1/x ≤ 1/a
      have := one_div_le_one_div_of_le ha_pos hax
      -- this gives 1 / x ≤ 1 / a directly
      simpa [hx] using this
    have hxpos' : 0 < 1 / x := one_div_pos.mpr hxpos
    have hlog : Real.log (1 / x) ≤ Real.log (1 / a) :=
      Real.log_le_log hxpos' hxy
    have : Real.log (1 / x) ≤ max (2 : ℝ) (Real.log (1 / a)) :=
      le_trans hlog (le_max_right _ _)
    simpa [hx] using this

-- Lemma 18: zeta32upper_pre
lemma zeta32upper_pre : ∃ b > 1, ∀ t : ℝ, ∀ s : ℂ, ‖s‖ ≤ 1 → (2 : ℝ) < |t| → ‖riemannZeta (s + 3/2 + Complex.I * t)‖ < b * |t| := by
  refine ⟨(12 : ℝ), by norm_num, ?_⟩
  intro t s hs ht
  have hlt : ‖riemannZeta (s + 3/2 + Complex.I * t)‖ < (10 : ℝ) + 2 * |t| := by
    simpa using (lem_zetaUppBound t s hs ht)
  have honele : (1 : ℝ) ≤ |t| := by
    have : (1 : ℝ) < |t| := lt_trans (by norm_num) ht
    exact le_of_lt this
  have h10le : (10 : ℝ) ≤ 10 * |t| := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right honele (by norm_num : (0 : ℝ) ≤ (10 : ℝ)))
  have hle2 : (10 : ℝ) + 2 * |t| ≤ (12 : ℝ) * |t| := by
    have htmp := add_le_add_right h10le (2 * |t|)
    have hcalc : 10 * |t| + 2 * |t| = (12 : ℝ) * |t| := by ring
    linarith
  exact lt_of_lt_of_le hlt hle2

-- Lemma 19: zeta32upper
lemma zeta32upper : ∃ b > 1, ∀ t : ℝ, |t| > 2 →
  let c := (3/2 : ℂ) + I * t
  ∀ s ∈ closedBall c 1, ‖riemannZeta s‖ < b * |t| := by
  -- Use zeta32upper_pre to get the bound
  obtain ⟨b, hb_gt, hbound⟩ := zeta32upper_pre
  refine ⟨b, hb_gt, ?_⟩
  intro t ht c s hs
  -- s ∈ closedBall c 1 means |s - c| ≤ 1
  rw [mem_closedBall] at hs
  -- Define s_pre = s - c, so |s_pre| ≤ 1
  set s_pre := s - c with hs_pre_def
  have hs_pre_bound : ‖s_pre‖ ≤ 1 := by
    rw [hs_pre_def]
    rwa [Complex.dist_eq] at hs
  -- Now s = s_pre + c = s_pre + 3/2 + I * t
  have hs_eq : s = s_pre + 3/2 + I * t := by
    rw [hs_pre_def]
    ring
  -- Apply zeta32upper_pre
  rw [hs_eq]
  exact hbound t s_pre hs_pre_bound ht

-- Lemma 20: Zeta1_Zeta_Expand

lemma Zeta1_Zeta_Expand :
    ∃ A > 1, ∃ b > 1,
    ∀ (t : ℝ) (_ : |t| > 2)
    (r1 r R1 R : ℝ)
    (_ : 0 < r1) (_ : r1 < r)
    (_ : 0 < r) (_ : r < R1) (_ : 0 < R1) (_ : R1 < R) (_ : R < 1),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc R1 c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderNatAt riemannZeta ρ) : ℂ) / (z - ρ)‖ ≤
      (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * (Real.log |t| + Real.log b + A) := by
  -- Apply the three lemmas mentioned in the informal proof
  obtain ⟨b, hbgt1, hb⟩ := zeta32upper
  obtain ⟨A, hAgt1, hA⟩ := zeta32lower_log

  -- Provide the constants A, b as required
  refine ⟨A, hAgt1, b, hbgt1, ?_⟩
  intro t ht r1 r R1 R hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 c hfin z hz

  -- Apply log_Deriv_Expansion_Zeta
  have hexp_lemma := log_Deriv_Expansion_Zeta t ht r1 r R1 R hr1_pos hr1_lt_r hr_lt_R1 hR1_lt_R hR_lt_1

  -- Set B = b * |t| as mentioned in informal proof
  have htpos : (0 : ℝ) < |t| := by linarith [ht]
  have hBgt1 : b * |t| > 1 := by
    have hb_pos : (0 : ℝ) < b := by linarith [hbgt1]
    calc (1 : ℝ) < 1 * 2 := by norm_num
    _ < b * 2 := mul_lt_mul_of_pos_right (by linarith [hbgt1]) (by norm_num)
    _ < b * |t| := mul_lt_mul_of_pos_left ht hb_pos

  -- Apply zeta32upper to get bound on |ζ| in the ball
  have hbound_ball : ∀ s ∈ closedBall (3/2 + I * t) R, ‖riemannZeta s‖ < b * |t| := by
    have hsubset : closedBall (3/2 + I * t) R ⊆ closedBall (3/2 + I * t) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1)
    intro s hs
    have hs1 : s ∈ closedBall (3/2 + I * t) 1 := hsubset hs
    have ht2 : |t| > 2 := by linarith [ht]
    specialize hb t ht2
    exact hb s hs1

  -- Apply log_Deriv_Expansion_Zeta with B = b * |t|
  have hexp := hexp_lemma (b * |t|) hBgt1 hbound_ball hfin z hz

  -- Use properties of ζ at c and bounds from zeta32lower_log
  have hζne : riemannZeta (3/2 + I * t) ≠ 0 := zetacnot0 t
  have hζpos : (0 : ℝ) < ‖riemannZeta (3/2 + I * t)‖ := norm_pos_iff.mpr hζne

  have hBpos : (0 : ℝ) < b * |t| := mul_pos (by linarith [hbgt1]) htpos
  have hBne : b * |t| ≠ 0 := ne_of_gt hBpos
  have htne : |t| ≠ 0 := ne_of_gt htpos
  have hbne : b ≠ 0 := ne_of_gt (by linarith [hbgt1])

  -- Key logarithmic bound using zeta32lower_log
  have hlog_bound : Real.log (b * |t| / ‖riemannZeta (3/2 + I * t)‖) ≤
                    Real.log |t| + Real.log b + A := by
    rw [Real.log_div hBne (ne_of_gt hζpos)]
    rw [Real.log_mul hbne htne]
    -- Apply zeta32lower_log bound
    have hA_bound := hA t
    have : -Real.log ‖riemannZeta (3/2 + I * t)‖ ≤ A := by
      have eq_neg : Real.log (1 / ‖riemannZeta (3/2 + I * t)‖) = -Real.log ‖riemannZeta (3/2 + I * t)‖ := by
        rw [Real.log_div (by norm_num) (ne_of_gt hζpos)]
        simp
      rw [← eq_neg]
      exact hA_bound
    linarith

  -- Need to show the coefficient is nonnegative
  have hcoeff_nonneg : (0 : ℝ) ≤ 16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) := by
    apply add_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · apply sq_nonneg
      · apply le_of_lt
        apply pow_pos
        linarith [hr1_lt_r]
    · apply div_nonneg
      · norm_num
      · apply le_of_lt
        apply mul_pos
        · -- Show R^2 / R1 - R1 > 0
          have h_gt : R > R1 := hR1_lt_R
          have h1_pos : (1 : ℝ) < R/R1 := by
            rw [one_lt_div]
            · exact h_gt
            · exact hR1_pos
          have h_sq_div : R^2/R1 = R * (R/R1) := by
            field [ne_of_gt hR1_pos]
          rw [h_sq_div]
          have h_r_pos : (0 : ℝ) < R := by linarith [hR1_pos, h_gt]
          have : R * (R/R1) > R * 1 := by
            apply mul_lt_mul_of_pos_left h1_pos h_r_pos
          simp at this
          linarith [this]
        · apply Real.log_pos
          rw [one_lt_div]
          · exact hR1_lt_R
          · exact hR1_pos

  -- Final calculation combining all bounds
  calc ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderNatAt riemannZeta ρ) : ℂ) / (z - ρ)‖
      ≤ (16 * r^2 / ((r - r1)^3) +
          1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (b * |t| / ‖riemannZeta (3/2 + I * t)‖) := hexp
    _ ≤ (16 * r^2 / ((r - r1)^3) +
          1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * (Real.log |t| + Real.log b + A) := by
      exact mul_le_mul_of_nonneg_left hlog_bound hcoeff_nonneg

-- Lemma 21: Zeta1_Zeta_Expansion (final)

lemma Zeta1_Zeta_Expansion
    (r1 r : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < 5 / (6 : ℝ)) :
    ∃ C > 1,
    ∀ (t : ℝ) (_ : |t| > 2),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc (5 / (6 : ℝ)) c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ)‖ ≤
      C * (1 / (r - r1)^3 + 1) * Real.log |t| := by
  -- Introduce the universal constants from Zeta1_Zeta_Expand
  obtain ⟨A, hAgt1, b, hbgt1, hmain⟩ := Zeta1_Zeta_Expand
  -- Fix numeric radii
  let R1 : ℝ := 5 / 6
  let R  : ℝ := 8 / 9
  have hR1_pos : 0 < R1 := by norm_num [R1]
  have hR1_lt_R : R1 < R := by norm_num [R1, R]
  have hR_lt_1  : R < 1 := by norm_num [R]
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
  -- Define some shorthand constants
  let d : ℝ := (r - r1) ^ 3
  have hd_pos : 0 < d := by
    have : 0 < r - r1 := sub_pos.mpr hr1_lt_r
    simpa [d] using pow_pos this 3
  let A0 : ℝ := 1 / ((R^2 / R1 - R1) * Real.log (R / R1))
  have hA0_pos : 0 < A0 := by
    have hx1 : 0 < R^2 / R1 - R1 := by
      --  (8/9)^2 / (5/6) - (5/6) = 31/270 > 0
      norm_num [R, R1]
    have hx2 : 0 < Real.log (R / R1) := by
      -- R/R1 = 16/15 > 1
      have : (1 : ℝ) < R / R1 := by norm_num [R, R1]
      exact Real.log_pos this
    have hxden : 0 < (R^2 / R1 - R1) * Real.log (R / R1) := mul_pos hx1 hx2
    simpa [A0] using (one_div_pos.mpr hxden)
  -- Coefficient K in Zeta1_Zeta_Expand specialized to our R1,R
  let K : ℝ := 16 * r^2 / d + A0
  -- S := log b + A (positive)
  let S : ℝ := Real.log b + A
  have hS_pos : 0 < S := by
    have hbpos : 0 < Real.log b := Real.log_pos hbgt1
    have hApos : 0 < A := lt_trans (by norm_num) hAgt1
    exact add_pos hbpos hApos
  -- Choose a constant C large enough so K ≤ C * (1/d + 1) and (L + S) ≤ (1 + S/log 3) * L
  let Kcoeff : ℝ := max (16 * r^2) A0
  have hK_le : K ≤ Kcoeff * (1 / d + 1) := by
    have hx_nonneg : 0 ≤ 1 / d := by
      exact le_of_lt (one_div_pos.mpr hd_pos)
    have hα_le : 16 * r^2 / d ≤ Kcoeff * (1 / d) := by
        have hα : 16 * r^2 ≤ Kcoeff := le_max_left _ _
        have : (16 * r^2) * (1 / d) ≤ Kcoeff * (1 / d) :=
          mul_le_mul_of_nonneg_right hα hx_nonneg
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hβ_le : A0 ≤ Kcoeff * 1 := by
      have hβ : A0 ≤ Kcoeff := le_max_right _ _
      simpa using hβ
    have : 16 * r^2 / d + A0 ≤ Kcoeff * (1 / d) + Kcoeff * 1 :=
      add_le_add hα_le hβ_le
    simpa [K, mul_add, mul_one, add_comm, add_left_comm, add_assoc] using this
  -- Build the final constant C (independent of t)
  let C : ℝ := max (Kcoeff * (1 + S / Real.log 2)) 2
  have hC_gt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hC_gt1, ?_⟩
  -- Now fix t, apply the expansion lemma and chain bounds
  intro t ht
  -- Unfold the let-binding c in the goal
  simp only
  intro hfin z hz
  -- Apply Zeta1_Zeta_Expand specialized to R1,R
  have ht2 : |t| > 2 := by linarith [ht]
  have hineq0 :=
    hmain t ht2 r1 r R1 R hr1_pos hr1_lt_r (lt_trans hr1_pos hr1_lt_r) hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
  have hineq1 := hineq0 hfin z hz
  -- Rewrite RHS with our K and S
  have hK_eq : (16 * r^2 / (r - r1)^3 + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) = K := by
    simp [K, A0, d, R1, R]
  have hLS_eq : Real.log |t| + Real.log b + A = Real.log |t| + S := by
    simp [S, add_comm, add_assoc]
  have hineq2 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ)‖
        ≤ K * (Real.log |t| + S) := by
    rw [← hK_eq, ← hLS_eq]
    exact hineq1
  -- Bound (Real.log |t| + S) by (1 + S/log 3) * Real.log |t|
  have hlog2pos : 0 < Real.log (2 : ℝ) := by
    exact Real.log_pos (by norm_num)
  -- Since |t| > 3, we have log 3 ≤ log |t|
  have hpos_t : 0 < |t| := lt_trans (by norm_num) ht
  have hL_ge_log3' : Real.log 2 ≤ Real.log |t| := by
    have hge : (2 : ℝ) ≤ |t| := le_of_lt ht
    exact Real.log_le_log (by norm_num) hge
  have hratio_nonneg : 0 ≤ S / Real.log 2 := le_of_lt (div_pos hS_pos hlog2pos)
  have hneq : Real.log 2 ≠ 0 := ne_of_gt hlog2pos

  -- Key inequality: S ≤ (S / log 3) * log |t|
  have hS_le : S ≤ (S / Real.log 2) * Real.log |t| := by
    -- Since log 3 ≤ log |t| and S/log 3 ≥ 0, we have (S/log 3) * log 3 ≤ (S/log 3) * log |t|
    -- But (S/log 3) * log 3 = S, so S ≤ (S/log 3) * log |t|
    calc S
      = (S / Real.log 2) * Real.log 2 := by field
      _ ≤ (S / Real.log 2) * Real.log |t| := mul_le_mul_of_nonneg_left hL_ge_log3' hratio_nonneg

  have hsum_bound : Real.log |t| + S ≤ (1 + S / Real.log 2) * Real.log |t| := by
    have hstep : Real.log |t| + S ≤ Real.log |t| + (S / Real.log 2) * Real.log |t| := by
      gcongr
    -- Real.log |t| + (S / Real.log 3) * Real.log |t| = (1 + S / Real.log 3) * Real.log |t|
    have h_factor : Real.log |t| + (S / Real.log 2) * Real.log |t| = (1 + S / Real.log 2) * Real.log |t| := by ring
    rw [← h_factor]
    exact hstep
  -- Chain: ≤ K*(1 + S/log 3) * log|t|
  have hineq3 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ)‖
        ≤ K * ((1 + S / Real.log 2) * Real.log |t|) :=
    le_trans hineq2 (mul_le_mul_of_nonneg_left hsum_bound (by
      have hr2_nonneg : 0 ≤ r^2 := by
        have : 0 ≤ r * r := mul_nonneg (le_of_lt hr_pos) (le_of_lt hr_pos)
        simpa [pow_two] using this
      have hterm1 : 0 ≤ 16 * r^2 / d :=
        div_nonneg (mul_nonneg (by norm_num) hr2_nonneg) (le_of_lt hd_pos)
      have : 0 ≤ K := add_nonneg hterm1 (le_of_lt hA0_pos)
      exact this))
  -- Replace K by Kcoeff * (1/d + 1)
  have hKcoeff : K * ((1 + S / Real.log 2) * Real.log |t|)
      ≤ (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 2) * Real.log |t|) :=
    mul_le_mul_of_nonneg_right hK_le (by
      have hLpos : 0 < Real.log |t| :=
        Real.log_pos (lt_trans (by norm_num) ht)
      have hcoef_pos : 0 < 1 + S / Real.log 2 :=
        add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt (div_pos hS_pos hlog2pos))
      have : 0 ≤ (1 + S / Real.log 2) * Real.log |t| :=
        le_of_lt (mul_pos hcoef_pos hLpos)
      simpa using this)
  -- Put everything together and rewrite into the target form using C
  have hfinal := le_trans hineq3 hKcoeff
  -- C was chosen so that C ≥ Kcoeff * (1 + S/log 3)
  have hC_ge : Kcoeff * (1 + S / Real.log 2) ≤ C := by
    exact le_max_left _ _
  -- Therefore RHS ≤ C * (1/d + 1) * log|t|
  have : (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 2) * Real.log |t|)
      ≤ C * (1 / d + 1) * Real.log |t| := by
    have hnonneg_term : 0 ≤ (1 / d + 1) * Real.log |t| := by
      have h1 : 0 ≤ 1 / d := le_of_lt (one_div_pos.mpr hd_pos)
      have h2 : 0 ≤ Real.log |t| := le_of_lt (Real.log_pos (lt_trans (by norm_num) ht))
      have : 0 ≤ (1 / d + 1) := add_nonneg h1 (by norm_num)
      exact mul_nonneg this h2
    have hstep := mul_le_mul_of_nonneg_left hC_ge hnonneg_term
    -- rewrite both sides to match target
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
  -- Substitute d = (r - r1)^3 to get the final form
  have hfinal_le := le_trans hfinal this
  simp only [d] at hfinal_le
  exact hfinal_le
