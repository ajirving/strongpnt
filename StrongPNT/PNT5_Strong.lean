import PrimeNumberTheoremAnd.MediumPNT
import StrongPNT.ZetaZeroFree

set_option lang.lemmaCmd true

--Put in a namespace to avoid collisions with MediumPNT
namespace Strong
open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)


local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I

local notation "ψ" => ChebyshevPsi


open ComplexConjugate
open MeasureTheory

lemma LogDerivZetaBoundedAndHolo : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound 1 9 A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  -- Use the uniform bound with exponent 2 and holomorphicity on the ^1-rectangle,
  -- then adjust constants to match our LogDerivZetaHasBound (which uses log^9 in the RHS).
  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd2⟩ := LogDerivZetaBndUnif2
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT'
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  · -- Bound: use the log^2 bound and the fact log^2 ≤ log^9 for |t|>3 (so log|t|>1).
    intro σ t ht hσ
    have hσ' : σ ∈ Ici (1 - A₁ / Real.log |t| ^ 1) := by
      -- Since min A₁ A₂ ≤ A₁, the lower threshold 1 - A₁/log ≤ 1 - min/log ≤ σ
      -- Hence σ ≥ 1 - A₁/log.
      have hAle : min A₁ A₂ ≤ A₁ := min_le_left _ _
      have hlogpos : 0 < Real.log |t| := by
        -- |t| > 3 ⇒ log|t| > 0
        exact Real.log_pos (lt_trans (by norm_num) ht)
      have := sub_le_sub_left
        (div_le_div_of_nonneg_right (show min A₁ A₂ ≤ A₁ from hAle) (le_of_lt hlogpos)) 1
      -- 1 - A₁ / log ≤ 1 - min / log
      have hthr : 1 - A₁ / Real.log |t| ^ 1 ≤ 1 - (min A₁ A₂) / Real.log |t| ^ 1 := by
        simpa [pow_one] using this
      -- hσ : σ ≥ 1 - (min A₁ A₂) / log |t|
      have : σ ∈ Ici (1 - (min A₁ A₂) / Real.log |t| ^ 1) := by
        simpa [pow_one] using hσ
      exact le_trans hthr (mem_Ici.mp this)
    -- Apply the log^2 bound, then compare exponents 2 ≤ 9 since log|t| ≥ 1
    have hmain := zeta_bnd2 σ t ht (by simpa [pow_one] using hσ')
    have hlog_ge_one : (1 : ℝ) ≤ Real.log |t| := by
      -- from |t| > 3 we have log|t| ≥ 1 since exp 1 ≤ 3 < |t|
      have hpos : 0 < |t| := lt_trans (by norm_num) ht
      have hle : Real.exp 1 ≤ |t| := by
        have : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
        exact this.trans (le_of_lt ht)
      have := Real.log_le_log (Real.exp_pos 1) hle
      simpa [Real.log_exp] using this
    have hpow : Real.log |t| ^ (2 : ℕ) ≤ Real.log |t| ^ (9 : ℕ) := by
      exact pow_le_pow_right₀ hlog_ge_one (by decide : (2 : ℕ) ≤ 9)
    -- Multiply both sides by C ≥ 0
    have : C * Real.log |t| ^ (2 : ℕ) ≤ C * Real.log |t| ^ (9 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt C_pos)
    convert! (le_trans hmain this)
    simp
  · -- Holomorphic: restrict the ^1-rectangle using A := min A₁ A₂ ≤ A₂
    intro T hT
    -- Our rectangle is a subset since 1 - (min A₁ A₂)/log T ≥ 1 - A₂/log T
    have hsubset :
        ((Icc ((1 : ℝ) - min A₁ A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) ⊆
        ((Icc ((1 : ℝ) - A₂ / Real.log T ^ 1) 2) ×ℂ (Icc (-T) T) \ {1}) := by
      intro s hs
      rcases hs with ⟨hs_box, hs_ne⟩
      rcases hs_box with ⟨hre, him⟩
      rcases hre with ⟨hre_left, hre_right⟩
      -- build the new box membership
      constructor
      · -- s ∈ Icc (1 - A₂ / Real.log T ^ 1) 2 ×ℂ Icc (-T) T
        constructor
        · -- s ∈ re ⁻¹' Icc (1 - A₂ / Real.log T ^ 1) 2
          constructor
          · -- 1 - A₂ / Real.log T ^ 1 ≤ s.re
            have hAle : min A₁ A₂ ≤ A₂ := min_le_right _ _
            have hlogpos : 0 < Real.log T := by
              have hT' : 1 < T := by linarith
              exact Real.log_pos hT'
            have := sub_le_sub_left
              (div_le_div_of_nonneg_right hAle (le_of_lt hlogpos)) 1
            have hthr : 1 - A₂ / Real.log T ^ 1 ≤ 1 - (min A₁ A₂) / Real.log T ^ 1 := by
              simpa [pow_one] using this
            exact le_trans hthr hre_left
          · exact hre_right
        · exact him
      · exact hs_ne
    exact (holo T hT).mono hsubset

open Filter Topology

/-%%
\section{Strong_PNT}

\begin{theorem}[Strong_PNT]\label{Strong_PNT}\lean{Strong_PNT}\leanok  We have
$$ \sum_{n \leq x} \Lambda(n) = x + O(x \exp(-c(\log x)^{1/2})).$$
\end{theorem}
%%-/
/-- *** Prime Number Theorem (Strong_ Strength) *** The `ChebyshevPsi` function is asymptotic to `x`. -/
theorem Strong_PNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := by
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by
    exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by
    rwa [← integral_Ici_eq_integral_Ioi]
  clear ContDiffν ν_nonneg'  ν_massOne'
  obtain ⟨c_close, c_close_pos, h_close⟩ :=
    SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩  := MellinOfSmooth1cExplicit ContDiff1ν ν_supp ν_massOne
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := LogDerivZetaBoundedAndHolo
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  have holo2 : HolomorphicOn (fun s ↦ ζ' s / ζ s) (uIcc σ₂ 2 ×ℂ uIcc (-3) 3 \ {1}) := by
    apply holo2'.mono
    intro s hs
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_reProdIm,
      mem_Icc, mem_singleton_iff] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    rcases hs.1.1 with ⟨left, right⟩
    constructor
    · apply le_trans _ left
      apply min_le_min_right
      apply le_max_left
    · rw [max_eq_right (by linarith)] at right ⊢
      exact right

  clear holo2' σ₂'_lt_one

  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2GenBound ν_supp ContDiff1ν (by norm_num) (by norm_num) zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3GenBound ν_supp ContDiff1ν (by norm_num) (by norm_num) zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  ⟨σ₂_pos, σ₂_lt_one⟩
  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4GenBound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ (by norm_num : (1 : ℝ) > 0) A_in_Ioc
  simp only [rpow_one] at hc₂ hc₃ hc₄
  let C' := c_close + C_main
  let C'' := 2 *(c₁ + c₂)
  let C''' := 2 * (c₃ + c₄)


  let c : ℝ := A ^ ((1 : ℝ) / 2) / 4
  have cpos : 0 < c := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c]
    obtain ⟨left, right⟩ := A_in_Ioc
    positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩

  let c_εx : ℝ := A ^ ((1 : ℝ) / 2) / 2
  have c_εx_pos : 0 < c_εx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx]
  let c_Tx : ℝ := A ^ ((1 : ℝ) / 2)
  have c_Tx_pos : 0 < c_Tx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx, c_Tx]


  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / 2)))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / 2)))

  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 2)).comp Real.tendsto_log_atTop

  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x) : -c_εx * Real.log x ^ ((1 : ℝ) / 2) = -(c_εx * Real.log x ^ ((1 : ℝ) / 2)) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    apply (tendsto_rpow_atTop (by norm_num)).comp
    exact tendsto_log_atTop

  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num

  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx (by norm_num : (1 : ℝ) / 2 < 1)
    exact this.eventually_gt_atTop 2

  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3

  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) := by
    apply (tendsto_order.mp ?_).1
    · exact σ₂_lt_one
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp [Function.comp, div_eq_mul_inv]
    · simp

  have eventually_ε_lt_ε_main : ∀ᶠ (x : ℝ) in atTop, εx x < ε_main := by
    apply (tendsto_order.mp ex_to_zero).2
    assumption

  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop

  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 100] with x hx x_gt
        convert hx using 1
        · rw [Real.norm_of_nonneg]
          apply Real.log_nonneg
          have : (1 : ℝ) = Real.log (rexp 1) := by
            exact Eq.symm (Real.log_exp 1)

          rw [this]
          apply Real.log_le_log
          · exact Real.exp_pos _
          · have := Real.exp_one_lt_d9
            linarith
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp

  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this]
      rw [mul_assoc]
      grw [hx]
      simp

  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c εx c_εx
    have : 0 < (A ^ ((1 : ℝ) / 2) / 4) := by
        positivity
    have const1bnd : (A ^ ((1 : ℝ) / 2) / 4) < (A ^ ((1 : ℝ) / 2) / 2) := by
        linarith
    have const2bnd : (0 : ℝ) < 1 / 2 := by norm_num
    have this (x) :
      C' * rexp (-(A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]

  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / 2
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have : 0 < A ^ const2 := by
      unfold const2
      apply Real.rpow_pos_of_pos
      exact A_in_Ioc.1
    have this (x) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]

  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / 2)
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (1 : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul]
    rw [Real.log_exp]
    rw [Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (1 : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le]
        rw [div_eq_mul_inv]
        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos]
        rw [(by linarith : 1 + -(const2 * 1) = const2)]
      rw [div_mul_eq_div_div]
      rw [neg_div]
      rw [this (A_in_Ioc.1)]

      rw [mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div]

      rw [this (y := Real.log x) logxpos]

      rw [← Real.exp_add]
      apply Real.exp_monotone

      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]

      gcongr

      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      rw [←Real.sqrt_eq_rpow]
      apply Real.sqrt_nonneg

    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith

  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / 2
    have const2eq : const2 = 1 / 2 := by rfl
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    have const1eq : const1 = (A ^ const2 / 2) := by rfl
    set const1' := (A ^ const2 / 4)
    have const1'eq : const1' = (A ^ const2 / 4) := by rfl
    have A_pow_pos : 0 < A ^ const2 := by
      unfold const2
      apply Real.rpow_pos_of_pos
      exact A_in_Ioc.1

    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]

    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt

    have this (x) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)))
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      ring
    rw [this]
    rw [rpow_one] at x_bnd
    grw [x_bnd]

  have event_4_aux4 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      Tendsto (fun x ↦ c' * Real.log x ^ pow2) atTop (𝓝 0) := by
    rw [← mul_zero c']
    apply Tendsto.const_mul
    have := tendsto_rpow_neg_atTop (y := -pow2) (by linarith)
    rw [neg_neg] at this
    apply this.comp
    exact Real.tendsto_log_atTop

  have event_4_aux3 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      ∀ᶠ (x : ℝ) in atTop, c' * (Real.log x) ^ pow2 < c := by
    apply (event_4_aux4 pow2_neg cpos c').eventually_lt_const
    exact cpos

  have event_4_aux2 {c1 : ℝ} (c1pos : 0 < c1) (c2 : ℝ) {pow1 : ℝ} (pow1_lt : pow1 < 1) :
      ∀ᶠ (x : ℝ) in atTop, 0 ≤ Real.log x * (c1 - c2 * (Real.log x) ^ (pow1 - 1)) := by
    filter_upwards [eventually_gt_atTop 3 , event_4_aux3 (by linarith : pow1 - 1 < 0)
      (by linarith : 0 < c1 / 2) c2] with x x_gt hx
    have : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      linarith
    apply mul_nonneg this
    linarith

  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    filter_upwards [event_4_aux2 (by linarith : 0 < 1 - const1) (const2 + const3) pow1_lt,
      eventually_gt_atTop 3] with x hx x_gt
    rw [← sub_nonneg]
    have :
      Real.log x - const3 * Real.log x ^ pow1 - (const1 * Real.log x + const2 * Real.log x ^ pow1)
      = (1 - const1) * Real.log x - (const2 + const3) * Real.log x ^ pow1 := by ring
    rw [this]
    convert hx using 1
    ring_nf
    congr! 1
    · have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
          = const2 * Real.log x ^ pow1 := by
        rw [mul_assoc, mul_comm, mul_assoc]
        congr! 1
        conv =>
          enter [1, 2]
          rw [← Real.rpow_one (Real.log x)]
        rw [← Real.rpow_add (Real.log_pos (by linarith))]
        ring_nf
      rw [this]
    have : Real.log x * const3 * Real.log x ^ (-1 + pow1)
        = const3 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]



  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / 2) / 4) * Real.log x ^ ((1 : ℝ) / 2)) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂_lt_one (A ^ ((1 : ℝ) / 2) / 2)
      (A ^ ((1 : ℝ) / 2) / 4) (by norm_num : (1 : ℝ) / 2 < 1)] with x x_gt hx
    gcongr
  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf

    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf
  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4
  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge zeta_bnd
  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X

  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T)
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T) >= 1 - (1/2) / 1 := by
      gcongr
      · exact A_in_Ioc.2
      · apply (Real.le_log_iff_exp_le (by positivity)).mpr
        linarith[Real.exp_one_lt_d9]
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound

  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo1_compat : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) := by
    -- direct from holo1 with ^1-rectangle
    simpa [σ₁, pow_one] using! holo1

  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith[mem_reProdIm.mp hs.1 |>.1.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ ≤ 2 * (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖) + ‖I₅ ν ε X σ₂‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1_compat ν_supp ν_nonneg ν_massOne ContDiff1ν,
      SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂_pos σ₁_lt_one σ₂_lt_σ₁ holo1_compat holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    grw [norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_sub_le, norm_add_le, norm_sub_le]
    rw [I9I1 (by linarith), I8I2 (by linarith), I7I3 (by linarith), I6I4 (by linarith)]
    simp only [norm_neg, RCLike.norm_conj]
    exact le_of_eq (by ring)
  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : 2 * (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : 2 * (c₁ + c₂) * X * Real.log X / (ε * T)
      = 2 * (c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
  have C'''bnd : 2 * (c₃ * X * X ^ (-A / Real.log T) / ε
                    + c₄ * X * X ^ (-A / Real.log T) / ε)
                  ≤ C''' * X * X ^ (-A / Real.log T) / ε := by
    apply le_of_eq
    ring

  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X)
                  + (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖
                  + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + (2 * (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖)
                  + ‖I₅ ν ε X σ₂‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (2 * (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε)
                  + c₅ * X ^ σ₂ / ε) := by
      gcongr
      · convert! h_close using 1
        rw [← norm_neg]
        congr
        ring
    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + (2 * (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T))
                  + 2 * (c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

/-%%
\begin{proof}
\uses{ChebyshevPsi, SmoothedChebyshevClose, LogDerivZetaBndAlt, ZetaBoxEval, LogDerivZetaBndUniform, LogDerivZetaHolcSmallT, LogDerivZetaHolcLargeT,
SmoothedChebyshevPull1, SmoothedChebyshevPull2, I1Bound, I2Bound, I3Bound, I4Bound, I5Bound}\leanok
  Evaluate the integrals.
\end{proof}
%%-/

#print axioms Strong_PNT

end Strong
