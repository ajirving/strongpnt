import PrimeNumberTheoremAnd.MediumPNT
import StrongPNT.ZetaZeroFree

set_option lang.lemmaCmd true
set_option maxHeartbeats 400000

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

/-- Our preferred left vertical line. -/
@[inline] noncomputable def sigma1Of (A T : ℝ) : ℝ := 1 - A / Real.log T

def LogDerivZetaHasBound (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t|)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9


theorem log_pos (T : ℝ) (T_gt : 3 < T) : (Real.log T > 1) := by
    have elt3 : Real.exp 1 < 3 := by
      linarith[Real.exp_one_lt_d9]
    have logTgt1 : Real.log T > 1 := by
      refine (lt_log_iff_exp_lt ?_).mpr ?_
      · linarith
      · linarith
    exact logTgt1

/-%%
\begin{lemma}[I2Bound]\label{I2Bound}\lean{I2Bound}\leanok
We have that
$$
\left|I_{2}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon T}
.
$$
\end{lemma}
%%-/
lemma I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
--    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound: LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ := sigma1Of A T
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) 9)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
--  clear suppSmoothingF mass_one ContDiffSmoothingF
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  have log_big : 1 < Real.log T := by exact log_pos T (T_gt)
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    have : σ₁ = sigma1Of A T := rfl
    rw [this]
    unfold sigma1Of
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_left
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      exact A_in.1.le
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have : σ₁ = sigma1Of A T := rfl
  have σ₁pos : 0 < σ₁ := by
    have : σ₁ = sigma1Of A T := rfl
    rw [this]
    unfold sigma1Of
    rw[sub_pos]
    calc
      A / Real.log T ≤ 1 / 2 / Real.log T := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply le_of_lt
        linarith
        -- refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> (Tpos)
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        apply le_of_lt
        refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> linarith[Real.exp_one_lt_d9]
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹), ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        convert this using 3
        apply uIoc_of_le
        exact interval_length_nonneg
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
        calc
          1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
          _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
  -- Now bound the integrand
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ 9 := has_bound σ (-T) (by simp; rw [abs_of_pos Tpos]; exact T_gt) (by rw[this] at hσ; unfold sigma1Of at hσ; simp at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ 9 := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  -- Then estimate the remaining factors.
  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, sigma1Of] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, sigma1Of] at hσ ⊢
          linarith[one_add_inv_log X_gt.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, sigma1Of]
          rw[← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
          exact hσ.2
          · refine (Real.log_pos ?_).ne.symm
            linarith
          · apply Real.log_pos
            linarith
          · linarith
          · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_left]
          exact this
          exact ε_pos
          positivity
          apply mul_pos ε_pos
          exact lt_of_lt_of_le (pow_pos Tpos 2) this
          positivity
        _ = C' * X / (ε * T) := by
          field_simp
          ring
/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBndUniform, I2, I8}\leanok
Unfold the definitions and apply the triangle inequality.
$$
\left|I_{2}(\nu, \epsilon, X, T, \sigma_1)\right| =
\left|\frac{1}{2\pi i} \int_{\sigma_1}^{\sigma_0}
\left(\frac{-\zeta'}\zeta(\sigma - T i) \right) \cdot
\mathcal M(\widetilde 1_\epsilon)(\sigma - T i) \cdot
X^{\sigma - T i}
 \ d\sigma
\right|
$$
$$\leq
\frac{1}{2\pi}
\int_{\sigma_1}^{\sigma_0}
C \cdot \log T ^ 9
\frac{C'}{\epsilon|\sigma - T i|^2}
X^{\sigma_0}
 \ d\sigma
 \leq
C'' \cdot \frac{X\log T^9}{\epsilon T^2}
,
$$
where we used Theorems \ref{MellinOfSmooth1b} and \ref{LogDerivZetaBndUniform}, and the fact that
$X^\sigma \le X^{\sigma_0} = X\cdot X^{1/\log X}=e \cdot X$.
Since $T>3$, we have $\log T^9 \leq C''' T$.
\end{proof}
%%-/

/-%%
\begin{lemma}[I8Bound]\label{I8Bound}\lean{I8Bound}\leanok
We have that
$$
\left|I_{8}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon T}
.
$$
\end{lemma}
%%-/
lemma I8Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
--    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by

  obtain ⟨C, hC, i2Bound⟩ := I2Bound suppSmoothingF ContDiffSmoothingF has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
  -- intro m
  change ‖I₂ SmoothingF ε T X (sigma1Of A T)‖ ≤ C * X / (ε * T) at i2Bound
  unfold sigma1Of at i2Bound
  have σ₁_eq : σ₁ = 1 - A / (Real.log T) := rfl
  rw[σ₁_eq]
  exact i2Bound

/-%%
\begin{proof}\uses{I8I2, I2Bound}\leanok
  We deduce this from the corresponding bound for $I_2$, using the symmetry between $I_2$ and $I_8$.
\end{proof}
%%-/


/-%%
\begin{lemma}[I3Bound]\label{I3Bound}\lean{I3Bound}\leanok
We have that
$$
\left|I_{3}(\nu, \epsilon, X, T)\right| \ll \frac{X}{\epsilon}\, X^{-\frac{A}{(\log T)^9}}
.
$$
Same with $I_7$.
\end{lemma}
%%-/

theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        --(SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
        --(mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1),
        let σ₁ : ℝ := 1 - A / (Real.log T)
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
--  intro SmoothingF suppSmoothingF ContDiffSmoothingF
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded 9
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁ -- SmoothingFnonneg mass_one
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3

  have logXgt1 : Real.log X > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logTgt1 : Real.log T > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logX9gt1 : Real.log X ^ 1 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logXgt1
    linarith
    linarith

  have logT9gt1 : Real.log T ^ 1 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logTgt1
    linarith
    linarith

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      linarith[h2]
    have abs_tgt3 : 3 < |t| := by
      rw[this]
      linarith[h2]
    have abs_tltX : |t| < T := by
      rw[this]
      linarith[h1]
    exact ⟨abs_tgt3, abs_tltX⟩

  have logtgt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| > 1 := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine logt_gt_one ?_
    exact h1.le

  have logt9gt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9  > 1 := by
    intro t ht
    refine one_lt_pow₀ (logtgt1_bounds t ht) ?_
    linarith

  have logtltlogT_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| < Real.log T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have m := log_lt_log (by linarith : 0 < (|t|)) (h2 : |t| < T )
    exact m

  have logt9ltlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 < Real.log T ^ 9 := by
    intro t ht
    obtain h1 := logtltlogT_bounds t ht
    obtain h2 := logtgt1_bounds t ht
    have h3: 0 ≤ Real.log |t| := by linarith
    refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr h1
    linarith
    linarith
    linarith

  have Aoverlogt9gtAoverlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ 9 > A / Real.log T ^ 9 := by
    intro t ht
    have h1 := logt9ltlogT9_bounds t ht
    have h2 :=logt9gt1_bounds t ht
    refine div_lt_div_of_pos_left ?_ ?_ h1
    linarith [hA.1]
    linarith

  have AoverlogT9in0half: A / Real.log T ^ 1 ∈ Ioo 0 (1/2) := by
    constructor
    · refine div_pos ?_ ?_
      refine EReal.coe_pos.mp ?_
      exact EReal.coe_lt_coe hA.1
      linarith
    · refine (div_lt_comm₀ ?_ ?_).mpr ?_
      linarith
      linarith
      refine (div_lt_iff₀' ?_).mpr ?_
      linarith
      have hA_lt : A ≤ 1 / 2 := hA.2
      have hbound : 1 / 2 < (1 / 2) * Real.log T ^ 1 := by
        linarith
      linarith

  have σ₁lt2 : (σ₁ : ℝ) < 2 := by
    unfold σ₁
    calc 1 - A / Real.log T
      < 1 - 0 := by simp only [sub_zero]; exact sub_lt_self 1 (div_pos hA.1 (lt_trans zero_lt_one logTgt1))
      _ = 1 := by norm_num
      _ < 2 := by norm_num

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    calc 1 - A / Real.log T
      < 1 - 0 := by simp only [sub_zero]; exact sub_lt_self 1 (div_pos hA.1 (by linarith [logTgt1]))
      _ = 1 := by norm_num

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    rw [sub_pos]
    calc
      A / Real.log T ≤ (1/2) / Real.log T := by
        apply div_le_div_of_nonneg_right hA.2 (by linarith)
      _ ≤ (1/2) / 1 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ = 1/2 := by norm_num
      _ < 1 := by norm_num

  have quotient_bound : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ 9/ t ^ 2  := by
    intro t ht
    have loght := logt9gt1_bounds t ht
    have logpos : Real.log |t| ^ 9 > 0 := by linarith
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    have denom_pos : 0 < t ^ 2 := by
      have : t ^ 2 = |t| ^ 2 := by
        exact Eq.symm (sq_abs t)
      rw [this]
      have h1 := ht.1
      have abspos : |t| > 0 := by linarith
      exact sq_pos_of_pos abspos
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have boundthing : ∀ t, 3 < |t| ∧ |t| < T → σ₁ ∈ Ici (1 - A / Real.log |t|) := by
    intro t ht
    have h1 := Aoverlogt9gtAoverlogT9_bounds t ht
    unfold σ₁
    apply mem_Ici.mpr
    ring_nf
    -- We need to show: 1 - A / log T ≥ 1 - A / log |t|
    -- Equivalently: A / log |t| ≥ A / log T
    -- Since A > 0 and log T < log |t| (because |t| < T), this follows
    apply sub_le_sub_left
    have : Real.log |t| ≤ Real.log T := by
      apply Real.log_le_log (by linarith) (le_of_lt ht.2)
    exact div_le_div_of_nonneg_left (le_of_lt hA.1) (Real.log_pos (by linarith)) this

  have : ∫ (t : ℝ) in -T..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) = ∫ (t : ℝ) in Ioo (-T : ℝ) (-3 : ℝ),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.integral_Ioc_eq_integral_Ioo
  rw[this]

  have MellinBound : ∀ (t : ℝ) , ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    apply CMhyp σ₁
    exact σ₁pos
    dsimp
    ring_nf
    rfl
    dsimp
    ring_nf
    linarith
    exact εgt0
    exact εlt1

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ 9 := by
    intro t tbounds
    obtain ⟨tgt3, tltT⟩ := tbounds
    apply hCζ
    · exact tgt3
    · apply boundthing
      constructor
      · exact tgt3
      · exact tltT

  have Mellin_bd : ∀ t, 3 < |t| ∧ |t| < T →
  ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖σ₁ + t * I‖ ^ 2)⁻¹ := by
    intro t ht
    apply MellinBound

  have logzeta_bd : ∀ t, 3 < |t| ∧ |t| < T →
    ‖ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)‖ ≤ Cζ * Real.log |t| ^ 9 := by
    intro t t_bounds
    obtain ⟨abs_tgt3,abs_tltX⟩ := t_bounds
    apply logzetabnd
    constructor
    · exact abs_tgt3
    · exact abs_tltX
  have : ‖1 / (2 * ↑π * I) *
        (I * ∫ (t : ℝ) in -X..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑T ^ (↑σ₁ + ↑t * I))‖
    =
    (1 / (2 * π)) * ‖∫ (t : ℝ) in -X..-3,
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑T ^ (↑σ₁ + ↑t * I)‖ := by
    simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
    rw[Complex.norm_I]
    simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
    have : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by
      dsimp
      ring_nf
      simp only [norm_mul, norm_eq_abs, abs_neg, abs_one, one_mul, mul_one]
      rw[inv_I]
      have : ‖-I‖ = ‖-1 * I‖ := by
        simp
      rw[this]
      have : ‖-1 * I‖ = ‖-1‖ * ‖I‖ := by
        simp
      rw[this, Complex.norm_I]
      ring_nf
      simp
      exact pi_nonneg
    rw[this]

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have norm_X_sigma1: ∀ (t : ℝ), ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
    intro t
    have Xpos : 0 < X := by linarith
    have : ((↑σ₁ + ↑t * I).re) = σ₁ := by
      dsimp
      ring_nf
    nth_rw 2[← this]
    apply Complex.norm_cpow_eq_rpow_re_of_pos Xpos

  have bound_integral : ∀ (t : ℝ), 3  < |t| ∧ |t| < T → ‖f t‖ ≤ g t := by
    intro t
    rintro ⟨ht_gt3, ht_ltT⟩
    have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := norm_X_sigma1 t
    have logtgt1 : 1 < Real.log |t| := by
        exact logt_gt_one ht_gt3.le
    have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
    have h𝓜 := MellinBound t
    have : ‖f ↑t‖ = ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ := by
      rfl
    rw[this]
    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ 9) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      rw[Xσ_bound]
      gcongr
    have : (Cζ * Real.log |t| ^ 9) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f: ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I))‖ = ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          f t)‖ := by
      unfold f
      simp
  rw[int_with_f]
  apply (norm_mul_le _ _).trans
  have int_mulbyI_is_int : ‖I * ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ = ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    rw [Complex.norm_mul, Complex.norm_I]
    ring
  rw[int_mulbyI_is_int]

  have norm_1over2pii_le1: ‖1 / (2 * ↑π * I)‖ ≤ 1 := by
    simp
    have pi_gt_3 : Real.pi > 3 := by
      exact pi_gt_three
    have pi_pos : 0 < π := by linarith [pi_gt_3]
    have abs_pi_inv_le : |π|⁻¹ ≤ (1 : ℝ) := by
      rw [abs_of_pos pi_pos]
      have h : 1 = π * π⁻¹ := by
        field_simp
      rw[h]
      nth_rw 1 [← one_mul π⁻¹]
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact inv_nonneg.mpr (le_of_lt pi_pos)
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_half_le_one : (2 : ℝ)⁻¹ ≤ 1 := by norm_num
    linarith

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · exact norm_1over2pii_le1
  apply le_trans this
  have : ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑ t‖ := by
    apply norm_integral_le_integral_norm
  apply le_trans this

  have norm_f_nonneg: ∀ t, ‖f t‖ ≥ 0 := by
    exact fun t ↦ norm_nonneg (f t)

  have g_cont : ContinuousOn g (Icc (-T) (-3)) := by
    unfold g
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_const
    · exact continuousOn_const
    · refine ContinuousOn.pow ?_ 9
      refine ContinuousOn.log ?_ ?_
      · refine Continuous.continuousOn ?_
        exact _root_.continuous_abs
      · intro t ht
        have h1 := ht.1
        have h2 := ht.2
        by_contra!
        have : t = 0 := by
          exact abs_eq_zero.mp this
        rw[this] at h2
        absurd
        h2
        linarith
    · refine ContinuousOn.inv₀ ?_ ?_
      · refine ContinuousOn.mul ?_ ?_
        · exact continuousOn_const
        · refine ContinuousOn.pow ?_ 2
          refine ContinuousOn.norm ?_
          refine ContinuousOn.add ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.mul ?_ ?_
            · refine continuousOn_of_forall_continuousAt ?_
              intro x hx
              exact continuous_ofReal.continuousAt
            · exact continuousOn_const
      · intro x hx
        have norm_sq_pos : ‖(σ₁ : ℂ) + x * Complex.I‖ ^ 2 = σ₁ ^ 2 + x ^ 2 := by
          rw [Complex.sq_norm]
          exact normSq_add_mul_I σ₁ x
        have : 0 < σ₁ ^ 2 + x ^ 2 := by
          apply add_pos_of_pos_of_nonneg
          · exact sq_pos_of_pos σ₁pos
          · exact sq_nonneg x
        apply mul_ne_zero
        · linarith
        · rw [norm_sq_pos]
          exact ne_of_gt this
    · exact continuousOn_const

  have g_integrable_Icc : IntegrableOn g (Icc (-T) (-3)) volume := by
    exact ContinuousOn.integrableOn_Icc g_cont

  have g_integrable_Ioo : IntegrableOn g (Ioo (-T) (-3)) volume := by
    apply MeasureTheory.IntegrableOn.mono_set g_integrable_Icc
    exact Ioo_subset_Icc_self

  have int_normf_le_int_g: ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in Ioo (-T) (-3), g ↑t := by

    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · have f_int : IntegrableOn (fun (t : ℝ) ↦ ‖f t‖) (Ioo (-T : ℝ) (-3 : ℝ)) volume := by
        have hle : -T ≤ -3 := by linarith
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp h_int
      apply MeasureTheory.setIntegral_mono_on
      exact f_int
      exact g_integrable_Ioo
      exact measurableSet_Ioo
      intro t ht
      apply bound_integral
      have : |t| = -t := by
        refine abs_of_neg ?_
        linarith [ht.2]
      have abs_tgt3 : 3 < |t| := by
        rw[this]
        linarith[ht.2]
      have abs_tltX : |t| < T := by
        rw[this]
        linarith[ht.1]
      constructor
      · linarith
      · linarith
    · have : ∫ (t : ℝ) in -T..-3, ‖f ↑ t‖ = ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖  := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      have : ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖ = 0 := by
        rw [← this]
        exact intervalIntegral.integral_undef h_int
      rw [this]
      apply MeasureTheory.setIntegral_nonneg
      · exact measurableSet_Ioo
      · intro t ht
        have abst_negt : |t| = -t := by
          refine abs_of_neg ?_
          linarith [ht.2]
        have tbounds1 : 3 < |t| ∧ |t| < T := by
          rw[abst_negt]
          constructor
          · linarith [ht.2]
          · linarith [ht.1]
        unfold g
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        · linarith
        · linarith
        · have : 0 ≤ Real.log |t| := by
            apply Real.log_nonneg
            linarith [tbounds1.1]
          positivity
        · field_simp
          apply div_nonneg
          · linarith
          · apply mul_nonneg
            · linarith
            · rw [Complex.sq_norm]
              exact normSq_nonneg (↑σ₁ + ↑t * I)
        · apply Real.rpow_nonneg
          linarith

  apply le_trans int_normf_le_int_g
  unfold g

  have : X ^ σ₁ = X ^ (1 - A / Real.log T ) := by
    rfl
  rw[this]

  have : X ^ (1 - A / Real.log T) = X * X ^ (- A / Real.log T) := by
    have hX : X > 0 := by linarith
    simp only [Real.rpow_sub hX, Real.rpow_one]
    have h₁ : X ^ (-A / Real.log T) * X ^ (A / Real.log T) = 1 := by
      rw [← Real.rpow_add hX]
      ring_nf
      exact rpow_zero X
    field_simp
    rw[mul_assoc, h₁]
    ring

  rw[this]


  have Bound_of_log_int: ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]
    have normsquared : ∀ (t : ℝ), ‖↑σ₁ + ↑t * I‖ ^ 2 = σ₁ ^ 2 + t ^ 2 := by
      intro t
      simp only [Complex.sq_norm]
      exact normSq_add_mul_I σ₁ t

    have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2
          = ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) := by
      simp_rw [normsquared]

    have bound : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      rw [this]
      have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 /  t ^ 2 := by
        refine setIntegral_mono_on ?_ ?_ ?_ ?_
        ·
          have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have h2 : t ≠ 0 := by linarith
              have h3 : 0 < t ^ 2 := pow_two_pos_of_ne_zero h2
              have h4 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              linarith [h3, h4]
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have tne0 : t ≠ 0 := by linarith
              exact pow_ne_zero 2 tne0
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · exact measurableSet_Ioo
        · intro x hx
          have xneg : x < 0 := by linarith[hx.2]
          have absx : |x| = -x := abs_of_neg xneg
          have h1 : 3 < |x| ∧ |x| < T := by
            rw[absx]
            constructor
            · linarith [hx.2]
            · linarith [hx.1]
          exact quotient_bound x (t_bounds x hx)
      apply le_trans this
      have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
            = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
        have eq_integrand : ∀ (t : ℝ), t ∈ Ioo (-T) (-3) → (Real.log |t|) ^ 9 / t ^ 2 = (Real.log (-t)) ^ 9 / (-t) ^ 2 := by
          intro t ht
          have tneg : t < 0 := by linarith[ht.2]
          have : |t| = -t := abs_of_neg tneg
          rw [this, neg_sq]

        have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
              = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo eq_integrand

        rw [this]

        have interval_to_Ioo1 : ∫ (t : ℝ) in -T..-3, Real.log (-t) ^ 9 / (-t) ^ 2
                        = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        have interval_to_Ioo2 : ∫ (t : ℝ) in (3)..(T), Real.log t ^ 9 / t ^ 2
                    = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        rw [← interval_to_Ioo1, ← interval_to_Ioo2]
        rw [intervalIntegral.integral_comp_neg (fun (t : ℝ) ↦ Real.log (t) ^ 9 / (t) ^ 2)]
        simp
      rw [this]
      have : ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 < Cint := by
        exact Cinthyp T Tgt3
      linarith
    rw [ mul_comm]
    rw [← mul_div_assoc, mul_one]
    exact (div_le_div_iff_of_pos_right εgt0).mpr bound


  have factor_out_constants :
  ∫ (t : ℝ) in Ioo (-T) (-3), Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ))
  = Cζ * CM * (X * X ^ (-A / Real.log T)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     rw [← integral_const_mul]
     apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
     intro t ht
     ring

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · have hpos : 0 < X * X ^ (-A / Real.log T) := by
        apply mul_pos
        · linarith
        · apply Real.rpow_pos_of_pos
          linarith
      apply mul_nonneg
      · apply mul_nonneg
        · linarith
        · linarith
      · linarith [hpos]

  apply le_trans this
  ring_nf
  field_simp


lemma I7Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2))
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
  obtain ⟨C, Cpos, bound⟩ := I3Bound suppSmoothingF ContDiffSmoothingF hCζ Cζpos hA
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]
/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBnd, IntegralofLogx^n/x^2Bounded, I3, I7}\leanok
Unfold the definitions and apply the triangle inequality.
$$
\left|I_{3}(\nu, \epsilon, X, T, \sigma_1)\right| =
\left|\frac{1}{2\pi i} \int_{-T}^3
\left(\frac{-\zeta'}\zeta(\sigma_1 + t i) \right)
\mathcal M(\widetilde 1_\epsilon)(\sigma_1 + t i)
X^{\sigma_1 + t i}
\ i \ dt
\right|
$$
$$\leq
\frac{1}{2\pi}
\int_{-T}^3
C \cdot \log t ^ 9
\frac{C'}{\epsilon|\sigma_1 + t i|^2}
X^{\sigma_1}
 \ dt
,
$$
where we used Theorems \ref{MellinOfSmooth1b} and \ref{LogDerivZetaBnd}.
Now we estimate $X^{\sigma_1} = X \cdot X^{-A/ \log T^9}$, and the integral is absolutely bounded.
\end{proof}
%%-/



/-%%
\begin{lemma}[I4Bound]\label{I4Bound}\lean{I4Bound}\leanok
We have that
$$
\left|I_{4}(\nu, \epsilon, X, \sigma_1, \sigma_2)\right| \ll \frac{X}{\epsilon}\,
 X^{-\frac{A}{(\log T)^9}}
.
$$
Same with $I_6$.
\end{lemma}
%%-/

lemma I4Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    --(SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    --(mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} --{Cζ : ℝ} --(hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ)
    (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by

  have reOne : re 1 = 1 := by exact rfl
  have imOne : im 1 = 0 := by exact rfl
  have reThree : re 3 = 3 := by exact rfl
  have imThree : im 3 = 0 := by exact rfl

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  unfold I₄ SmoothedChebyshevIntegrand

  let S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1
  let C' : ℝ := sSup S
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -(ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        ((ζ' / ζ) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by exact rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, mem_diff, mem_singleton_iff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        have : -3 ≠ 0 := by norm_num
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  obtain ⟨D, Dpos, MellinSmooth1bBound⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  let C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)
  use C
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnnorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := by exact temp
        positivity
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert sInfPos.le using 5
      norm_cast
  use CNonneg

  let Tlb : ℝ := max 4 (max (rexp A) (rexp (A / (1 - σ₂))))
  use Tlb

  have : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  use this

  intro X X_gt_three ε ε_pos ε_lt_one

  intro T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := by exact le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb := by
      have : rexp (A / (1 - σ₂)) ≤ Tlb := by
        unfold Tlb
        apply le_max_of_le_right
        apply le_max_right
      rw[← Real.le_log_iff_exp_le] at this
      · rw[div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · linarith
        · exact logTlb_pos
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ≤ 1 - A / Real.log T := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · exact logTlb_pos
      · apply log_le_log (by positivity)
        exact le_of_lt (by exact T_gt_Tlb)
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := by exact min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := by exact max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T) / ε = 1 * (C * X * X ^ (-A / Real.log T) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg, Complex.norm_I, mul_one]
    have : 1 / (2 * π) < 1 / 6 := by
      rw[one_div_lt_one_div]
      · refine (div_lt_iff₀' ?_).mp ?_
        norm_num
        ring_nf
        refine gt_iff_lt.mpr ?_
        exact Real.pi_gt_three
      · positivity
      · norm_num
    apply le_of_lt
    exact lt_trans this (by norm_num)
    exact pi_nonneg
  · let f : ℝ → ℂ := fun σ ↦ (-ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul, norm_neg]
        have : C * X * X ^ (-A / Real.log T) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T)) := by ring
        rw[this]
        have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I) =
              𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s := by exact rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]

                · have one_inv: (1⁻¹ : ℝ) = ( 1 : ℝ) := by norm_num
                  rw[zero_mul, neg_zero, Real.exp_zero, one_inv, mul_one]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    rw [←div_eq_mul_inv]
                    ring_nf at xInIoc ⊢
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  simp only [norm_nonneg]
  norm_num


lemma I6Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    --(SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    --(mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} --{A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ)
    (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
  obtain ⟨C, Cpos, Tlb, Tlb_gt, bound⟩ := I4Bound suppSmoothingF ContDiffSmoothingF h_logDeriv_holo hσ₂ hA
  refine ⟨C, Cpos, Tlb, Tlb_gt, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]

/-%%
\begin{proof}\uses{MellinOfSmooth1b, LogDerivZetaBndAlt, I4, I6}\leanok
The analysis of $I_4$ is similar to that of $I_2$, (in Lemma \ref{I2Bound}) but even easier.
Let $C$ be the sup of $-\zeta'/\zeta$ on the curve $\sigma_2 + 3 i$ to $1+ 3i$ (this curve is compact, and away from the pole at $s=1$).
Apply Theorem \ref{MellinOfSmooth1b} to get the bound $1/(\epsilon |s|^2)$, which is bounded by $C'/\epsilon$.
And $X^s$ is bounded by $X^{\sigma_1} = X \cdot X^{-A/ \log T^9}$.
Putting these together gives the result.
\end{proof}
%%-/


lemma LogDerivZetaBoundedAndHolo : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound A C
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
    exact (le_trans hmain this)
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
    simp [mem_reProdIm] at hs ⊢
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
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  ⟨σ₂_pos, σ₂_lt_one⟩
  obtain ⟨c₇, c₇pos, hc₇⟩ := I7Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₈, c₈pos, hc₈⟩ := I8Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne

  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc

  obtain ⟨c₆, c₆pos, Tlb₆, Tlb₆bnd, hc₆⟩ := I6Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc

  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇


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
      div_pos_iff_of_pos_right, div_pos_iff_of_pos_left, σ₂, c, c_εx]
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
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _

  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) := by
    --have' := (tendsto_order.mp ?_).1
    apply (tendsto_order.mp ?_).1
    · exact σ₂_lt_one
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp [Function.comp, pow_one, div_eq_mul_inv]
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
            -- linarith
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
      --positivity -- fails?? Worked before
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
    have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
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
    rw [mul_le_mul_left c₅pos]
    apply Real.exp_monotone
    convert hx

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
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4

  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge zeta_bnd
    -- ν_nonneg ν_massOne ContDiff1ν ν_supp

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
    simpa [σ₁, pow_one] using holo1

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
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1_compat ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂_pos σ₁_lt_one σ₂_lt_σ₁ holo1_compat holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    apply le_trans (by apply norm_add_le)
    rw [(by ring : ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ =
      (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖) + (‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖))]
    gcongr <;> apply le_trans (by apply norm_sub_le) <;> rfl
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
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]

  have C'''bnd : c₃ * X * X ^ (-A / Real.log T) / ε
                    + c₄ * X * X ^ (-A / Real.log T) / ε
                    + c₆ * X * X ^ (-A / Real.log T) / ε
                    + c₇ * X * X ^ (-A / Real.log T) / ε
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
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T) / ε
                  + c₇ * X * X ^ (-A / Real.log T) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert h_close using 1
      rw [← norm_neg]
      congr
      ring

      -- unfold σ₁
      change ‖I₂ ν ε (Tx X) X σ₁‖ ≤ c₂ * X / (ε * (Tx X))
      dsimp at hc₂
      dsimp [σ₁]
      -- have : sigma1Of = 1 - A / Real.log T := rfl
      unfold sigma1Of at hc₂


      -- dsimp [Tx] at hc₂

      exact hc₂


    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε
                  + c₆ * X * X ^ (-A / Real.log T) / ε
                  + c₇ * X * X ^ (-A / Real.log T) / ε)
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
