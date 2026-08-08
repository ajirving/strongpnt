import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.ExponentialBounds
import StrongPNT.PNT1_ComplexAnalysis
import Mathlib.Tactic.Cases

def zerosetKfR (R : ℝ) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}

open Filter Metric Set Bornology Function

/-! ### The quotient `Cf` (no core wrapper) -/

open scoped Topology ComplexConjugate

lemma trailingCoeff_def {f : ℂ → ℂ} {z : ℂ} (h1 : AnalyticAt ℂ f z)
    (h2 : analyticOrderAt f z ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ meromorphicTrailingCoeffAt f z = g z
    ∧ f =ᶠ[𝓝 z] fun z_1 ↦ (z_1 - z) ^ analyticOrderNatAt f z * g z_1 := by
  obtain ⟨hg1, hg2, hg3⟩ := (h1.analyticOrderAt_ne_top.mp h2).choose_spec
  set g := (h1.analyticOrderAt_ne_top.mp h2).choose
  refine ⟨g, hg1, hg2, ?_, (by simpa)⟩
  simp_rw [← zpow_natCast] at hg3
  rw [hg1.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hg2 (eventually_nhdsWithin_of_eventually_nhds hg3)]

lemma order_ne_top {f : ℂ → ℂ} {r : ℝ} {z : ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hr : 0 ≤ r)
    (ne : ∃ z' ∈ closedBall (0 : ℂ) r, f z' ≠ 0) (hz : z ∈ closedBall 0 r) :
    analyticOrderAt f z ≠ ⊤ := by
  rcases ne with ⟨z', hz'⟩
  refine hf.analyticOrderAt_ne_top_of_isPreconnected (isConnected_closedBall hr).isPreconnected hz'.1 hz ?_
  simp [AnalyticAt.analyticOrderAt_eq_zero (hf z' hz'.1)|>.mpr hz'.2]

open Classical in
/-- The “deflated” quotient: divide `f` by the product of `(z-ρ)^{m_ρ}`, and at a zero `z=σ`
    use the local factor function `h_σ σ` in the numerator (so the expression extends analytically). -/
noncomputable def Cf
    (R1 : ℝ)
    (f : ℂ → ℂ)
    (z : ℂ) : ℂ :=
if h_finite_zeros : (zerosetKfR R1 f).Finite then
    if _ : z ∈ zerosetKfR R1 f then
      meromorphicTrailingCoeffAt f z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase z), (z - ρ) ^ analyticOrderNatAt f ρ
    else
      f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ
  else
    1

/-! ### Helper lemmas used by the Cf proofs (statements only) -/

lemma lem_denomAnalAt (S : Finset ℂ) (n : ℂ → ℕ)
    (w : ℂ) (hw : w ∉ S) :
    AnalyticAt ℂ (fun z => ∏ s ∈ S, (z - s) ^ (n s)) w ∧
    (∏ s ∈ S, (w - s) ^ (n s)) ≠ 0 := by
  constructor
  · fun_prop
  · -- Second part: nonzero product
    apply Finset.prod_ne_zero_iff.mpr fun s hs ↦ pow_ne_zero _ ?_
    grind

lemma lem_ratioAnalAt (w : ℂ)
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h w)
    (S : Finset ℂ) (n : ℂ → ℕ)
    (hw : w ∉ S) :
    AnalyticAt ℂ (fun z => h z / ∏ s ∈ S, (z - s) ^ (n s)) w := by
  have hden := lem_denomAnalAt S n w hw
  exact hh.div hden.1 hden.2

/-! ### Cf lemmas (renamed to use `Cf` directly) -/



lemma lem_prod_no_sigma1
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 f) (z : ℂ) :
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ =
    (z - σ) ^ analyticOrderNatAt f σ *
    ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ analyticOrderNatAt f ρ := by
  exact Finset.mul_prod_erase _ _ (h_finite_zeros.mem_toFinset.2 hσ)|>.symm

lemma lem_Cf_at_sigma
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 f) (hfσ : AnalyticAt ℂ f σ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g σ ∧ ∀ᶠ z in nhds σ,
      Cf R1 f z =
      g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ analyticOrderNatAt f ρ := by
  by_cases top : analyticOrderAt f σ = ⊤
  · refine ⟨0, analyticAt_const, ?_⟩
    have f_eq_zero := analyticOrderAt_eq_top.mp top
    have trailing_eq_zero : ∀ᶠ (z : ℂ) in nhds σ, meromorphicTrailingCoeffAt f z = 0 := by
      filter_upwards [eventually_eventually_nhds.mpr f_eq_zero] with z eq_zero
      apply MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
      exact meromorphicOrderAt_eq_top_iff.mpr <| eventually_nhdsWithin_of_eventually_nhds eq_zero
    filter_upwards [f_eq_zero, trailing_eq_zero] with z f_eq_zero trailing_eq_zero
    simp [Cf, trailing_eq_zero, f_eq_zero, h_finite_zeros]
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := trailingCoeff_def hfσ top
  refine ⟨g, hg1, ?_⟩
  filter_upwards [hg1.continuousAt.eventually_ne hg2, hg4] with z ne_zero f_eq
  by_cases! h : z = σ
  · simp [Cf, hσ, h, hg3, h_finite_zeros]
  · have : f z ≠ 0 := by
      rw [f_eq]
      apply mul_ne_zero (pow_ne_zero _ (by grind)) ne_zero
    have : z ∉ zerosetKfR R1 f := by
      simp [zerosetKfR, this]
    simp only [Cf, h_finite_zeros, ↓reduceDIte, this, f_eq]
    rw [lem_prod_no_sigma1 h_finite_zeros σ hσ, mul_div_mul_left]
    grind

lemma lem_h_ratio_anal
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (σ : ℂ)
    (g : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g σ) :
    AnalyticAt ℂ
      (fun z => g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (z - ρ) ^ analyticOrderNatAt f ρ) σ := by
  have hden := lem_denomAnalAt (h_finite_zeros.toFinset.erase σ) (fun ρ => analyticOrderNatAt f ρ) σ
    (hw := by
      simp [Finset.mem_erase])
  exact hg_analytic.div hden.1 hden.2

lemma lem_Cf_analytic {R R1 : ℝ} {f : ℂ → ℂ} (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    AnalyticAt ℂ (Cf R1 f) z := by
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · unfold Cf
    simp [h_finite_zeros, analyticAt_const]
  by_cases h : z ∈ zerosetKfR R1 f
  · obtain ⟨g, hg1, hg2⟩ := lem_Cf_at_sigma h_finite_zeros z h (h_f_analytic z hz)
    apply analyticAt_congr hg2|>.mpr
    exact lem_h_ratio_anal h_finite_zeros _ _ hg1
  · have h_ratio_analytic : AnalyticAt ℂ (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ) z := by
      apply lem_ratioAnalAt z f (h_f_analytic _ hz)
      simp_all
    refine h_ratio_analytic.congr ?_
    have h_open : IsOpen (Set.compl (zerosetKfR R1 f)) := h_finite_zeros.isClosed.isOpen_compl
    apply Filter.eventually_of_mem (h_open.mem_nhds h)
    intro w hw_not_in_compl
    -- Convert from membership in complement to non-membership
    have hw_not_in_zeros : w ∉ zerosetKfR R1 f := hw_not_in_compl
    -- Since w ∉ zerosetKfR R1, Cf w uses the else branch
    change f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ =
         Cf R1 f w
    -- Apply the definition of Cf using dif_neg for dependent if-then-else
    simp [Cf, h_finite_zeros, hw_not_in_zeros]

lemma lem_Cf_never_zero
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (ne_top : ∀ z ∈ closedBall 0 R1, analyticOrderAt f z ≠ ⊤)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1) :
    Cf R1 f z ≠ 0 := by
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · simp [Cf, h_finite_zeros]
  by_cases h : z ∈ zerosetKfR R1 f <;> simp only [Cf, ↓reduceDIte, h, h_finite_zeros]
  · refine  div_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦ pow_ne_zero _ (by grind))
    apply (hf z hz).meromorphicAt.meromorphicTrailingCoeffAt_ne_zero
    rw [(hf z hz).meromorphicOrderAt_eq]
    simp_all
  · exact div_ne_zero (by simp_all [zerosetKfR])
      (Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦ pow_ne_zero _ fun _ ↦ (by simp_all [zerosetKfR, sub_eq_zero]))

open Classical in
noncomputable def Bf
    (R R1 : ℝ)
    (f : ℂ → ℂ)
    (z : ℂ) : ℂ :=
  if h_finite_zeros : (zerosetKfR R1 f).Finite then
    Cf R1 f z *
    ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - conj ρ * z / (R : ℂ)) ^ analyticOrderNatAt f ρ
  else
    1

lemma lem_mod_Bf_prod_mod (R R1 : ℝ)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (z : ℂ)
    (hz : z ∉ zerosetKfR R1 f) :
  ‖Bf R R1 f z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * conj ρ / (R : ℂ)) / (z - ρ))‖ ^ analyticOrderNatAt f ρ := by
  simp only [Bf, h_finite_zeros, ↓reduceDIte, norm_mul, norm_prod]
  simp only [Cf, hz, ↓reduceDIte, h_finite_zeros, norm_div, norm_prod]
  rw [div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib]
  congr 2
  ext ρ
  rw [← norm_div, ← norm_div, ← norm_pow, div_pow]
  ring_nf

theorem lem_mod_Bf_at_0_as_ratio (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ‖Bf R R1 f 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
  rw [lem_mod_Bf_prod_mod R R1 f h_finite_zeros 0 (by simp_all [zerosetKfR])]
  congr 2
  ext
  simp [div_pow, abs_of_nonneg (by linarith : 0 ≤ R)]


theorem lem_mod_Bf_at_0_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ‖Bf R R1 f 0‖ ≥ 1 := by
  rw [lem_mod_Bf_at_0_as_ratio R R1 hR1_pos hR1_lt_R f (by simp_all) h_finite_zeros]
  rw [hf0_eq_one, norm_one, one_mul]
  refine Finset.one_le_prod fun ρ hρ ↦ one_le_pow₀ ?_
  simp only [zerosetKfR, mem_closedBall, dist_zero_right, Finite.mem_toFinset, mem_setOf_eq] at hρ
  refine one_le_div ?_|>.mpr (hρ.1.trans hR1_lt_R.le)
  exact norm_pos_iff.mpr fun h ↦ (by simp_all)

theorem lem_Bf_is_analytic (R R1 : ℝ)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    AnalyticOnNhd ℂ (Bf R R1 f)  (closedBall (0 : ℂ) R) := by
  intro z hz
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · unfold Bf
    simp [h_finite_zeros, analyticAt_const]
  have h_product : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - conj ρ * w / (R : ℂ)) ^ analyticOrderNatAt f ρ) z := by
    fun_prop
  unfold Bf
  simp only [h_finite_zeros, ↓reduceDIte]
  exact (lem_Cf_analytic h_f_analytic hz).mul h_product

lemma lem_mod_Bf_eq_mod_f_on_boundary (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (z : ℂ) (hz : ‖z‖ = R) :
      ‖Bf R R1 f z‖ = ‖f z‖ := by
  rw [lem_mod_Bf_prod_mod R R1 f h_finite_zeros z (by simp_all [zerosetKfR])]
  suffices ∀ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * conj ρ / (R : ℂ)) / (z - ρ))‖ ^ analyticOrderNatAt f ρ = 1 by
    rw [Finset.prod_congr rfl this, Finset.prod_const_one, mul_one]
  intro ρ hρ
  convert one_pow _
  have z_ne_rho : z ≠ ρ := by
    intro h_eq
    simp_all [zerosetKfR]
    linarith
  rw [(by field : R - z * conj ρ / R = ((R : ℂ)^2 - z * conj ρ) / R)]
  rw [← hz, ← Complex.mul_conj', ← mul_sub, ← map_sub]
  simp only [Complex.norm_div, Complex.norm_mul, Complex.norm_real, norm_norm, Complex.norm_conj]
  rw [div_div, div_self]
  exact mul_ne_zero (by linarith) (norm_ne_zero_iff.mpr (by grind))

lemma lem_Bf_bounded_on_boundary (B R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ = R) :
      ‖Bf R R1 f z‖ ≤ B := by
  rw [lem_mod_Bf_eq_mod_f_on_boundary R R1 (by linarith) hR1_lt_R f h_finite_zeros z hz]
  exact hf_le_B _ hz.le

lemma lem_max_mod_principle_for_Bf (B R : ℝ) (hR_pos : 0 < R)
    (fB : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ fB (closedBall (0 : ℂ) R))
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R → ‖fB z‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ R) : ‖fB z‖ ≤ B := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := 0) (r := R)) ?_ (fun z hz ↦ ?_) ?_
  · apply DifferentiableOn.diffContOnCl
    apply AnalyticOnNhd.differentiableOn
    convert h_analytic
    exact closure_ball _ (by linarith)
  · apply h_bd_boundary
    rw [frontier_ball _ (by linarith)] at hz
    simp_all
  · rw [closure_ball _ (by linarith)]
    simp_all

lemma lem_Bf_bounded_in_disk_from_boundary (B R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 f z‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
      ‖Bf R R1 f z‖ ≤ B := by
  exact lem_max_mod_principle_for_Bf B R (by linarith)
    (Bf R R1 f) (lem_Bf_is_analytic R R1 f h_f_analytic) h_bd_boundary z hz

lemma lem_Bf_bounded_in_disk_from_f (B R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
      ‖Bf R R1 f z‖ ≤ B := by
  exact lem_Bf_bounded_in_disk_from_boundary B R R1 hR1_pos hR1_lt_R f h_f_analytic (lem_Bf_bounded_on_boundary B R R1 hR1_pos hR1_lt_R f h_finite_zeros hf_le_B) z hz

lemma lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ)) ≤ (1/Real.log (R/R1)) * Real.log B := by
  rw [← abs_of_nonneg (by linarith : 0 ≤ R)] at h_f_analytic
  convert  AnalyticOnNhd.sum_divisor_le (by grind : 0 < |R1|) (by grind) hB.le h_f_analytic (by grind) _ using 1
  · rw [finsum_eq_finsetSum_of_support_subset (s := h_finite_zeros.toFinset)]
    · push_cast
      refine Finset.sum_congr rfl (fun z hz ↦ ?_)
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (h_f_analytic.mono (by gcongr))]
      · norm_cast
        unfold analyticOrderNatAt
        cases analyticOrderAt f z <;> simp
      · rw [abs_of_nonneg (by linarith)]
        simp_all [zerosetKfR]
    · intro z hz
      simp_all only [mem_support, MeromorphicOn.divisor_def, mem_closedBall, dist_zero_right, ne_eq,
        ite_eq_right_iff, WithTop.untop₀_eq_zero, and_imp, Classical.not_imp, not_or, zerosetKfR,
        Finite.coe_toFinset, mem_setOf_eq]
      rw [abs_of_pos (by linarith)] at hz
      refine ⟨hz.2.1, apply_eq_zero_of_analyticOrderAt_ne_zero ?_⟩
      rw [(h_f_analytic _ (by simp; grind)).meromorphicOrderAt_eq] at hz
      simp_all
  · simp_all; ring
  · intro z hz
    apply hf_le_B
    simp_all only [mem_sphere_iff_norm, sub_zero]
    grind

variable {R R1 r B : ℝ} {f : ℂ → ℂ}
variable (h_finite_zeros : (zerosetKfR R1 f).Finite)

lemma lem_num_prod_never_zero_all
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1) :
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - conj ρ * z / (R : ℂ)) ^ analyticOrderNatAt f ρ) ≠ 0 := by
  refine  Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦ pow_ne_zero _ ?_
  apply norm_pos_iff.mp
  grw [norm_sub_norm_le _ _|>.ge]
  rw [Complex.norm_of_nonneg (by linarith), norm_div, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg (by linarith)]
  have hR_pos : (0 : ℝ) < R := by linarith
  grw [(by simp_all [zerosetKfR] : ‖ρ‖ ≤ R1), (by simp_all : ‖z‖ ≤ R1)]
  have h1 : R1 * R1 < R * R := by gcongr
  have h2 : R1 * R1 / R < R := by
    rwa [div_lt_iff₀ hR_pos]
  linarith

lemma Bf_never_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (ne_top : ∀ z ∈ closedBall 0 R1, analyticOrderAt f z ≠ ⊤)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1) : Bf R R1 f z ≠ 0 := by
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · simp [Bf, h_finite_zeros]
  simp only [Bf, h_finite_zeros, ↓reduceDIte]
  exact mul_ne_zero (lem_Cf_never_zero hf ne_top z hz) (lem_num_prod_never_zero_all R R1 hR1_pos hR1_lt_R f h_finite_zeros z hz)

def isLf (Lf : ℂ → ℂ) (f : ℂ → ℂ) (r R R1 : ℝ) : Prop :=
    AnalyticOnNhd ℂ Lf (closedBall 0 r) ∧ Lf 0 = 0 ∧
    (∀ z ∈ closedBall (0 : ℂ) r, deriv Lf z = logDeriv (Bf R R1 f) z) ∧
    ∀ z ∈ closedBall (0 : ℂ) r, (Lf z).re = Real.log (norm (Bf R R1 f z)) - Real.log (norm (Bf R R1 f 0))

lemma re_Lf_le_log_B
    (B r R R1 : ℝ)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bound : ∀ z, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (Lf : ℂ → ℂ)
    (hLf : isLf Lf f r R R1)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
      Complex.re (Lf z) ≤ Real.log B := by
  rw [hLf.2.2.2 _ (by simp_all)]
  have : Real.log ‖Bf R R1 f z‖ ≤ Real.log B := by
    gcongr
    · refine norm_pos_iff.mpr ?_
      apply Bf_never_zero R R1 hR1_pos hR1_lt_R f
      · exact fun z hz ↦ h_f_analytic z (closedBall_subset_closedBall (by linarith) hz)
      · exact fun z hz ↦ order_ne_top h_f_analytic (by linarith) ⟨0, (by simp; linarith), (by simp_all)⟩
          (closedBall_subset_closedBall (by linarith) hz)
      · simp_all; linarith
    · exact lem_Bf_bounded_in_disk_from_f B R R1 hR1_pos hR1_lt_R f h_f_analytic h_finite_zeros h_f_bound z (by linarith)
  suffices 0 ≤ Real.log ‖Bf R R1 f 0‖ by linarith
  exact Real.log_nonneg <| lem_mod_Bf_at_0_ge_1 R R1 hR1_pos hR1_lt_R f h_f_zero h_finite_zeros


lemma apply_BC_to_Lf
    (B r1 r R R1 : ℝ)
    (hB : 1 < B)
    (hr1_pos : 0 < r1)
    (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bound : ∀ z, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (Lf : ℂ → ℂ)
    (hLf : isLf Lf f r R R1)
    (z : ℂ) (hz : ‖z‖ ≤ r1) :
      ‖deriv Lf z‖ ≤
      (16 * Real.log B * r^2) / (r - r1)^3 := by
  refine borel_caratheodory_II (by linarith) (Real.log_pos hB) hr1_pos hr1_lt_r hLf.1.analyticOn hLf.2.1 ?_ (by simp_all)
  exact fun w hw ↦ re_Lf_le_log_B B r R R1 hr_lt_R1 hR1_pos hR1_lt_R f h_f_analytic h_f_zero h_finite_zeros h_f_bound Lf hLf w (by simp_all)

-- Lemma 6: Lf_deriv_is_logBf_deriv
lemma Lf_deriv_is_logBf_deriv (hR1_lt_R : R1 < R) (hR1_pos : 0 < R1)
    (h_f_analytic : ∀ z ∈ closedBall 0 R1, AnalyticAt ℂ f z)
    (ne_top : ∀ z ∈ closedBall 0 R1, analyticOrderAt f z ≠ ⊤)
    (z : ℂ) :
      logDeriv (fun w ↦ Bf R R1 f w /
                           Bf R R1 f 0) z =
      logDeriv (fun w ↦ Bf R R1 f w) z := by
  simp_rw [div_eq_mul_inv]
  refine logDeriv_mul_const z _ ?_
  exact inv_ne_zero (Bf_never_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ne_top 0 (by simp; linarith))

-- Lemma 12: z_minus_rho_diff_nonzero
lemma z_minus_rho_diff_nonzero {R1 : ℝ} {f : ℂ → ℂ}
    (ρ : ℂ) (hρ : ρ ∈ zerosetKfR R1 f)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    z - ρ ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ w - ρ) z := by
  exact ⟨(by grind), (by fun_prop)⟩

-- Lemma 13: blaschke_num_diff_nonzero
lemma blaschke_num_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (ρ : ℂ) (hρ : ρ ∈ zerosetKfR R1 f)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) :
    R - (conj ρ) * z / R ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ R - (conj ρ) * w / R) z := by
  refine ⟨?_, (by fun_prop)⟩
  rw [sub_ne_zero]
  intro hzero
  replace hzero := congr_arg norm hzero |>.le
  have hR : 0 < R := by linarith
  rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg hR.le] at hzero
  grw [(by simp_all : ‖z‖ ≤ R), (by simp_all [zerosetKfR] : ‖ρ‖ ≤ R1)] at hzero
  field_simp at hzero
  linarith

-- Lemma 14: blaschke_frac_diff_nonzero
lemma blaschke_frac_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (ρ : ℂ) (hρ : ρ ∈ zerosetKfR R1 f)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    (R - (conj ρ) * z / R) / (z - ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ (R - (conj ρ) * w / R) / (w - ρ)) z := by
  have hden := z_minus_rho_diff_nonzero (R1:=R1) (f:=f) ρ hρ z hz
  have hnum := blaschke_num_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R ρ hρ z (by simp_all; linarith)
  exact ⟨div_ne_zero hnum.1 hden.1, hnum.2.div hden.2 hden.1⟩


-- Lemma 15: blaschke_pow_diff_nonzero
lemma blaschke_pow_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (ρ : ℂ) (hρ : ρ ∈ zerosetKfR R1 f)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    ((R - (conj ρ) * z / R) / (z - ρ)) ^ analyticOrderNatAt f ρ ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ((R - (conj ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R
      ρ hρ z hz
  exact ⟨pow_ne_zero _ hfrac.1, hfrac.2.pow _⟩

-- Lemma 16: blaschke_prod_diff_nonzero
lemma blaschke_prod_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    (∏ ρ ∈ h_finite_zeros.toFinset, ((R - (conj ρ) * z / R) / (z - ρ)) ^ analyticOrderNatAt f ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                        ((R - (conj ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦ ?_, DifferentiableAt.fun_finsetProd fun ρ hρ ↦ ?_⟩
  · exact blaschke_pow_diff_nonzero hR1_pos hR1_lt_R ρ (by simp_all) z hz|>.1
  · exact blaschke_pow_diff_nonzero hR1_pos hR1_lt_R ρ (by simp_all) z hz|>.2

-- Lemma 17: f_diff_nonzero_outside_Kf
lemma f_diff_nonzero_outside_Kf {R1 : ℝ} {f : ℂ → ℂ}
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    f z ≠ 0 ∧ DifferentiableAt ℂ f z := by
  exact ⟨(by simp_all [zerosetKfR]), h_f_analytic _ (by simp_all)|>.differentiableAt⟩

lemma logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
  (hfg : f =ᶠ[𝓝 z] g) : logDeriv f z = logDeriv g z := by
  unfold logDeriv
  simp only [Pi.div_apply]
  rw [hfg.deriv_eq, hfg.eq_of_nhds]

lemma logDeriv_Bf_is_sum (hR1_lt_R : R1 < R) (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    logDeriv (Bf R R1 f) z = logDeriv f z + logDeriv (fun w ↦
          ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (conj ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  have h_ev : Bf R R1 f =ᶠ[𝓝 z]
      (fun w ↦ f w * ∏ ρ ∈ h_finite_zeros.toFinset, ((R - (conj ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) := by
    filter_upwards [h_finite_zeros.isClosed.isOpen_compl.mem_nhds (by simp_all)] with w hwU
    simp_all [Bf, Cf, div_pow]
    field
  rw [logDeriv_congr_of_eventuallyEq h_ev]
  have hf' := f_diff_nonzero_outside_Kf h_f_analytic z hz
  have hg' := blaschke_prod_diff_nonzero hR1_pos hR1_lt_R h_finite_zeros z hz
  rw [logDeriv_mul _ hf'.1 hg'.1 hf'.2 hg'.2]

theorem in_r_minus_kf {R1 r : ℝ} {f : ℂ → ℂ}
  (hr_lt_R1 : r < R1)
  (z : ℂ)
  (hz : z ∈ closedBall 0 r \ zerosetKfR R1 f) :
   z ∈ closedBall 0 R1 \ zerosetKfR R1 f := by
  simp_all [zerosetKfR]
  linarith

-- Lemma 34: Lf_deriv_step3
lemma Lf_deriv_step3 (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R)
    (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r \ zerosetKfR R1 f) :
    deriv Lf z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ * (1 / (z - R^2 / (conj ρ)) - 1 / (z - ρ)) := by
  rw [h_Lf.2.2.1 z (by simp_all), logDeriv_Bf_is_sum h_finite_zeros hR1_lt_R hR1_pos h_f_analytic z (in_r_minus_kf hr_lt_R1 _ hz), logDeriv_apply]
  have := fun ρ (hρ : ρ ∈ h_finite_zeros.toFinset) ↦ blaschke_pow_diff_nonzero (f := f) hR1_pos hR1_lt_R ρ (by simp_all) z (by simp_all; linarith)
  rw [logDeriv_prod (fun ρ hρ ↦ (this ρ hρ).1) (fun ρ hρ ↦ (this ρ hρ).2)]
  rw [Finset.sum_congr rfl fun ρ hρ ↦ ?_]
  rw [logDeriv_fun_pow (blaschke_frac_diff_nonzero (f := f) hR1_pos hR1_lt_R ρ (by simp_all) z (by simp_all; linarith)|>.2)]
  congr 1
  have hden := z_minus_rho_diff_nonzero ρ (by simp_all) z (in_r_minus_kf hr_lt_R1 _ hz)
  have hnum := blaschke_num_diff_nonzero (f := f) hR1_pos hR1_lt_R
      ρ (by simp_all) z (by simp_all; linarith)
  rw [logDeriv_div z hnum.1 hden.1 hnum.2 hden.2]
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h; simp_all [zerosetKfR]
  simp [logDeriv_apply]
  field_simp [(by simpa : conj ρ ≠ 0), (by norm_cast; linarith : (R : ℂ) ≠ 0)]
  rw [← div_neg]
  ring

-- Lemma 36: sum_rearranged
lemma sum_rearranged {R R1 : ℝ} {f : ℂ → ℂ}
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (z : ℂ) :
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ *
                                    (1 / (z - R^2 / (conj ρ)) - 1 / (z - ρ)) =
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (conj ρ)) -
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun _ _ ↦ ?_]
  ring

-- Lemma 38: rearrange_Lf_deriv
lemma rearrange_Lf_deriv (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R)
    (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r \ zerosetKfR R1 f) :
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ) =
    deriv Lf z -
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (conj ρ)) := by
  rw [Lf_deriv_step3 h_finite_zeros hr_lt_R1 hR1_lt_R hR1_pos h_f_analytic h_f_zero Lf h_Lf z hz]
  rw [sum_rearranged h_finite_zeros z]
  ring

-- Lemma 40: target_inequality_setup
lemma target_inequality_setup (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R)
    (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r \ zerosetKfR R1 f) :
  ‖deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ)‖ ≤
  ‖deriv Lf z‖ +
  ‖∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (conj ρ))‖ := by
  rw [rearrange_Lf_deriv h_finite_zeros hr_lt_R1 hR1_lt_R hR1_pos h_f_analytic h_f_zero Lf h_Lf z hz]
  exact norm_sub_le _ _


lemma norm_Rsq_div_conj (R : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0) : ‖((R^2 : ℂ) / (conj ρ))‖ = (R^2 : ℝ) / ‖ρ‖ := by
  have hb : conj ρ ≠ 0 := by simpa
  have hnormR : ‖(R^2 : ℂ)‖ = (R^2 : ℝ) := by
    simp
  calc
    ‖((R^2 : ℂ) / (conj ρ))‖
        = ‖(R^2 : ℂ)‖ / ‖conj ρ‖ := norm_div _ _
    _ = (R^2 : ℝ) / ‖ρ‖ := by
      simp [hnormR]

lemma norm_sub_ge_norm_sub (x y : ℂ) : ‖x - y‖ ≥ ‖y‖ - ‖x‖ := by
  have := norm_sub_le_norm_add y (-x)
  rwa [norm_neg, (by ring : y + -x = -(x - y)), norm_neg] at this


lemma lem_sum_bound_step2 {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
      (∑ ρ ∈ h_finite_zeros.toFinset,
          (analyticOrderNatAt f ρ : ℝ) / ‖z - (R^2 : ℂ) / (conj ρ)‖)
        ≤ (1/(R^2/R1 - R1)) *
          (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ)) := by
  have hz_norm : ‖z‖ ≤ R1 := by
    simp_all [zerosetKfR]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρS ↦ ?_
  have hρ_ne : ρ ≠ 0 := by
    intro h
    simp_all [zerosetKfR]
  have hρ_norm : ‖ρ‖ ≤ R1 := by simp_all [zerosetKfR]
  rw [← mul_one_div, mul_comm]
  gcongr
  · rw [sub_pos, lt_div_iff₀ hR1_pos, ← pow_two]
    gcongr
  · have h_Rsq_bound : R^2/R1 ≤ ‖((R^2 : ℂ) / (conj ρ))‖ := by
      rw [norm_Rsq_div_conj R ρ hρ_ne]
      gcongr
    grw [h_Rsq_bound, ← hz_norm]
    exact norm_sub_ge_norm_sub ..

lemma final_sum_bound {R R1 B : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hB : 1 < B)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bounded : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ B)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    ‖∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (conj ρ))‖ ≤
    1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
  grw [norm_sum_le]
  simp only [norm_div, Complex.norm_natCast]
  grw [lem_sum_bound_step2 hR1_pos hR1_lt_R h_f_zero h_finite_zeros z hz]
  -- Step 4: Apply lem_sum_m_rho_bound
  have h_f_bounded_alt : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B := by
    intro w hw
    exact h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw))
  grw [lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R f h_f_analytic h_f_zero h_finite_zeros h_f_bounded_alt]
  · field_simp
    rfl
  · refine div_nonneg (by norm_num) ?_
    rw [sub_nonneg, le_div_iff₀ hR1_pos, ← pow_two]
    gcongr

lemma Lf_exists (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_f_zero : f 0 = 1) :
    ∃ Lf : ℂ → ℂ, isLf Lf f r R R1 := by
  let B_f := Bf R R1 f
  have h_Bf_analytic : AnalyticOnNhd ℂ B_f (closedBall (0 : ℂ) R) :=
    lem_Bf_is_analytic R R1 f <| h_f_analytic.mono (by gcongr)
  have h_Bf_ne_zero : ∀ w ∈ closedBall (0 : ℂ) R1, B_f w ≠ 0 := by
    intro w hw
    refine Bf_never_zero R R1 hR1_pos hR1_lt_R f (fun z hz ↦ ?_) (fun z hz ↦ ?_) w hw
    · exact h_f_analytic z <| closedBall_subset_closedBall (by linarith) hz
    · refine order_ne_top h_f_analytic (by linarith) ?_ (closedBall_subset_closedBall (by linarith) hz)
      exact ⟨0, (by simp; linarith), (by simp_all)⟩
  -- Apply lem:log_of_analytic
  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := log_of_analytic_open hR1_pos
    (h_Bf_analytic.mono (fun z hz ↦ (by simp_all; linarith)))
    (fun z hz ↦ h_Bf_ne_zero z (by simp_all; linarith))
  have bs := closedBall_subset_ball (x := (0 : ℂ)) hr_lt_R1
  refine ⟨J, hJ1.mono bs, hJ2, fun z hz ↦ hJ3 z (bs hz), fun z hz ↦ (hJ4 z (bs hz)).symm⟩

-- Lemma 43: final_ineq1
lemma final_ineq1
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bounded : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ B)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r1 \ zerosetKfR R1 f) :
    ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset,
                 analyticOrderNatAt f ρ / (z - ρ)‖ ≤
    (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log B := by
  have hr_pos : 0 < r := by linarith [hr1pos, hr1_lt_r]
  have hR1_pos : 0 < R1 := by linarith [hr_pos, hr_lt_R1]
  obtain ⟨Lf, h_Lf⟩ := Lf_exists hr_lt_R1 hR1_lt_R hR1_pos (h_f_analytic.mono (by gcongr)) h_f_zero
  have hz_in_r : z ∈ closedBall (0 : ℂ) r \ zerosetKfR R1 f := by
    simp_all [zerosetKfR]
    linarith
  grw [target_inequality_setup h_finite_zeros hr_lt_R1 hR1_lt_R hR1_pos (h_f_analytic.mono (by gcongr)) h_f_zero Lf h_Lf z hz_in_r]
  have hz_in_R1 : z ∈ closedBall (0 : ℂ) R1 \ zerosetKfR R1 f := by
    simp_all [zerosetKfR]
    linarith
  grw [final_sum_bound hR1_pos hR1_lt_R hB (h_f_analytic.mono (by gcongr)) h_f_zero h_finite_zeros h_f_bounded z hz_in_R1]
  have hz_le_r1 : ‖z‖ ≤ r1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1
  have hz_abs : ‖z‖ ≤ r1 := hz_le_r1
  grw [apply_BC_to_Lf B r1 r R R1 hB hr1pos hr1_lt_r hr_lt_R1 hR1_pos hR1_lt_R f
    (h_f_analytic.mono (by gcongr)) h_f_zero h_finite_zeros
    (h_f_bound := fun w hw => h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw)))
    Lf h_Lf z hz_abs]
  field_simp
  rfl
