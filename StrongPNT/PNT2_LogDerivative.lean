import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.ExponentialBounds
import StrongPNT.PNT1_ComplexAnalysis
import Mathlib.Tactic.Cases

def zerosetKfR (R : ℝ) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}

open Filter Metric Set Bornology Function
open Classical

/-! ### The quotient `Cf` (no core wrapper) -/

noncomputable def trailingCoeff (f : ℂ → ℂ) (z : ℂ) : ℂ :=
    if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else
      0
  else
    0

lemma trailingCoeff_def {f : ℂ → ℂ} {z : ℂ} (h1 : AnalyticAt ℂ f z)
    (h2 : analyticOrderAt f z ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ trailingCoeff f z = g z
    ∧ f =ᶠ[nhds z] fun z_1 ↦ (z_1 - z) ^ analyticOrderNatAt f z * g z_1 := by
  obtain ⟨hg1, hg2, hg3⟩ := (h1.analyticOrderAt_ne_top.mp h2).choose_spec
  set g := (h1.analyticOrderAt_ne_top.mp h2).choose
  refine ⟨g, hg1, hg2, ?_, (by simpa)⟩
  simp [trailingCoeff, h1, h2, g]

lemma trailingCoeff_ne_zero {f : ℂ → ℂ} {z : ℂ} (h1 : AnalyticAt ℂ f z)
    (h2 : analyticOrderAt f z ≠ ⊤) : trailingCoeff f z ≠ 0 := by
  obtain ⟨_, _, _, hg3, _⟩ := trailingCoeff_def h1 h2
  rwa [hg3]

lemma order_ne_top {f : ℂ → ℂ} {r : ℝ} {z : ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hr : 0 ≤ r)
    (ne : ∃ z' ∈ closedBall (0 : ℂ) r, f z' ≠ 0) (hz : z ∈ closedBall 0 r) :
    analyticOrderAt f z ≠ ⊤ := by
  rcases ne with ⟨z', hz'⟩
  refine hf.analyticOrderAt_ne_top_of_isPreconnected (isConnected_closedBall hr).isPreconnected hz'.1 hz ?_
  simp [AnalyticAt.analyticOrderAt_eq_zero (hf z' hz'.1)|>.mpr hz'.2]

/-- The “deflated” quotient: divide `f` by the product of `(z-ρ)^{m_ρ}`, and at a zero `z=σ`
    use the local factor function `h_σ σ` in the numerator (so the expression extends analytically). -/
noncomputable def Cf
    (R1 : ℝ)
    (f : ℂ → ℂ)
    (z : ℂ) : ℂ :=
if h_finite_zeros : (zerosetKfR R1 f).Finite then
    if _ : z ∈ zerosetKfR R1 f then
      trailingCoeff f z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase z), (z - ρ) ^ analyticOrderNatAt f ρ
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
  · -- First part: AnalyticAt
    -- Use Finset.analyticAt_prod
    let f : ℂ → ℂ → ℂ := fun s z => (z - s) ^ (n s)
    have h_each_analytic : ∀ s ∈ S, AnalyticAt ℂ (f s) w := by
      intro s hs
      fun_prop
    convert S.analyticAt_prod h_each_analytic using 1
    ext
    simp [f]
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

lemma lem_Cf_analytic_off_K
    {R R1 : ℝ}
    {f : ℂ → ℂ}
    {h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R)}
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1  f) :
    AnalyticAt ℂ (Cf R1 f) z := by
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · unfold Cf
    simp [h_finite_zeros, analyticAt_const]
  have h_ratio_analytic : AnalyticAt ℂ (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ) z := by
    apply lem_ratioAnalAt z f
    · apply h_f_analytic _ hz.1
    · -- Show z ∉ ↑h_finite_zeros.toFinset
      intro h_z_in_finset
      have h_z_in_zeros : z ∈ zerosetKfR R1 f := h_finite_zeros.mem_toFinset.mp h_z_in_finset
      exact hz.2 h_z_in_zeros

  -- Show that the ratio function equals Cf in a neighborhood of z
  have h_eventually_eq : (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ) =ᶠ[nhds z]
    (fun w => Cf R1 f w) := by
    -- Since the zero set is finite, its complement is open
    have hz_not_in : z ∉ zerosetKfR R1 f := hz.2
    have h_open : IsOpen (Set.compl (zerosetKfR R1 f)) := h_finite_zeros.isClosed.isOpen_compl
    apply Filter.eventually_of_mem (h_open.mem_nhds hz_not_in)
    intro w hw_not_in_compl
    -- Convert from membership in complement to non-membership
    have hw_not_in_zeros : w ∉ zerosetKfR R1 f := hw_not_in_compl
    -- Since w ∉ zerosetKfR R1, Cf w uses the else branch
    show f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ =
         Cf R1 f w
    -- Apply the definition of Cf using dif_neg for dependent if-then-else
    simp [Cf, h_finite_zeros, hw_not_in_zeros]

  -- Transfer analyticity
  exact h_ratio_analytic.congr h_eventually_eq


lemma lem_prod_no_sigma1
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 f) (z : ℂ) :
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ =
    (z - σ) ^ analyticOrderNatAt f σ *
    ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ analyticOrderNatAt f ρ := by
  classical
  have hmem : σ ∈ h_finite_zeros.toFinset :=
    (Set.Finite.mem_toFinset (hs := h_finite_zeros)).2 hσ
  simpa using
    (Finset.mul_prod_erase (s := h_finite_zeros.toFinset)
      (f := fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ) (a := σ) hmem).symm


lemma lem_Cf_at_sigma
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 f) (hfσ : AnalyticAt ℂ  f σ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g σ ∧ ∀ᶠ z in nhds σ,
      Cf R1 f z =
      g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ analyticOrderNatAt f ρ := by
  by_cases top : analyticOrderAt f σ = ⊤
  · refine ⟨0, analyticAt_const, ?_⟩
    have f_eq_zero := analyticOrderAt_eq_top.mp top
    have trailing_eq_zero : ∀ᶠ (z : ℂ) in nhds σ, trailingCoeff f z = 0 := by
      filter_upwards [eventually_eventually_nhds.mpr f_eq_zero] with z eq_zero
      simp [trailingCoeff, analyticOrderAt_eq_top.mpr eq_zero]
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
    simp [Cf, this, f_eq, h_finite_zeros]
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

lemma lem_Cf_analytic_at_K
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 f) (hfσ : AnalyticAt ℂ f σ) :
    AnalyticAt ℂ (Cf R1 f)  σ := by
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · unfold Cf
    simp [h_finite_zeros, analyticAt_const]
  obtain ⟨g, hg1, hg2⟩ := lem_Cf_at_sigma h_finite_zeros σ hσ hfσ
  apply analyticAt_congr hg2|>.mpr
  apply lem_h_ratio_anal
  exact hg1

lemma lem_f_nonzero_off_K
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    f z ≠ 0 := by
  exact fun h => hz.2 ⟨hz.1, h⟩

lemma lem_Cf_nonzero_off_K
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f) :
    Cf R1 f z ≠ 0 := by
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · simp [Cf, h_finite_zeros]
  -- Since z ∉ zerosetKfR R1, Cf uses the else branch
  have hz_not_in : z ∉ zerosetKfR R1 f := hz.2

  -- Unfold Cf definition using the else branch
  have h_cf_eq : Cf R1 f z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ := by
    simp [Cf, hz_not_in, h_finite_zeros]

  rw [h_cf_eq]

  -- Apply div_ne_zero: need numerator ≠ 0 and denominator ≠ 0
  apply div_ne_zero

  -- Numerator: f z ≠ 0 by lem_f_nonzero_off_K with explicit parameters
  · apply @lem_f_nonzero_off_K R1 f z hz

  -- Denominator: product is nonzero
  · apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    -- Need (z - ρ) ^ analyticOrderNatAt f ρ ≠ 0
    apply pow_ne_zero
    -- Need z - ρ ≠ 0, i.e., z ≠ ρ
    intro h_eq
    -- From h_eq : z - ρ = 0, we get z = ρ using sub_eq_zero
    have hz_eq_rho : z = ρ := by
      rwa [sub_eq_zero] at h_eq
    -- But ρ ∈ zerosetKfR R1 (from hρ) and z ∉ zerosetKfR R1 (from hz_not_in)
    have hρ_in : ρ ∈ zerosetKfR R1 f := h_finite_zeros.mem_toFinset.mp hρ
    rw [hz_eq_rho] at hz_not_in
    exact hz_not_in hρ_in

lemma lem_Cf_nonzero_on_K
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 f) (hfσ : AnalyticAt ℂ f σ) (ne_top : analyticOrderAt f σ ≠ ⊤) :
    Cf R1 f σ ≠ 0 := by
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · simp [Cf, h_finite_zeros]
  have hden :
      (∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (σ - ρ) ^ analyticOrderNatAt f ρ) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro ρ hρmem
    have hρ_ne_σ : ρ ≠ σ := (Finset.mem_erase.mp hρmem).1
    have hσ_ne_ρ : σ ≠ ρ := hρ_ne_σ.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hσ_ne_ρ)
  simp [Cf, hσ, hden, h_finite_zeros]
  exact trailingCoeff_ne_zero hfσ ne_top

lemma lem_Cf_never_zero
    {R1 : ℝ}
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (ne_top : ∀ z ∈ closedBall 0 R1, analyticOrderAt f z ≠ ⊤)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1) :
    Cf R1 f z ≠ 0 := by
  by_cases h : z ∈ zerosetKfR R1 f
  ·  apply lem_Cf_nonzero_on_K z h (hf z (by simp_all)) (ne_top z (by simp_all))
  · apply lem_Cf_nonzero_off_K z ⟨hz, h⟩

noncomputable def Bf
    (R R1 : ℝ)
    (f : ℂ → ℂ)
    (z : ℂ) : ℂ :=
  if h_finite_zeros : (zerosetKfR R1 f).Finite then
    Cf R1 f z *
    ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * z / (R : ℂ)) ^ analyticOrderNatAt f ρ
  else
    1

theorem lem_R_div_mod_rho_ge_R_over_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 f) :
    R / norm ρ ≥ (R/R1 : ℝ) := by
  gcongr
  · linarith
  · apply norm_pos_iff.mpr
    intro h
    simp_all [zerosetKfR]
  · simp_all [zerosetKfR]

lemma lem_mod_Bf_is_prod_mod (R R1 : ℝ)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (z : ℂ)
    (hz : z ∉ zerosetKfR R1 f) :
  ‖Bf R R1 f  z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ)) ^ analyticOrderNatAt f ρ‖ := by
  -- Use definition of Bf: Bf z = Cf z * ∏ ρ, ((R - star ρ * z / R)^{m_ρ})
  simp only [Bf, h_finite_zeros, ↓reduceDIte]
  rw [norm_mul, norm_prod]
  -- When z ∉ zerosetKfR R1, we have Cf z = f z / ∏ ρ, (z - ρ)^{m_ρ} by definition
  have hCf : Cf R1 f z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ := by
    simp [Cf, hz, h_finite_zeros]
  rw [hCf, norm_div, norm_prod]
  -- Rearrange: (‖f z‖ / ∏‖(z-ρ)^{m_ρ}‖) * ∏‖(R - star ρ * z / R)^{m_ρ}‖
  rw [div_mul_eq_mul_div]
  -- Use properties of products to combine: ‖f z‖ * (∏‖(R - star ρ * z / R)^{m_ρ}‖ / ∏‖(z-ρ)^{m_ρ}‖)
  rw [mul_div_assoc]
  -- Use Finset.prod_div_distrib: ∏(a/b) = (∏a)/(∏b)
  rw [← Finset.prod_div_distrib]
  congr 2
  ext ρ
  -- Show ‖a^n‖ / ‖b^n‖ = ‖(a/b)^n‖
  rw [← norm_div, ← div_pow]
  congr 2
  -- Show star ρ * z = z * star ρ by commutativity
  ring


lemma lem_mod_Bf_prod_mod (R R1 : ℝ)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
  (z : ℂ)
  (hz : z ∉ zerosetKfR R1 f) :
  ‖Bf R R1 f z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ analyticOrderNatAt f ρ := by
  -- Apply lem_mod_Bf_is_prod_mod to get the first form (use hz that z ∉ zeroset)
  have h1 := lem_mod_Bf_is_prod_mod R R1 f h_finite_zeros z hz
  rw [h1]
  -- Now use lem_abs_pow to transform each term in the product
  congr 2
  ext ρ
  rw [norm_pow]

lemma lem_mod_Bf_at_0 (R R1 : ℝ)
    (f : ℂ → ℂ)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ‖Bf R R1 f 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖((R : ℂ) / (-ρ))‖ ^ analyticOrderNatAt f ρ := by

  have hz0 : 0 ∉ zerosetKfR R1 f := by
    simp_all [zerosetKfR]
  rw [lem_mod_Bf_prod_mod R R1 f h_finite_zeros 0 hz0]
  -- Now simplify: when z = 0, we have ((R - 0 * star ρ / R) / (0 - ρ)) = R / (-ρ)
  congr 2
  ext ρ
  congr 1
  simp only [zero_mul, zero_div, sub_zero, zero_sub]

theorem lem_mod_Bf_at_0_eval  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ‖Bf R R1 f 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
  -- Start with lem_mod_Bf_at_0
  rw [lem_mod_Bf_at_0 R R1 f h_f_nonzero_at_zero h_finite_zeros]
  -- Now we need to show the products are equal
  congr 1
  -- Use Finset.prod_congr to show the products are equal
  apply Finset.prod_congr rfl
  intro ρ hρ
  simp
  rw [abs_of_nonneg (by linarith)]

theorem lem_mod_Bf_at_0_as_ratio  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ‖Bf R R1 f 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
  exact lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R f h_f_nonzero_at_zero h_finite_zeros

lemma lem_prod_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
    (h_nonneg : ∀ ρ ∈ K, 0 ≤ a ρ) (h_le : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  exact Finset.prod_le_prod h_nonneg h_le


lemma lem_mod_lower_bound_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (R/R1 : ℝ) ^ analyticOrderNatAt f ρ ≥ 1 := by
  classical
  set K := h_finite_zeros.toFinset

  have h_base_ge_1 : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have h :=
    lem_prod_ineq K (fun _ : ℂ => (1 : ℝ))
      (fun ρ : ℂ => (R/R1 : ℝ) ^ analyticOrderNatAt f ρ)
      (by intro ρ hρ; norm_num)
      (by
        intro ρ hρ
        simpa using (one_le_pow₀ (by linarith [h_base_ge_1])))
  simpa [K] using h

theorem lem_mod_Bf_at_0_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ‖Bf R R1 f 0‖ ≥ 1 := by
  -- First derive f 0 ≠ 0 from f 0 = 1
  have R_over_R1_nonneg : 1 < R / R1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have R_over_R1_nonneg : 0 ≤ R / R1 := by linarith
  have h_f_nonzero_at_zero : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
  -- Use lem_mod_Bf_at_0_as_ratio to express ‖Bf ... 0‖ as a product
  rw [lem_mod_Bf_at_0_as_ratio R R1 hR1_pos hR1_lt_R f h_f_nonzero_at_zero h_finite_zeros]
  -- Since f 0 = 1, we have ‖f 0‖ = 1
  rw [hf0_eq_one, norm_one, one_mul]
  -- Show that the product ∏ (R / ‖ρ‖)^n ≥ ∏ (3/2)^n
  have h_prod_ge : ∏ ρ ∈ h_finite_zeros.toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ ≥
                   ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ analyticOrderNatAt f ρ := by
    apply Finset.prod_le_prod
    -- Show (3/2)^n ≥ 0
    · intro ρ hρ
      apply pow_nonneg
      apply R_over_R1_nonneg
    -- Show (R / ‖ρ‖)^n ≥ (3/2)^n for each ρ
    · intro ρ hρ
      have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 f := by
        exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      -- We have R / norm ρ ≥ 3/2, and ‖ρ‖ = norm ρ
      have h_ratio_ge : R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
        -- norm is defined as ‖z‖, so they are equal
        have h_norm_abs_eq : ‖ρ‖ = norm ρ := by rfl
        rw [h_norm_abs_eq]
        exact lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_nonzero_at_zero ρ h_ρ_in_zeros

      -- Use power monotonicity: if a ≥ b > 0, then a^n ≥ b^n
      have h_3_2_pos : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
      have h_3_2_pos : (0 : ℝ) < (R/R1 : ℝ) := by linarith
      have h_ratio_pos : (0 : ℝ) ≤ R / ‖ρ‖ := by
        linarith [h_ratio_ge]
      exact pow_le_pow_left₀ R_over_R1_nonneg h_ratio_ge (analyticOrderNatAt f ρ)
  -- Use lem_mod_lower_bound_1: the (3/2)^n product is ≥ 1
  have h_3_2_prod_ge_1 : ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ analyticOrderNatAt f ρ ≥ 1 :=
    lem_mod_lower_bound_1 R R1 hR1_pos hR1_lt_R f h_finite_zeros
  -- Combine: 1 ≤ (3/2)^n product ≤ (R/‖ρ‖)^n product
  exact le_trans h_3_2_prod_ge_1 h_prod_ge

theorem lem_Bf_is_analytic (R R1 : ℝ)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    AnalyticOnNhd ℂ (Bf R R1 f)  (Metric.closedBall (0 : ℂ) R) := by
  -- By definition of AnalyticOnNhd
  intro z hz
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · unfold Bf
    simp [h_finite_zeros, analyticAt_const]
  -- First show the finite Blaschke product factor is analytic at z
  have h_blaschke_linear : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
    intro ρ hρ
    -- rewrite as constant + constant * w
    have h_eq : (fun w : ℂ => (R : ℂ) - star ρ * w / (R : ℂ)) =
                (fun w : ℂ => (R : ℂ) + (-(star ρ) / (R : ℂ)) * w) := by
      funext w
      field_simp
      ring
    rw [h_eq]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)

  have h_powers : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ analyticOrderNatAt f ρ) z := by
    intro ρ hρ
    exact (h_blaschke_linear ρ hρ).fun_pow _

  have h_product : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * w / (R : ℂ)) ^ analyticOrderNatAt f ρ) z := by
    apply Finset.analyticAt_fun_prod
    intro ρ hρ
    apply h_powers
    exact hρ
  -- Now handle two cases: z is in the finite zero set or not
  unfold Bf
  simp [h_finite_zeros]
  by_cases hz_in : z ∈ zerosetKfR R1 f
  · -- z is a zero: use the local factor specification to get analyticity of Cf at σ
    have h_cf_at_sigma := @lem_Cf_analytic_at_K R1 f z hz_in (h_f_analytic z ?_)
    -- Multiply analytic functions to get analyticity of Bf = Cf * product
    · exact AnalyticAt.fun_mul h_cf_at_sigma h_product
    · exact closedBall_subset_closedBall (by linarith) hz
  · -- z is not a zero: Cf is analytic off the zero set
    have hz_in_compl : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 f := by
      constructor
      · exact hz
      · exact hz_in
    have h_cf_off := @lem_Cf_analytic_off_K R R1 f h_f_analytic z hz_in_compl
    exact AnalyticAt.fun_mul h_cf_off h_product

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = (‖z‖ ^ 2 : ℂ) := by
  -- Use the fact that star = conj for complex numbers
  rw [Complex.star_def]
  -- Now use Complex.mul_conj': z * conj z = ‖z‖ ^ 2
  exact Complex.mul_conj' z

lemma lem_mod_Bf_eq_mod_f_on_boundary (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 f z‖ = ‖f z‖ := by
  intro z hz
  -- Use the factorization from lem_mod_Bf_prod_mod; first show z ∉ zerosetKfR
  have hz_not_in : z ∉ zerosetKfR R1 f := by
    intro h_in
    -- h_in says z ∈ closedBall (0, R1), so ‖z‖ ≤ R1
    have h_norm_le_R1 : ‖z‖ ≤ R1 := by simpa [sub_zero] using (h_in.1 : z ∈ Metric.closedBall (0 : ℂ) R1)
    -- hz gives ‖z‖ = R, and R1 < R, contradiction
    have h_norm_eq_R : ‖z‖ = R := by simpa using hz
    linarith [h_norm_le_R1, h_norm_eq_R, hR1_lt_R]
  rw [lem_mod_Bf_prod_mod R R1 f h_finite_zeros z hz_not_in]

  -- Show each Blaschke factor has norm 1 when |z| = R
  have h_each_factor_one : ∀ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ = 1 := by
    intro ρ hρ

    -- First, we need z ≠ ρ (if z = ρ, we get a contradiction since |z| = R > R1 but ρ ∈ ball(0, R1))
    have z_ne_rho : z ≠ ρ := by
      intro h_eq
      have rho_in_zeros : ρ ∈ zerosetKfR R1 f := (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      have rho_bound : ‖ρ‖ ≤ R1 := by
        have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := rho_in_zeros.1
        rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
        simpa using h_in_ball
      have R1_lt_R : R1 < R := by linarith
      rw [← h_eq, hz] at rho_bound
      linarith [R1_lt_R]

    -- Now prove the Blaschke factor has norm 1
    rw [Complex.norm_div]

    -- Use z * star z = ‖z‖² = R² when |z| = R
    have z_conj_eq : z * star z = (R ^ 2 : ℂ) := by
      rw [complex_mul_star_eq_norm_sq z, hz, pow_two]

    -- Rewrite numerator: R - z * star ρ / R = (R² - z * star ρ) / R
    have num_rewrite : (R : ℂ) - z * star ρ / (R : ℂ) = ((R : ℂ)^2 - z * star ρ) / (R : ℂ) := by
      field [ne_of_gt hR1_pos]
    rw [num_rewrite, Complex.norm_div]

    -- Key step: R² - z * star ρ = z * star(z - ρ) using z * star z = R²
    have factor_eq : (R : ℂ)^2 - z * star ρ = z * star (z - ρ) := by
      rw [← z_conj_eq, star_sub]
      ring

    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    field_simp

    have h_denom_ne_zero : R * ‖z - ρ‖ ≠ 0 := by
      apply mul_ne_zero
      -- Prove R is not zero
      · linarith [hR1_pos, hR1_lt_R]
      -- Prove the norm is not zero
      · simp [norm_ne_zero_iff, sub_ne_zero, z_ne_rho]
    -- field_simp can now use this fact to solve the goal.
    rw [Complex.norm_real, norm_norm, hz]
    field_simp [h_denom_ne_zero]
    exact div_self h_denom_ne_zero


  -- Apply this to show the product equals 1
  have h_prod_one : ∏ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ analyticOrderNatAt f ρ = 1 := by
    -- Each factor equals 1, and 1^n = 1
    rw [← Finset.prod_congr rfl (fun ρ hρ => by rw [h_each_factor_one ρ hρ, one_pow])]
    rw [Finset.prod_const_one]

  rw [h_prod_one, mul_one]


lemma lem_Bf_bounded_on_boundary (B R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 f z‖ ≤ B := by
  intro z hz
  have hz_le : ‖z‖ ≤ R := le_of_eq hz
  have h_eq :=
    lem_mod_Bf_eq_mod_f_on_boundary R R1 (by linarith) hR1_lt_R f h_finite_zeros z hz
  simpa [h_eq] using hf_le_B z hz_le

lemma mem_closedBall_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  have : dist z (0 : ℂ) ≤ R := by simpa [Complex.dist_eq, sub_zero] using hz
  simpa [Metric.closedBall] using this

lemma closure_ball_eq_closedBall_center (R : ℝ) (hR : 0 < R) :
  closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
  simpa using (closure_ball (x := (0 : ℂ)) (r := R) (ne_of_gt hR))

lemma lem_max_mod_principle_for_Bf (B R : ℝ) (hB : 1 < B) (hR_pos : 0 < R)
    (fB : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ fB (Metric.closedBall (0 : ℂ) R))
  (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R → ‖fB z‖ ≤ B) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖fB z‖ ≤ B := by
  intro z hz
  -- Prepare nonnegativity of B
  have hB0 : 0 ≤ B := le_of_lt (lt_trans zero_lt_one hB)
  -- Convert analytic assumption to the form required by Hard MMP
  have h_an_on_closure : AnalyticOn ℂ fB (closure (ballDR R)) := by
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using h_analytic.analyticOn
  -- Apply Hard maximum modulus principle on the closed ball of radius R
  have h_le :=
    lem_HardMMP R B hR_pos fB h_an_on_closure (by
      intro z hzR; exact h_bd_boundary z hzR)
  -- It remains to see that z belongs to the closure of the open ball of radius R
  have hz_cl : z ∈ closure (ballDR R) := by
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_of_norm_le hz
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using hz_closed
  exact h_le z hz_cl


lemma lem_Bf_bounded_in_disk_from_boundary (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 f z‖ ≤ B := by
  have hA := lem_Bf_is_analytic R R1 f h_f_analytic
  exact lem_max_mod_principle_for_Bf B R hB (by linarith)
    (Bf R R1 f) hA h_bd_boundary


lemma lem_Bf_bounded_in_disk_from_f (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 f z‖ ≤ B := by
  intro z hz
  have h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 f z‖ ≤ B :=
    lem_Bf_bounded_on_boundary B R R1 hR1_pos hR1_lt_R f h_finite_zeros hf_le_B
  exact (lem_Bf_bounded_in_disk_from_boundary B R R1 hB hR1_pos hR1_lt_R f h_f_analytic h_bd_boundary) z hz


lemma lem_Bf_at_0_le_M (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
  ‖Bf R R1 f 0‖ ≤ B := by
  have h :=
    lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R f h_f_analytic h_finite_zeros hf_le_B
  have h0 : ‖(0 : ℂ)‖ ≤ R := by simpa using (le_of_lt (by linarith))
  simpa using h 0 h0


lemma lem_combine_bounds_on_Bf0 (B R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hBf0 : ‖Bf R R1 f 0‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ : ℝ) ≤ B := by
  classical
  -- Abbreviate the finite set of zeros
  set K := h_finite_zeros.toFinset
  -- Evaluate ‖Bf(0)‖ in terms of the product over zeros
  have hf0_ne0 : f 0 ≠ 0 := by simp [hf0_eq_one]
  have hf0_norm : ‖f 0‖ = 1 := by simp [hf0_eq_one]
  have h_eval0 :=
    lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R f hf0_ne0 h_finite_zeros
  have h_eval_prod :
      ‖Bf R R1 f 0‖
        = ∏ ρ ∈ K, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
    rw [h_eval0, hf0_norm, one_mul]
  -- For each zero ρ ∈ K, we have R/‖ρ‖ ≥ 3/2
  have h_base_ge : ∀ ρ ∈ K, R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
    intro ρ hρK
    have hρ_in : ρ ∈ zerosetKfR R1 f := by simpa [K] using hρK
    simpa using
      (lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f hf0_ne0 ρ hρ_in)
  -- Compare products termwise and combine
  have R_over_R1_nonneg : 0 ≤ R/R1 := by
    have : 0 ≤ R := by linarith
    apply div_nonneg (by assumption) (le_of_lt hR1_pos)
  have h_prod_le :
      ∏ ρ ∈ K, (R/R1 : ℝ) ^ analyticOrderNatAt f ρ
        ≤ ∏ ρ ∈ K, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
    refine lem_prod_ineq K
      (fun ρ => (R/R1 : ℝ) ^ analyticOrderNatAt f ρ)
      (fun ρ => (R / ‖ρ‖) ^ analyticOrderNatAt f ρ)
      ?h_nonneg ?h_le
    · intro ρ hρK; exact pow_nonneg (R_over_R1_nonneg) _
    · intro ρ hρK
      exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ R / R1) (h_base_ge ρ hρK) _
  have h_prod_le_B :
      ∏ ρ ∈ K, (R / R1: ℝ) ^ analyticOrderNatAt f ρ ≤ B := by
    have h_right : ∏ ρ ∈ K, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ =
        ‖Bf R R1 f 0‖ := by
      simp [h_eval_prod]
    exact le_trans h_prod_le (by simpa [h_right] using hBf0)
  -- Convert the product of powers to a single power with exponent the sum of exponents
  have h_prod_pow_sum :
      (∏ ρ ∈ K, (R/R1 : ℝ) ^ analyticOrderNatAt f ρ)
        = (R/R1 : ℝ) ^ (∑ ρ ∈ K, analyticOrderNatAt f ρ) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum K (fun ρ => analyticOrderNatAt f ρ) (R/R1 : ℝ))
  -- Now we have a bound on (3/2)^(sum m_ρ) with a natural-number exponent
  have h_natPow : (R / R1 : ℝ) ^ (∑ ρ ∈ K, analyticOrderNatAt f ρ) ≤ B := by
    simpa [h_prod_pow_sum] using h_prod_le_B
  -- Let S be that natural sum of multiplicities
  set S : ℕ := ∑ ρ ∈ K, analyticOrderNatAt f ρ
  have h_natPowS : (R / R1 : ℝ) ^ S ≤ B := by simpa [S] using h_natPow
  -- Convert to real exponent using Real.rpow_natCast
  have h_rpowS : (R / R1 : ℝ) ^ (S : ℝ) ≤ B := by
    -- rewrite the left-hand side using rpow_natCast
    simpa [(Real.rpow_natCast (R / R1 : ℝ) S)] using h_natPowS
  -- Finally, rewrite S back as the sum over K and K as the toFinset
  have h_cast_sum : (S : ℝ)
      = (∑ ρ ∈ K, (analyticOrderNatAt f ρ : ℝ)) := by
    simp [S]
  -- Conclude by rewriting the exponent
  have : (R / R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderNatAt f ρ : ℝ)) ≤ B := by
    simpa [h_cast_sum] using h_rpowS
  simpa [K] using this


lemma lem_jensen_inequality_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ : ℝ) ≤ B := by
  -- Derive f 0 ≠ 0 from f 0 = 1
  have hf0_ne0 : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
  -- Bound Bf at 0 using the maximum modulus arguments
  have hBf0 :=
    lem_Bf_at_0_le_M B R R1 hB hR1_pos hR1_lt_R f h_f_analytic h_finite_zeros hf_le_B
  -- Convert that bound into the desired product bound
  let K := h_finite_zeros.toFinset
  have hres := lem_combine_bounds_on_Bf0 B R R1 hR1_pos hR1_lt_R f hf0_eq_one h_finite_zeros hBf0
  -- Align coercions and finish (adjust numerical coercions if necessary)
  simpa using hres


lemma lem_log_mono_inc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

lemma lem_jensen_log_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ)) * Real.log (R / R1) ≤ Real.log B := by
  -- Let S denote the sum of the multiplicities
  set S : ℝ := ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ)
  -- From the Jensen-type inequality
  have hpow_le : (R / R1 : ℝ) ^ S ≤ B := by
    simpa [S] using
      (lem_jensen_inequality_form B R R1 hB hR1_pos hR1_lt_R f h_f_analytic hf0_eq_one h_finite_zeros hf_le_B)
  -- Base positivity
  have hbase_pos : 1 < (R / R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have hbase_pos' : 0 < (R / R1 : ℝ) := by
    have : 0 < R := by linarith
    linarith
  -- Positivity of the left-hand side to apply log monotonicity
  have hxpos : 0 < (R / R1 : ℝ) ^ S := by
    simpa [S] using Real.rpow_pos_of_pos hbase_pos' S
  -- Apply monotonicity of log
  have hlog_le : Real.log ((R / R1 : ℝ) ^ S) ≤ Real.log B :=
    lem_log_mono_inc hxpos hpow_le
  -- Rewrite log of a power
  have hlog_rpow : Real.log ((R / R1 : ℝ) ^ S) = S * Real.log (R / R1) := by
    simpa using (Real.log_rpow hbase_pos' S)
  -- Conclude
  simpa [S, hlog_rpow] using hlog_le


lemma lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ)) ≤ (1/Real.log (R/R1)) * Real.log B := by
  have h_div_log : (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ)) * Real.log (R/R1) ≤ Real.log B := by
    apply lem_jensen_log_form B R R1 hB hR1_pos hR1_lt_R f h_f_analytic hf0_eq_one h_finite_zeros hf_le_B
  have log_pos' : R/R1 > 1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have log_pos : Real.log (R/R1) > 0 := by exact Real.log_pos log_pos'
  calc
    ∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderNatAt f ρ)
    _ = 1 / Real.log (R / R1) * (Real.log (R / R1) * (∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderNatAt f ρ))) := by
      field_simp [ne_of_gt log_pos]
    _ ≤ 1 / Real.log (R / R1) * Real.log B := by
      gcongr
      rw [mul_comm]
      exact h_div_log

variable {R R1 r B : ℝ} {f : ℂ → ℂ}
variable (h_finite_zeros : (zerosetKfR R1 f).Finite)

lemma Bf_is_analytic_on_disk
    (R R1 : ℝ)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1)) :
    AnalyticOnNhd ℂ (Bf R R1 f ) (Metric.closedBall (0 : ℂ) R) :=
    lem_Bf_is_analytic R R1 f <| h_f_analytic.mono (closedBall_subset_closedBall hR_lt_1.le)

lemma lem_Bf_eq_prod_Cf
    (R R1 : ℝ)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z, Bf R R1 f z =
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ analyticOrderNatAt f ρ) *
      (Cf R1 f z) := by
  intro z
  simp [Bf, h_finite_zeros]
  ring

lemma lem_num_prod_never_zero_all
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1,
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ analyticOrderNatAt f ρ) ≠ 0 := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  apply pow_ne_zero

  -- Following the informal proof: extract bounds |ρ| ≤ R1, |z| ≤ R1
  have hρ_mem : ρ ∈ zerosetKfR R1 f := by
    rwa [Set.Finite.mem_toFinset h_finite_zeros] at hρ
  have hρ_bound : ‖ρ‖ ≤ R1 := by
    rw [zerosetKfR] at hρ_mem; simp at hρ_mem; exact hρ_mem.1
  have hz_bound : ‖z‖ ≤ R1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz

  -- Get R > 0
  have hR_pos : (0 : ℝ) < R := lt_trans hR1_pos hR1_lt_R

  -- Key step: show R - R1²/R > 0 as stated in informal proof
  have key_positive : (0 : ℝ) < R - R1 * R1 / R := by
    -- Since R1 < R, we have R1² < R² so R1²/R < R
    have h1 : R1 * R1 < R * R := by
      apply mul_self_lt_mul_self (le_of_lt hR1_pos) hR1_lt_R
    have h2 : R1 * R1 / R < R := by
      rw [div_lt_iff₀ hR_pos]
      exact h1
    linarith [h2]

  -- Show factor is nonzero by proving positive norm
  suffices h : (0 : ℝ) < ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ by
    exact norm_pos_iff.mp h

  -- Use reverse triangle inequality: |a - b| ≥ |a| - |b|
  have triangle_ineq : ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ ≥ ‖(R : ℂ)‖ - ‖star ρ * z / (R : ℂ)‖ :=
    norm_sub_norm_le _ _

  -- Simplify ‖(R : ℂ)‖ = R
  have R_norm_eq : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_of_nonneg (le_of_lt hR_pos)]

  -- Bound the product term: ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R
  have product_bound : ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R := by
    rw [norm_div, norm_mul, norm_star, R_norm_eq]
    -- We need to show ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R
    -- This is equivalent to ‖ρ‖ * ‖z‖ ≤ R1 * R1
    have mult_bound : ‖ρ‖ * ‖z‖ ≤ R1 * R1 := by
      exact mul_le_mul hρ_bound hz_bound (norm_nonneg _) (le_of_lt hR1_pos)
    -- Use the fact that division preserves inequality for positive denominators
    have : ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R := by
      exact div_le_div_of_nonneg_right mult_bound (le_of_lt hR_pos)
    exact this

  -- Combine the bounds: ‖factor‖ ≥ R - R1²/R > 0
  rw [R_norm_eq] at triangle_ineq
  linarith [triangle_ineq, product_bound, key_positive]

lemma Bf_never_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R1))
    (ne_top : ∀ z ∈ closedBall 0 R1, analyticOrderAt f z ≠ ⊤) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1, Bf R R1 f z ≠ 0 := by
  intro z hz
  by_cases h_finite_zeros : (zerosetKfR R1 f).Finite
  swap
  · simp [Bf, h_finite_zeros]
  -- Use the factorization of Bf as product of numerator and Cf
  rw [lem_Bf_eq_prod_Cf R R1 f h_finite_zeros]
  -- Show the product is nonzero by showing each factor is nonzero
  apply mul_ne_zero
  · -- First factor: the product over zeros (numerator part) using lem:bl_num_nonzero
    exact lem_num_prod_never_zero_all R R1 hR1_pos hR1_lt_R f h_finite_zeros z hz
  · -- Second factor: Cf never zero using lem:C_never_zero
    apply lem_Cf_never_zero hf ne_top z hz

lemma log_Bf_le_log_B3
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 f z)) ≤ Real.log B := by
  intro z hz
  gcongr
  · refine norm_pos_iff.mpr <| ?_
    apply Bf_never_zero R R1 hR1_pos hR1_lt_R f
    · exact fun z hz ↦ h_f_analytic z (closedBall_subset_closedBall (by linarith) hz)
    · exact fun z hz ↦ order_ne_top h_f_analytic (by norm_num) ⟨0, (by simp), (by simp_all)⟩
        (closedBall_subset_closedBall (by linarith) hz)
    · simpa
  · exact lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R f (h_f_analytic.mono (closedBall_subset_closedBall hR_lt_1.le)) h_finite_zeros h_f_bound z (by linarith)

lemma log_Bf0_ge_0
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    0 ≤ Real.log (‖Bf R R1 f 0‖) := by
  exact Real.log_nonneg <| lem_mod_Bf_at_0_ge_1 R R1 hR1_pos hR1_lt_R f h_f_zero h_finite_zeros

def isLf (Lf : ℂ → ℂ) (f : ℂ → ℂ) (r R R1 : ℝ) : Prop :=
    AnalyticOnNhd ℂ Lf (closedBall 0 r) ∧ Lf 0 = 0 ∧
    (∀ z ∈ closedBall (0 : ℂ) r, deriv Lf z = logDeriv (Bf R R1 f) z) ∧
    ∀ z ∈ closedBall (0 : ℂ) r, (Lf z).re = Real.log (norm (Bf R R1 f z)) - Real.log (norm (Bf R R1 f 0))

lemma re_Lf_le_log_B
    (B r R R1 : ℝ)
    (hB : 1 < B)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) 
    (Lf : ℂ → ℂ)
    (hLf : isLf Lf f r R R1) :
    ∀ z, norm z ≤ r →
      Complex.re (Lf z) ≤ Real.log B := by
  intro z hz
  rw [hLf.2.2.2]
  · -- Apply log_Bf_le_log_B3 and log_Bf0_ge_0
    -- derive the required bound ‖z‖ ≤ R1 from ‖z‖ ≤ r and r < R1
    have hz_apply_BC_to_Lfle_R1 : ‖z‖ ≤ R1 := by linarith [hz, hr_lt_R1]
    have h1 := log_Bf_le_log_B3 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_f_bound z hz_apply_BC_to_Lfle_R1
    have h2 := log_Bf0_ge_0 R R1 hR1_pos hR1_lt_R f h_f_zero h_finite_zeros
    linarith
  · -- Show z is in the closed ball of radius r
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hz)

lemma apply_BC_to_Lf
    (B r1 r R R1 : ℝ)
    (hB : 1 < B)
    (hr1_pos : 0 < r1)
    (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B)
    (Lf : ℂ → ℂ)
    (hLf : isLf Lf f r R R1) :
    ∀ z, norm z ≤ r1 →
      norm (deriv Lf z) ≤
      (16 * Real.log B * r^2) / (r - r1)^3 := by
  classical
  intro z hz
  -- derive 0 < r from 0 < r1 and r1 < r
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
  -- instantiate L := Lf ... with the derived positivity proof
  let L := Lf
  -- L is analytic on a neighborhood of the closed ball of radius r
  have h_analytic_nhd :=
    hLf.1
  -- Build an open set U containing the closed ball where L is differentiable
  -- L(0) = 0
  have hL0 : L 0 = 0 := by
    exact hLf.2.1
  -- Re L ≤ log B on the closed ball of radius r
  have hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ Real.log B := by
    intro w hw
    have hw' : norm w ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact re_Lf_le_log_B B r R R1 hB hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_f_bound Lf hLf w hw'
  -- z ∈ closedBall 0 r1
  have hz' : z ∈ Metric.closedBall 0 r1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  -- Apply Borel–Carathéodory II
  have hBC :=
    borel_caratheodory_II hr_pos (Real.log_pos hB) hr1_pos hr1_lt_r h_analytic_nhd.analyticOn hL0 hre_L_le_M hz'
  -- conclude
  simpa [L] using hBC


-- Lemma 6: Lf_deriv_is_logBf_deriv
lemma Lf_deriv_is_logBf_deriv (hR1_lt_R : R1 < R) (hR1_pos : 0 < R1)
    (h_f_analytic : ∀ z ∈ closedBall 0 R1, AnalyticAt ℂ f z)
    (ne_top : ∀ z ∈ closedBall 0 R1, analyticOrderAt f z ≠ ⊤) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
      logDeriv (fun w ↦ Bf R R1 f w /
                           Bf R R1 f 0) z =
      logDeriv (fun w ↦ Bf R R1 f w) z := by
  intro z _
  -- Rewrite the division as multiplication by inverse
  have h_eq : (fun w ↦ Bf R R1 f w /
                       Bf R R1 f 0) =
              (fun w ↦ (Bf R R1 f 0)⁻¹ *
                       Bf R R1 f w) := by
    ext w
    rw [div_eq_mul_inv]
    ring
  rw [h_eq]
  -- Show that Bf ... 0 ≠ 0 using Bf_never_zero
  have h0_in_ball : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simp [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hR1_pos
  have h_Bf0_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ne_top 0 h0_in_ball
  -- Show that the inverse is non-zero
  have h_inv_ne_zero : (Bf R R1 f 0)⁻¹ ≠ 0 :=
    inv_ne_zero h_Bf0_ne_zero
  exact logDeriv_const_mul z _ h_inv_ne_zero

-- Lemma 7: Lfderiv_is_logderivBf

-- Continuing with the remaining lemmas...

-- Lemma 12: z_minus_rho_diff_nonzero
lemma z_minus_rho_diff_nonzero {R1 : ℝ} {f : ℂ → ℂ} :
    ∀ ρ ∈ zerosetKfR R1 f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    z - ρ ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ w - ρ) z := by
  intro ρ hρ z hz
  have hz_pair := (Set.mem_diff z).1 hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_pair.1
  have hz_notK : z ∉ zerosetKfR R1 f := hz_pair.2
  -- Show z ≠ ρ hence z - ρ ≠ 0
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz_notK (by simpa [h_eq] using hρ)
  have h_nonzero : z - ρ ≠ 0 := sub_ne_zero.mpr hz_ne_rho
  -- Differentiability of w ↦ w - ρ at z
  have hdiff : DifferentiableAt ℂ (fun w => w) z := differentiableAt_fun_id
  have hdiff_sub : DifferentiableAt ℂ (fun w => w - ρ) z := hdiff.sub_const ρ
  exact ⟨h_nonzero, hdiff_sub⟩

-- Lemma 13: blaschke_num_diff_nonzero
lemma blaschke_num_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) :
    ∀ ρ ∈ zerosetKfR R1 f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
    R - (star ρ) * z / R ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := by
  intro ρ hρ z hz
  constructor
  · intro hzero
    have hRne : (R : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (hR1_pos.trans hR1_lt_R)))
    -- From the equation R - conj(ρ) * z / R = 0, deduce conj(ρ) * z = R^2
    have heq : (R : ℂ) = (star ρ) * z / (R : ℂ) := sub_eq_zero.mp hzero
    have hmul := congrArg (fun t : ℂ => t * (R : ℂ)) heq
    have heq_mul : (R : ℂ) * (R : ℂ) = (star ρ) * z := by
      -- simplify the right-hand side
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hRne] using hmul
    -- Take norms and simplify
    have hnorm_eq : ‖(R : ℂ)‖ * ‖(R : ℂ)‖ = ‖ρ‖ * ‖z‖ := by
      simpa [Complex.norm_mul, Complex.norm_conj] using congrArg (fun t : ℂ => ‖t‖) heq_mul
    -- Bounds: ‖z‖ ≤ R and ‖ρ‖ ≤ R1
    have hz_norm_le : ‖z‖ ≤ R := by
      have hz' : dist z (0 : ℂ) ≤ R := (Metric.mem_closedBall.mp hz)
      simpa [dist_eq_norm] using hz'
    have hrho_norm_le : ‖ρ‖ ≤ R1 := by
      rcases hρ with ⟨hρ_ball, _hρ_zero⟩
      have : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_ball)
      simpa [dist_eq_norm] using this
    have hz_nonneg : 0 ≤ ‖z‖ := by simp
    have hR1_nonneg : 0 ≤ R1 := le_of_lt hR1_pos
    have hle : ‖ρ‖ * ‖z‖ ≤ R1 * R := by
      have h1 : ‖ρ‖ * ‖z‖ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hrho_norm_le hz_nonneg
      have h2 : R1 * ‖z‖ ≤ R1 * R := mul_le_mul_of_nonneg_left hz_norm_le hR1_nonneg
      exact le_trans h1 h2
    -- Evaluate ‖(R : ℂ)‖ as R (since R > 0)
    have hnorm_R : ‖(R : ℂ)‖ = R := by
      have h1 : ‖(R : ℂ)‖ = |R| := by simp
      simp [h1, abs_of_pos (hR1_pos.trans hR1_lt_R)]
    -- Rewrite the equality using hnorm_R
    have : R * R = ‖ρ‖ * ‖z‖ := by simpa [hnorm_R] using hnorm_eq
    have hle' : R * R ≤ R1 * R := by simpa [this] using hle
    -- But R1 * R < R * R since R > 0, hence RHS < LHS, contradiction
    have hposR : 0 < R := hR1_pos.trans hR1_lt_R
    have hposRR : 0 < R * R := by nlinarith [hposR]
    have hlt : R1 * R < R * R := by
      gcongr
    exact (lt_irrefl _ (lt_of_le_of_lt hle' hlt))
  · fun_prop

-- Lemma 14: blaschke_frac_diff_nonzero
lemma blaschke_frac_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) :
    ∀ ρ ∈ zerosetKfR R1 f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    (R - (star ρ) * z / R) / (z - ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro ρ hρ z hz
  -- Denominator: nonvanishing and differentiable
  have hden := z_minus_rho_diff_nonzero (R1:=R1) (f:=f) ρ hρ z hz
  have hden_ne : z - ρ ≠ 0 := hden.1
  have hden_diff : DifferentiableAt ℂ (fun w ↦ w - ρ) z := hden.2
  -- Extract membership in the smaller closed ball
  have hz_in_small : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 f := by
    simpa [Set.mem_diff] using hz
  have hz_small : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_in_small.1
  -- Show z ∈ closedBall 0 1 to use the numerator lemma
  have hz_dist_le_small : dist z (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hz_small
  have hRle : R ≤ 1 := le_of_lt hR_lt_1
  have hR1_le_R : R1 ≤ R := le_of_lt hR1_lt_R
  have hR1_le_1 : R1 ≤ 1 := le_trans hR1_le_R hRle
  have hz_ball1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hz_le1 : dist z (0 : ℂ) ≤ 1 := le_trans hz_dist_le_small hR1_le_1
    simpa [Metric.mem_closedBall] using hz_le1
  -- Numerator: nonvanishing and differentiable
  have hz_ballR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : dist z (0 : ℂ) ≤ R := le_trans hz_dist_le_small (le_of_lt hR1_lt_R)
    simpa [Metric.mem_closedBall] using hz_le_R
  have hnum := blaschke_num_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R ρ hρ z hz_ballR
  have hnum_ne : R - (star ρ) * z / R ≠ 0 := hnum.1
  have hnum_diff : DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := hnum.2
  -- Conclude
  refine And.intro ?_ ?_
  · intro h
    have h' : (R - (star ρ) * z / R) * (z - ρ)⁻¹ = 0 := by
      simpa [div_eq_mul_inv] using h
    rcases mul_eq_zero.mp h' with hnum0 | hinv0
    · exact hnum_ne hnum0
    · exact hden_ne (inv_eq_zero.mp hinv0)
  · exact hnum_diff.div hden_diff hden_ne

-- Lemma 15: blaschke_pow_diff_nonzero
lemma blaschke_pow_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) :
    ∀ ρ ∈ zerosetKfR R1 f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    ((R - (star ρ) * z / R) / (z - ρ)) ^ analyticOrderNatAt f ρ ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  intro ρ hρ z hz
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1
      ρ hρ z hz
  rcases hfrac with ⟨hne, hdiff⟩
  constructor
  · exact pow_ne_zero _ hne
  · simpa using hdiff.pow (analyticOrderNatAt f ρ)

-- Lemma 16: blaschke_prod_diff_nonzero
lemma blaschke_prod_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    (∏ ρ ∈ h_finite_zeros.toFinset, ((R - (star ρ) * z / R) / (z - ρ)) ^ analyticOrderNatAt f ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                        ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  intro z hz
  classical
  constructor
  · -- non-vanishing of the product
    have hne_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * z / R) / (z - ρ)) ^ analyticOrderNatAt f ρ ≠ 0 := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 ρ hρ' z hz
      exact hpair.1
    exact (Finset.prod_ne_zero_iff).2 hne_each
  · -- differentiability of the product
    have hdiff_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        DifferentiableAt ℂ
          (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 ρ hρ' z hz
      exact hpair.2
    -- Use DifferentiableAt.finset_prod and identify the function
    have hdiff :=
      (DifferentiableAt.finset_prod (u := h_finite_zeros.toFinset)
        (f := fun ρ => fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ)
        (x := z) hdiff_each)
    have hfun_eq :
        (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ)
        =
        (∏ ρ ∈ h_finite_zeros.toFinset,
            (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ)) := by
      funext w
      simp [Finset.prod_apply]
    exact hfun_eq.symm ▸ hdiff

-- Lemma 17: f_diff_nonzero_outside_Kf
lemma f_diff_nonzero_outside_Kf {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    f z ≠ 0 ∧ DifferentiableAt ℂ f z := by
  intro z hz
  -- unpack membership in the set difference
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 f := by
    simpa [Set.mem_diff] using hz
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 := hz'.1
  have hz_notin : z ∉ zerosetKfR R1 f := hz'.2
  -- show f z ≠ 0
  have hz_nonzero : f z ≠ 0 := by
    intro hfz
    exact hz_notin ⟨hz_in_R1, hfz⟩
  -- show differentiable at z using analyticity on closedBall 1
  have hR1_lt_1 : R1 < 1 := by linarith
  have hsubset1 :
      Metric.closedBall (0 : ℂ) R1 ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hR1_lt_1
  have hz_in_ball1 : z ∈ Metric.ball (0 : ℂ) 1 := hsubset1 hz_in_R1
  have hz_in_1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.ball_subset_closedBall hz_in_ball1
  have hAna : AnalyticAt ℂ f z := h_f_analytic z hz_in_1
  have hDiff : DifferentiableAt ℂ f z := hAna.differentiableAt
  exact ⟨hz_nonzero, hDiff⟩

-- Lemma 19: logDeriv_fprod_is_sum
lemma logDeriv_fprod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    logDeriv (fun w ↦ f w * ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z =
    logDeriv f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                            ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  intro z hz
  have hf' := f_diff_nonzero_outside_Kf (R:=R) (R1:=R1) (f:=f) hR1_lt_R hR_lt_1 h_f_analytic z hz
  rcases hf' with ⟨hf_ne, hf_diff⟩
  have hg' := blaschke_prod_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_finite_zeros z hz
  rcases hg' with ⟨hg_ne, hg_diff⟩
  rw [logDeriv_mul _ hf_ne hg_ne hf_diff hg_diff]

-- Lemma 20: logDeriv_Bf_is_sum

lemma div_mul_eq_mul_mul_inv_fun {α} (f A B : α → ℂ) :
  (fun w => (f w / A w) * B w) = (fun w => f w * (B w * (A w)⁻¹)) := by
  funext w
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma prod_num_mul_inv_den_eq_prod_ratio_fun_mem
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) / (∏ ρ ∈ K, (D ρ w) ^ (m ρ)) := by
          simp [div_eq_mul_inv]
    _ = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ)) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ)) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow_div :
              (N ρ w / D ρ w) ^ (m ρ)
                = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
            calc
              (N ρ w / D ρ w) ^ (m ρ)
                  = (N ρ w * (D ρ w)⁻¹) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
              _ = (N ρ w) ^ (m ρ) * ((D ρ w)⁻¹) ^ (m ρ) := by
                        simpa using (mul_pow (N ρ w) ((D ρ w)⁻¹) (m ρ))
              _ = (N ρ w) ^ (m ρ) * ((D ρ w) ^ (m ρ))⁻¹ := by
                        simp
              _ = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
          simpa using hpow_div.symm

lemma logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
  (hfg : f =ᶠ[nhds z] g) : logDeriv f z = logDeriv g z := by
  unfold logDeriv
  simp
  rw [hfg.deriv_eq, hfg.eq_of_nhds]

lemma logDeriv_Bf_is_sum (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
:
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \
          zerosetKfR R1 f,
    logDeriv (Bf R R1 f) z =
    logDeriv f z +
      logDeriv
        (fun w ↦
          ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  classical
  intro z hz
  -- Abbreviations
  set K : Finset ℂ := h_finite_zeros.toFinset
  -- Define denominator and numerator products and the ratio product
  let A : ℂ → ℂ := fun w => ∏ ρ ∈ K, (w - ρ) ^ analyticOrderNatAt f ρ
  let BN : ℂ → ℂ := fun w => ∏ ρ ∈ K, (R - (star ρ) * w / R) ^ analyticOrderNatAt f ρ
  let RatProd : ℂ → ℂ :=
    fun w => ∏ ρ ∈ K, ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ
  -- Establish: Bf is eventually equal to f times the product of ratios near z
  set S : Set ℂ := zerosetKfR R1 f
  have hS_fin : S.Finite := h_finite_zeros
  have hU_open : IsOpen Sᶜ := hS_fin.isClosed.isOpen_compl
  have hz_notin : z ∉ S := by
    rcases hz with ⟨_, hnotin⟩; exact hnotin
  have hzU : z ∈ Sᶜ := by simpa [Set.mem_compl] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hzU
  have h_ev :
      (fun w ↦ Bf R R1 f w)
        =ᶠ[nhds z]
      (fun w ↦ f w * RatProd w) := by
    refine Filter.eventually_of_mem hU_mem ?_
    intro w hwU
    have hw_notin : w ∉ S := by simpa [Set.mem_compl] using hwU
    -- Rewrite Bf and Cf at points away from the zero set
    have hBf_w :
        Bf R R1 f w
          = Cf R1 f  w * BN w := by
      simp [Bf, BN, K, h_finite_zeros, S]
    have hCf_w :
        Cf R1 f w
          = f w / A w := by
      simp [Cf, S, A, K, hw_notin, h_finite_zeros]
    -- Use functional identities to simplify to f * RatProd
    have h_eq1 := div_mul_eq_mul_mul_inv_fun (f := f) (A := A) (B := BN)
    have h_eq1_w : (f w / A w) * BN w = f w * (BN w * (A w)⁻¹) := by
      simpa using congrArg (fun g : (ℂ → ℂ) => g w) h_eq1
    have h_eq2 :=
      prod_num_mul_inv_den_eq_prod_ratio_fun_mem
        (K := K)
        (N := fun ρ w ↦ (R - (star ρ) * w / R))
        (D := fun ρ w ↦ (w - ρ))
        (m := fun ρ ↦ analyticOrderNatAt f ρ)
    have h_eq2_w : BN w * (A w)⁻¹ = RatProd w := by
      simpa [BN, A, RatProd] using congrArg (fun g : (ℂ → ℂ) => g w) h_eq2
    -- Chain the equalities
    calc
      Bf R R1 f w
          = (f w / A w) * BN w := by simpa [hCf_w] using hBf_w
      _ = f w * (BN w * (A w)⁻¹) := h_eq1_w
      _ = f w * RatProd w := by simp [h_eq2_w]
  -- Transfer equality to logDeriv at z
  have hlog_congr := logDeriv_congr_of_eventuallyEq (f := fun w ↦
      Bf R R1 f w)
      (g := fun w ↦ f w * RatProd w) (z := z) h_ev
  -- Apply product rule to the RHS
  have hsum :=
    (logDeriv_fprod_is_sum (R:=R) (R1:=R1) (f:=f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_finite_zeros z hz)
  simpa [RatProd, K] using hlog_congr.trans hsum

-- Lemma 21: logDeriv_def_as_frac
lemma logDeriv_def_as_frac {f : ℂ → ℂ} {z : ℂ} :
    logDeriv f z = deriv f z / f z := by
  simp [logDeriv]

def ball_containment {r R1 : ℝ} (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (z : ℂ) (hz : z ∈ Metric.closedBall 0 r) : z ∈ Metric.closedBall 0 R1 := by
  simp at *
  exact le_trans hz (le_of_lt hr_lt_R1)

theorem in_r_minus_kf {R1 r : ℝ} {f : ℂ → ℂ}
  (hr_pos : 0 < r)
  (hr_lt_R1 : r < R1)
  (z : ℂ)
  (hz : z ∈ Metric.closedBall 0 r \ zerosetKfR R1 f) :
   z ∈ Metric.closedBall 0 R1 \ zerosetKfR R1 f := by
  obtain ⟨h1, h2⟩ := hz
  have : z ∈ Metric.closedBall 0 R1 := by
    apply ball_containment hr_pos hr_lt_R1 z h1
  constructor <;> assumption

-- Lemma 22: Lf_deriv_step1
lemma Lf_deriv_step1 (hR1_pos : 0 < R1) (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1)) (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 f,
    deriv Lf z =
    deriv f z / f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                                ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  have ne_top : ∀ z ∈ closedBall 0 R1, analyticOrderAt f z ≠ ⊤ := by
    refine fun z hz ↦ order_ne_top h_f_analytic (by norm_num) ⟨0, (by simp), (by simp_all)⟩ (closedBall_subset_closedBall (by linarith) hz)
  intro z hz
  -- Extract closedBall membership
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r ∧ z ∉ zerosetKfR R1 f := by
    simpa [Set.mem_diff] using hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := hz'.1
  -- From Lfderiv_is_logderivBf
  have hLf :=
  --
    (Lf_deriv_is_logBf_deriv hR1_lt_R hR1_pos (fun z hz ↦ h_f_analytic z (closedBall_subset_closedBall (by linarith) hz)) ne_top
      z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)).symm
  -- Expand logDeriv of Bf into sum
  have hsum :
      logDeriv (fun w ↦
        Bf R R1 f           w) z =
      logDeriv f z +
        logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
    have h :=
      (logDeriv_Bf_is_sum (R := R) (R1 := R1) (f := f)
        h_finite_zeros hR1_lt_R hR_lt_1 hR1_pos h_f_analytic z (in_r_minus_kf hr_pos hr_lt_R1 _ hz))
    simpa using h
  -- Turn logDeriv f into deriv f / f using differentiability and nonvanishing
  obtain ⟨hf_ne, hfdiff⟩ :=
    f_diff_nonzero_outside_Kf (R := R) (R1 := R1) (f := f)
      hR1_lt_R hR_lt_1 h_f_analytic z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have hfrac : logDeriv f z = deriv f z / f z :=
    logDeriv_def_as_frac (f := f) (z := z)
  -- Combine
  -- First, identify deriv Lf with the logarithmic derivative of Bf at z
  have hLf_eq_logDerivBf :
      deriv Lf z =
      logDeriv (fun w ↦
        Bf R R1 f w) z := by
    -- Unfold Lf to use the derivative property from log_of_analytic
    -- and then rewrite deriv B / B as logDeriv B.
    have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r := hz_ball
    exact h_Lf.2.2.1 z hz_in_r
  -- Chain the identities: deriv Lf = logDeriv Bf = logDeriv f + logDeriv(prod),
  -- then rewrite logDeriv f as deriv f / f.
  calc
    _
        = logDeriv (fun w ↦
            Bf R R1 f
              w) z := hLf_eq_logDerivBf
    _ = logDeriv f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := hsum
    _ = deriv f z / f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
            simp [hfrac]

-- Lemma 23: logDeriv_prod_is_sum
lemma logDeriv_prod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, logDeriv (fun w ↦
              ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
  intro z hz
  have hdiff : ∀ ρ ∈ h_finite_zeros.toFinset,
      DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 ρ hρmem z hz
    exact h.2
  have hne : ∀ ρ ∈ h_finite_zeros.toFinset,
      ((R - (star ρ) * z / R) / (z - ρ)) ^ analyticOrderNatAt f ρ ≠ 0 := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 ρ hρmem z hz
    exact h.1
  rw [logDeriv_prod hne hdiff]

-- Lemma 24: logDeriv_power_is_mul
lemma logDeriv_power_is_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z =
    analyticOrderNatAt f ρ * logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz ρ hρFin
  have hρmem : ρ ∈ zerosetKfR R1 f := by
    simpa using (h_finite_zeros.mem_toFinset.mp hρFin)
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1
      ρ hρmem z hz
  rcases hfrac with ⟨_hneq, hdiff⟩
  rw [logDeriv_fun_pow hdiff]

-- Lemma 25: logDeriv_prod_is_sum_mul
lemma logDeriv_prod_is_sum_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ analyticOrderNatAt f ρ) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ *
                                    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have hsum :=
    logDeriv_prod_is_sum (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_finite_zeros z hz
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  exact
    logDeriv_power_is_mul (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_finite_zeros z hz ρ hρ

-- Lemma 26: Lf_deriv_step2
lemma Lf_deriv_step2  (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 f,
    deriv Lf z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ *
                                                       logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have h1 :=
    Lf_deriv_step1 h_finite_zeros hR1_pos h_f_analytic hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 h_f_zero Lf h_Lf z hz
  have hsum :=
    logDeriv_prod_is_sum_mul (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have h2 := congrArg (fun t => deriv f z / f z + t) hsum
  exact h1.trans h2

-- Lemma 27: logDeriv_Blaschke_is_diff
lemma logDeriv_Blaschke_is_diff {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
    logDeriv (fun w ↦ R - (star ρ) * w / R) z - logDeriv (fun w ↦ w - ρ) z := by
  intro z hz ρ hρ
  have hρ_set : ρ ∈ zerosetKfR R1 f := by
    exact (Set.Finite.mem_toFinset (hs := h_finite_zeros) (a := ρ)).mp hρ
  rcases hz with ⟨hz_in, hz_notin⟩
  have hden := z_minus_rho_diff_nonzero
      ρ hρ_set z ⟨hz_in, hz_notin⟩
  rcases hden with ⟨hden_nz, hden_diff⟩
  have hz_le : ‖z‖ ≤ R1 := by
    simpa [Metric.closedBall, dist_eq_norm] using hz_in
  have hle1 : R1 < 1 := by linarith [hR1_lt_R, hR_lt_1]
  have hz_in1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have : ‖z‖ ≤ 1 := le_of_lt (hz_le.trans_lt hle1)
    simpa [Metric.closedBall, dist_eq_norm] using this
  have hz_inR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : ‖z‖ ≤ R := by
      calc ‖z‖ ≤ R1 := hz_le
      _ ≤  R := le_of_lt hR1_lt_R
    simpa [Metric.closedBall, dist_eq_norm] using hz_le_R
  have hnum := blaschke_num_diff_nonzero hR1_pos hR1_lt_R
      ρ hρ_set z hz_inR
  rcases hnum with ⟨hnum_nz, hnum_diff⟩
  rw [logDeriv_div z hnum_nz hden_nz hnum_diff hden_diff]

-- Lemma 28: logDeriv_linear
lemma logDeriv_linear {a b : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ a * w + b) z = a / (a * z + b) := by
  -- derivative of w ↦ a * w is a
  have h_id : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id _
  have h_mul' : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa [one_mul] using (h_id.const_mul a)
  have h_deriv_mul : deriv (fun w : ℂ => a * w) z = a := h_mul'.deriv
  -- unfold logDeriv and compute
  simp [logDeriv, h_deriv_mul]

-- Lemma 29: logDeriv_denominator
lemma logDeriv_denominator {ρ : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ w - ρ) z = 1 / (z - ρ) := by
  have h :=
    logDeriv_linear (a := (1 : ℂ)) (b := -ρ) (z := z)
  simpa [one_mul, sub_eq_add_neg] using h

-- Lemma 30: logDeriv_numerator_pre
lemma logDeriv_numerator_pre {R : ℝ} {ρ : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = -(star ρ) / R / (R - (star ρ) * z / R) := by
  classical
  -- Put the function in the linear form b + a * w
  let a : ℂ := -(star ρ) / (R : ℂ)
  let b : ℂ := (R : ℂ)
  have hlin : (fun w : ℂ ↦ (R : ℂ) - (star ρ) * w / (R : ℂ)) = (fun w : ℂ ↦ b + a * w) := by
    funext w
    -- rewrite as b + a*w
    simp [a, b, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
          add_comm, add_left_comm, add_assoc]
  -- Compute the derivative of b + a * w
  have hderiv_add : deriv (fun w : ℂ => b + a * w) z =
      deriv (fun _ : ℂ => b) z + deriv (fun y : ℂ => a * y) z := by
    simp
  have hderiv_ab : deriv (fun w : ℂ => b + a * w) z = a := by
    simp [deriv_const, deriv_const_mul, mul_comm]
  -- Now compute the logarithmic derivative and rewrite back
  simp [hlin, logDeriv, hderiv_ab, a, b, sub_eq_add_neg, div_eq_mul_inv,
         mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

lemma star_ne_zero_of_ne_zero {ρ : ℂ} (hρ : ρ ≠ 0) : star ρ ≠ 0 := by
  -- Use that conjugation preserves (and reflects) zero over ℂ
  -- This is true in any star semiring: star x = 0 ↔ x = 0
  -- We use the forward direction: if star ρ = 0 then ρ = 0, contradicting hρ
  intro h
  -- apply the equivalence star_eq_zero.mp
  have : ρ = 0 := (star_eq_zero).1 h
  exact hρ this

lemma field_identity_general {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) : (-(b/a)) / (a - c*b/a) = (1 : K) / (c - a^2/b) := by
  -- Multiply numerator and denominator by -a/b
  field_simp
  rw [← div_neg]
  ring

lemma complex_identity_from_field {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hρ : ρ ≠ 0) (hden : (R:ℂ) - (star ρ) * z / R ≠ 0) : (-(star ρ) / (R:ℂ)) / ((R:ℂ) - (star ρ) * z / R) = (1 : ℂ) / (z - (R:ℂ)^2 / (star ρ)) := by
  have ha : (R : ℂ) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hR)
  have hb : star ρ ≠ 0 := star_ne_zero_of_ne_zero hρ
  have hden' : (R : ℂ) - z * (star ρ) / (R : ℂ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hden
  have h := field_identity_general (K := ℂ) (a := (R : ℂ)) (b := star ρ) (c := z) ha hb
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h

lemma logDeriv_numerator_rearranged {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hrho : ρ ≠ 0) (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0) : -(star ρ) / R / ((R : ℂ) - (star ρ) * z / R) = 1 / (z - (R : ℂ)^2 / (star ρ)) := by
  simpa using (complex_identity_from_field (R:=R) (ρ:=ρ) (z:=z) (hR:=hR) (hρ:=hrho) (hden:=h_denom_ne_zero))

-- Lemma 32: logDeriv_numerator
lemma logDeriv_numerator {R : ℝ} {ρ : ℂ} {z : ℂ}
    (hR : R ≠ 0)
    (hrho : ρ ≠ 0)
    (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0):
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = 1 / (z - R^2 / (star ρ)) := by
  rw [logDeriv_numerator_pre, logDeriv_numerator_rearranged]
  <;> assumption

-- Lemma 33: logDeriv_Blaschke_is_diff_frac
lemma logDeriv_Blaschke_is_diff_frac {R R1 : ℝ} {f : ℂ → ℂ}
     (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ ρ ∈ h_finite_zeros.toFinset,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f , logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
         1 / (z - R^2 / (star ρ)) - 1 / (z - ρ) := by
  intro ρ hρ z hz
  -- Apply the division rule for logDeriv using logDeriv_Blaschke_is_diff
  have h_div := logDeriv_Blaschke_is_diff (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_finite_zeros z hz ρ hρ
  -- Evaluate logDeriv(R - (star ρ) * w / R) using logDeriv_numerator
  have hρ_mem : ρ ∈ zerosetKfR R1 f := by
    exact (h_finite_zeros.mem_toFinset).mp hρ
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h_eq
    -- ρ = 0 would mean f(0) = 0, but h_f_zero says f(0) = 1
    have : f 0 = 0 := by simpa [h_eq] using hρ_mem.2
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (this.symm.trans h_f_zero)
  have hR_ne_zero : R ≠ 0 := ne_of_gt (hR1_pos.trans hR1_lt_R)
  have h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0 := by
    -- This follows from blaschke_num_diff_nonzero
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := by
      have hle : R1 < R := hR1_lt_R
      apply Metric.closedBall_subset_closedBall (le_of_lt hle)
      exact hz.1
    have h := blaschke_num_diff_nonzero hR1_pos hR1_lt_R ρ hρ_mem z hz_ball
    exact h.1
  have h_num := logDeriv_numerator hR_ne_zero hρ_ne_zero h_denom_ne_zero
  -- Evaluate logDeriv(z - ρ) using logDeriv_denominator
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz.2 (by simpa [h_eq] using hρ_mem)
  have h_den := logDeriv_denominator (z := z) (ρ := ρ)
  -- Substitute the results back
  rw [h_div, h_num, h_den]

-- Lemma 34: Lf_deriv_step3
lemma Lf_deriv_step3   (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 f,
    deriv Lf z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ * (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) := by
  intro z hz
  -- Assuming Lf_deriv_step2 is also corrected to remove B
  rw [Lf_deriv_step2 h_finite_zeros hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero Lf h_Lf z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  exact logDeriv_Blaschke_is_diff_frac hR1_pos hR1_lt_R hR_lt_1 h_f_zero h_finite_zeros ρ hρ z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)

-- Lemma 36: sum_rearranged
lemma sum_rearranged {R R1 : ℝ} {f : ℂ → ℂ}
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 f,
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ *
                                    (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) =
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (star ρ)) -
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ) := by
  intro z hz
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext ρ
  rw [mul_sub, mul_one_div, mul_one_div]

-- Lemma 37: Lf_deriv_final_formula
lemma Lf_deriv_final_formula (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 f,
    deriv Lf z =
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ) +
                      ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (star ρ)) := by
  intro z hz
  -- Apply Lf_deriv_step3 with the corrected, simpler signature
  rw [Lf_deriv_step3 h_finite_zeros hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero Lf h_Lf z hz]
  -- Apply sum_rearranged with a simpler signature
  rw [sum_rearranged h_finite_zeros z hz]
  -- Rearrange terms
  ring

-- Lemma 38: rearrange_Lf_deriv
lemma rearrange_Lf_deriv (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 f,
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ) =
    deriv Lf z -
    ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (star ρ)) := by
  intro z hz
  -- The call to Lf_deriv_final_formula is now simpler as it no longer needs hB
  have h_final := Lf_deriv_final_formula h_finite_zeros hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero Lf h_Lf z hz
  rw [h_final]
  ring

-- Lemma 40: target_inequality_setup
lemma target_inequality_setup  (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (Lf : ℂ → ℂ)
    (h_Lf : isLf Lf f r R R1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 f,
  ‖deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ)‖ ≤
  ‖deriv Lf z‖ +
  ‖∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (star ρ))‖ := by
  intro z hz
  have hrearr := rearrange_Lf_deriv h_finite_zeros hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero Lf h_Lf z hz
  -- The rest of the proof is a direct application of the triangle inequality.
  -- We want to show ‖A‖ ≤ ‖B‖ + ‖C‖, where hrearr gives A = B - C.
  rw [hrearr]
  exact norm_sub_le _ _
-- Additional helper lemmas needed for the bounds

-- Additional bound lemmas

lemma norm_Rsq_div_conj (R : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0) : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ := by
  have hb : star ρ ≠ 0 := by
    intro h
    have h' := congrArg star h
    -- star (star ρ) = 0, hence ρ = 0
    have : ρ = 0 := by simpa [star_star] using h'
    exact hρ this
  have hnormR : ‖(R^2 : ℂ)‖ = (R^2 : ℝ) := by
    have h := (RCLike.norm_ofReal (K:=ℂ) (R^2))
    simp [abs_of_nonneg (sq_nonneg R)]
  calc
    ‖((R^2 : ℂ) / (star ρ))‖
        = ‖(R^2 : ℂ)‖ / ‖star ρ‖ := norm_div _ _
    _ = (R^2 : ℝ) / ‖ρ‖ := by
      simp [hnormR]

lemma zerosetKfR_subset_closedBall {R1 : ℝ} {f : ℂ → ℂ} :
  zerosetKfR R1 f ⊆ Metric.closedBall (0 : ℂ) R1 := by
  intro ρ hρ
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  exact hmem.left

lemma mem_zerosetKfR_ne_zero_of_f0_eq_one {R1 : ℝ} {f : ℂ → ℂ}
  (hf0 : f 0 = 1) {ρ : ℂ} (hρ : ρ ∈ zerosetKfR R1 f) : ρ ≠ 0 := by
  intro hρ0
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  have hzero : f 0 = 0 := by simpa [hρ0] using hmem.right
  have h10 : (1 : ℂ) ≠ 0 := one_ne_zero
  exact h10 (by simp [hf0] at hzero)

lemma norm_sub_ge_norm_sub (x y : ℂ) : ‖x - y‖ ≥ ‖y‖ - ‖x‖ := by
  have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_add_le (y - x) x
  have h' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := (sub_le_iff_le_add).mpr htri
  have hsymm : ‖y - x‖ = ‖x - y‖ := by
    simpa [sub_eq_add_neg, add_comm] using (norm_neg (x - y))
  simpa [hsymm] using h'


lemma mem_zerosetKfR_norm_le {R1 : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
  (hρ : ρ ∈ zerosetKfR R1 f) : ‖ρ‖ ≤ R1 := by
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 :=
    (zerosetKfR_subset_closedBall (R1 := R1) (f := f)) hρ
  have hdist : dist ρ (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hmem
  simpa [dist_eq_norm, sub_zero] using hdist

lemma lem_sum_bound_step2 {R R1: ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
      (∑ ρ ∈ h_finite_zeros.toFinset,
          (analyticOrderNatAt f ρ : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ (1/(R^2/R1 - R1)) *
          (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ)) := by
  classical
  intro z hz
  rcases hz with ⟨hzball, _hznotin⟩
  have hz_norm : ‖z‖ ≤ R1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
  -- Define the index finset
  set S := h_finite_zeros.toFinset
  have hS_spec : ∀ {ρ : ℂ}, ρ ∈ S → ρ ∈ zerosetKfR R1 f := by
    intro ρ hρ
    have hiff := (Set.Finite.mem_toFinset (hs := h_finite_zeros) : ρ ∈ S ↔ ρ ∈ zerosetKfR R1 f)
    exact (Iff.mp hiff) hρ
  -- Termwise bound and then sum
  have hsum_le :
      (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ ∑ ρ ∈ S, (1/(R^2/R1 - R1)) * (analyticOrderNatAt f ρ : ℝ) := by
    refine Finset.sum_le_sum ?termwise
    intro ρ hρS
    have hρmem : ρ ∈ zerosetKfR R1 f := hS_spec hρS
    have hρ_ne : ρ ≠ 0 :=
      mem_zerosetKfR_ne_zero_of_f0_eq_one (R1 := R1)
        (f := f) h_f_zero hρmem
    have hρ_norm : ‖ρ‖ ≤ R1 := mem_zerosetKfR_norm_le (R1 := R1)
      (f := f) hρmem
    have hpt : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1/(R^2/R1 - R1) := by
      -- Use triangle inequality and norms
      have h_Rsq_norm : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ :=
        norm_Rsq_div_conj R ρ hρ_ne
      have h_lower_bound : ‖z - (R^2 : ℂ) / (star ρ)‖ ≥ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ :=
        norm_sub_ge_norm_sub z ((R^2 : ℂ) / (star ρ))
      -- Since ‖ρ‖ ≤ R1 and ‖ρ‖ > 0, we have ‖((R^2 : ℂ) / (star ρ))‖ ≥ R^2/R1
      have hρ_pos : 0 < ‖ρ‖ := by
        simpa [norm_pos_iff] using hρ_ne
      have h_Rsq_bound : R^2/R1 ≤ ‖((R^2 : ℂ) / (star ρ))‖ := by
        rw [h_Rsq_norm]
        exact div_le_div_of_nonneg_left (sq_nonneg R) hρ_pos hρ_norm
      have h_combined : R^2/R1 - R1 ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        calc R^2/R1 - R1
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - R1 := by linarith [h_Rsq_bound]
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ := by linarith [hz_norm]
        _ ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := h_lower_bound
      have h_pos_denom : 0 < R^2/R1 - R1 := by
        have h_R_pos : 0 < R := by linarith [hR1_pos, hR1_lt_R]
        have h_Rsq_pos : 0 < R^2 := sq_pos_of_pos h_R_pos
        calc R^2/R1 - R1
        _ = (R^2 - R1*R1)/R1 := by field_simp
        _ = (R - R1)*(R + R1)/R1 := by ring
        _ > 0 := by
          apply div_pos
          · apply mul_pos
            · linarith [hR1_lt_R]
            · linarith [hR1_pos, hR1_lt_R]
          · exact hR1_pos
      have h_pos_norm : 0 < ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        apply lt_of_lt_of_le h_pos_denom h_combined
      -- Use the basic inequality: if 0 < a ≤ b then 1/b ≤ 1/a
      have h_reciprocal : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1 / (R^2/R1 - R1) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · exact h_pos_denom
        · exact h_combined
      exact h_reciprocal
    have hmnonneg : 0 ≤ (analyticOrderNatAt f ρ : ℝ) := by
      exact_mod_cast (Nat.zero_le (analyticOrderNatAt f ρ))
    have hmul := mul_le_mul_of_nonneg_left hpt hmnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  -- pull out the constant on the RHS sum
  rw [← Finset.mul_sum] at hsum_le
  exact hsum_le

-- 1/((R^2/R_1 - R_1) log(R/R_1))

lemma sq_div_sub_pos (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) : 0 < b^2/a - a := by
  -- Convert the inequality to a < b^2/a
  rw [sub_pos]
  -- Use lt_div_iff₀ to convert a < b^2/a to a * a < b^2
  rw [lt_div_iff₀ ha_pos]
  -- Rewrite a * a as a^2
  rw [← pow_two]
  -- Now we need a^2 < b^2, which follows from a < b for positive numbers
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  apply pow_lt_pow_left₀ hab ha_nonneg
  norm_num --lem_square_inequality_strict ha_pos hab

lemma final_sum_bound {R R1 B : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (hB : 1 < B)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f,
    ‖∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (star ρ))‖ ≤
    1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
  intro z hz
  -- Step 1: Use triangle inequality (norm_sum_le)
  have h_norm_bound := norm_sum_le h_finite_zeros.toFinset (fun ρ => analyticOrderNatAt f ρ / (z - R^2 / (star ρ)))

  -- Step 2: Simplify norm of each term
  have h_sum_eq : ∑ ρ ∈ h_finite_zeros.toFinset, ‖analyticOrderNatAt f ρ / (z - R^2 / (star ρ))‖ =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ) / ‖z - R^2 / (star ρ)‖ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast]

  -- Step 3: Apply lem_sum_bound_step2 (first lemma from informal proof)
  have h_step2 := lem_sum_bound_step2 hR1_pos hR1_lt_R h_f_zero h_finite_zeros z hz

  -- Step 4: Apply lem_sum_m_rho_bound
  have h_f_nonzero : f 0 ≠ 0 := by rw [h_f_zero]; norm_num
  have h_f_bounded_alt : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B := by
    intro w hw
    exact h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw))
  have h_sum_bound := lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R f (h_f_analytic.mono (closedBall_subset_closedBall hR_lt_1.le)) h_f_zero h_finite_zeros h_f_bounded_alt

  -- Step 5: Establish needed positivity properties
  have h_pos : 0 < R^2/R1 - R1 := sq_div_sub_pos R1 R hR1_pos hR1_lt_R
  have h_ratio_gt_one : 1 < R/R1 := by
    rw [one_lt_div_iff]
    left
    exact ⟨hR1_pos, hR1_lt_R⟩
  have h_log_pos : 0 < Real.log (R/R1) := Real.log_pos h_ratio_gt_one

  calc ‖∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - R^2 / (star ρ))‖
    ≤ ∑ ρ ∈ h_finite_zeros.toFinset, ‖analyticOrderNatAt f ρ / (z - R^2 / (star ρ))‖ := h_norm_bound
    _ = ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ) / ‖z - R^2 / (star ρ)‖ := h_sum_eq
    _ ≤ (1/(R^2/R1 - R1)) * (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderNatAt f ρ : ℝ)) := h_step2
    _ ≤ (1/(R^2/R1 - R1)) * ((1/Real.log (R/R1)) * Real.log B) := by
              apply mul_le_mul_of_nonneg_left h_sum_bound (div_nonneg zero_le_one (le_of_lt h_pos))
    _ = 1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
      field_simp [ne_of_gt h_pos, ne_of_gt h_log_pos]

lemma Lf_exists (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (hR1_pos : 0 < R1)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1) :
    ∃ Lf : ℂ → ℂ, isLf Lf f r R R1 := by
  let B_f := Bf R R1 f
  have h_Bf_analytic : AnalyticOnNhd ℂ B_f (Metric.closedBall (0 : ℂ) R) :=
    Bf_is_analytic_on_disk R R1 hR_lt_1 f h_f_analytic
  have h_Bf_ne_zero : ∀ w ∈ Metric.closedBall (0 : ℂ) R1, B_f w ≠ 0 := by
    intro w hw
    refine Bf_never_zero R R1 hR1_pos hR1_lt_R f (fun z hz ↦ ?_) (fun z hz ↦ ?_) w hw
    · exact h_f_analytic z <| closedBall_subset_closedBall (by linarith) hz
    · refine order_ne_top h_f_analytic (by norm_num) ?_ (closedBall_subset_closedBall (by linarith) hz)
      exact ⟨0, (by simp), (by simp_all)⟩
  -- Apply lem:log_of_analytic
  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := log_of_analytic_open hR1_pos
    (h_Bf_analytic.mono (fun z hz ↦ (by simp_all; linarith)))
    (fun z hz ↦ h_Bf_ne_zero z (by simp_all; linarith))
  have bs := closedBall_subset_ball (x := (0 : ℂ)) hr_lt_R1
  refine ⟨J, hJ1.mono bs, hJ2, fun z hz ↦ hJ3 z (bs hz), fun z hz ↦ (hJ4 z (bs hz)).symm⟩

-- Now, we can fix the `final_inequality` lemma.
lemma final_inequality
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic :
      AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 f,

        ‖(deriv f z / f z
          - ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ))‖
      ≤
      16 * r^2 / ((r - r1)^3) * Real.log B
        + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
  have hr_pos : 0 < r := by linarith [hr1pos, hr1_lt_r]
  have hR1_pos : 0 < R1 := by linarith [hr_pos, hr_lt_R1]
  obtain ⟨Lf, h_Lf⟩ := Lf_exists hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero
  intro z hz
  -- Lift z from r1-ball to r-ball (needed for target_inequality_setup)
  have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 f := by
    constructor
    · apply Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_r)
      exact hz.1
    · exact hz.2

  -- Apply target_inequality_setup (from informal proof)
  have hineq :=
    target_inequality_setup h_finite_zeros hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero Lf h_Lf z hz_in_r

  -- Lift z from r1-ball to R1-ball (needed for final_sum_bound)
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 f := by
    constructor
    · apply Metric.closedBall_subset_closedBall
      exact le_of_lt (lt_trans hr1_lt_r hr_lt_R1)
      exact hz.1
    · exact hz.2

  -- Apply final_sum_bound (from informal proof)
  have hsum :=
    final_sum_bound hR1_pos hR1_lt_R hR_lt_1 hB h_f_analytic h_f_zero h_finite_zeros h_f_bounded z hz_in_R1

  -- Apply apply_BC_to_Lf (from informal proof)
  have hz_le_r1 : ‖z‖ ≤ r1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1

  -- Convert ‖z‖ ≤ r1 to norm z ≤ r1 (they are definitionally equal)
  have hz_abs : ‖z‖ ≤ r1 := hz_le_r1

  have h_BC := apply_BC_to_Lf
    (B := B) (r1 := r1) (r := r) (R := R) (R1 := R1)
    (hB := hB) (hr1_pos := hr1pos) (hr1_lt_r := hr1_lt_r) (hr_lt_R1 := hr_lt_R1)
    (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
    (f := f) (h_f_analytic := h_f_analytic) (h_f_zero := h_f_zero)
    (h_finite_zeros := h_finite_zeros)
    (h_f_bound := fun w hw => h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw)))
    Lf h_Lf z hz_abs

  -- Convert norm to norm and rearrange the bound
  have hLf : ‖deriv Lf z‖ ≤
             16 * r^2 / ((r - r1)^3) * Real.log B := by
    -- h_BC gives: norm (...) ≤ (16 * Real.log B * r^2) / (r - r1)^3
    -- We need: ‖...‖ ≤ 16 * r^2 / ((r - r1)^3) * Real.log B
    -- norm and ‖·‖ are definitionally equal
    convert h_BC using 1
    -- Rearrange: (16 * Real.log B * r^2) / (r - r1)^3 = 16 * r^2 / ((r - r1)^3) * Real.log B
    ring

  exact le_trans hineq (add_le_add hLf hsum)


-- Lemma 43: final_ineq1
lemma final_ineq1
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall 0 1))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 f).Finite)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 f,
    ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset,
                 analyticOrderNatAt f ρ / (z - ρ)‖ ≤
    (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log B := by
  intro z hz
  -- Get the bound with separate terms from final_inequality
  have h_bound : ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset, analyticOrderNatAt f ρ / (z - ρ)‖ ≤
      16 * r^2 / ((r - r1)^3) * Real.log B + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
    apply final_inequality <;> assumption
  -- Factor out Real.log B using right distributivity: a * c + b * c = (a + b) * c
  rw [← add_mul] at h_bound
  exact h_bound
