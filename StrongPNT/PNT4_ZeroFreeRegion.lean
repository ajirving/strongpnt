import StrongPNT.PNT3_RiemannZeta
import StrongPNT.Z0
import Mathlib.Analysis.Meromorphic.Divisor

def zeroZ : Set ℂ := {s : ℂ | riemannZeta s = 0}

def ZetaZerosNearPoint (t : ℝ) : Set ℂ := { ρ : ℂ | ρ ∈ zeroZ ∧ ‖ρ - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) }

private lemma riemannZeta_correction_differentiable :
    Differentiable ℂ (Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1) := by
  let H : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1
  change Differentiable ℂ H
  -- Show differentiability everywhere by splitting on s = 1.
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · -- differentiable at 1 via removable singularity: differentiable on punctured nhds + continuity
    refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · -- differentiable on punctured nhds around 1
      filter_upwards [self_mem_nhdsWithin] with t ht
      -- On t ≠ 1, H agrees with (t-1)*ζ t; prove differentiableAt via congr
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
        have h2 : DifferentiableAt ℂ riemannZeta t :=
          (differentiableAt_riemannZeta ht)
        fun_prop (disch := assumption)
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds ht] with u hu using by
        simp [H, Function.update_of_ne hu]
    · -- continuity of H at 1 from the known residue/limit lemma
      simpa [H, continuousAt_update_same] using riemannZeta_residue_one
  · -- s ≠ 1: H agrees with (s-1)ζ(s), hence differentiable
    have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) s := by
      have h2 : DifferentiableAt ℂ riemannZeta s :=
        (differentiableAt_riemannZeta hs)
      fun_prop (disch := assumption)
    apply DifferentiableAt.congr_of_eventuallyEq hdiff
    filter_upwards [eventually_ne_nhds hs] with u hu using by
      simp [H, Function.update_of_ne hu]

lemma ZetaZerosNearPoint_finite (t : ℝ) : Set.Finite (ZetaZerosNearPoint t) := by
  -- Center and radius of the disk
  let c : ℂ := (3/2 : ℂ) + t * Complex.I
  let R : ℝ := (5/6 : ℝ)
  have hRpos : 0 < R := by norm_num
  -- Define H(s) = (s - 1) * ζ(s) with the removable singularity at s = 1 filled in by setting H(1) = 1.
  -- This H is differentiable (entire). We'll use g(z) = H (z + c).
  let H : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1
  have hH_diff : Differentiable ℂ H := riemannZeta_correction_differentiable
  apply (MeromorphicOn.divisor H (Metric.closedBall c R)).finiteSupport (isCompact_closedBall ..)|>.subset
  intro z hz
  have := Complex.analyticOnNhd_univ_iff_differentiable.mpr hH_diff
  simp_all only [ZetaZerosNearPoint, Set.mem_setOf_eq, Function.mem_support, ne_eq]
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (this.mono (Set.subset_univ _)) (by simp_all [c, R, dist_eq_norm_sub])]
  simp_all only [WithTop.untop₀_eq_zero, ENat.map_natCast_eq_zero, ENat.map_eq_top_iff, not_or,
    analyticOrderAt_ne_zero, Set.mem_univ, this z, true_and]
  constructor
  · simp_all only [zeroZ, Set.mem_setOf_eq, H]
    by_cases! h : z = 1
    · simp [h, riemannZeta_one_ne_zero] at hz
    · simp_all
  · apply this.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (x := 1) (Set.mem_univ _) (Set.mem_univ _)
    have :=  (this 1 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr (by simp [H])
    simp [this]


lemma lem_sigmage1 (sigma t : ℝ) (hsigma : sigma > 1) : riemannZeta (sigma + t * Complex.I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  simp [Complex.add_re, Complex.mul_re, Complex.I_re]
  linarith

lemma lem_sigmale1 (sigma1 t1 : ℝ) : riemannZeta (sigma1 + t1 * Complex.I) = 0 → sigma1 ≤ 1 := by
  contrapose!
  exact fun h ↦ lem_sigmage1 _ _ h

lemma lem_sigmale1Zt (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) : rho1.re ≤ 1 := by
  apply lem_sigmale1 rho1.re rho1.im
  simp_all [ZetaZerosNearPoint, zeroZ]

lemma complex_abs_of_real (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma complex_abs_real_cast (r : ℝ) : ‖(r : ℂ)‖ = |r| := Complex.norm_real r

lemma zerosetKfRc_eq_ZetaZerosNearPoint (t : ℝ) :
  zerosetKfRc (5/6 : ℝ) ((3/2 : ℂ) + t * Complex.I) riemannZeta = ZetaZerosNearPoint t := by
  ext ρ; constructor <;>   simp +contextual [zerosetKfRc, ZetaZerosNearPoint, zeroZ, dist_eq_norm_sub]

lemma s_notin_ZetaZerosNearPoint (δ t : ℝ) (hδ_pos : 0 < δ) :
  ((1 : ℂ) + δ + t * Complex.I) ∉ ZetaZerosNearPoint t := by
  intro hmem
  have hz0 : riemannZeta ((1 : ℂ) + δ + t * Complex.I) = 0 := hmem.1
  have : ((1 : ℂ) + δ + t * Complex.I).re = 1 + δ := by simp
  have hpos : (1 : ℝ) < 1 + δ := by linarith
  have hnonzero := lem_sigmage1 (1 + δ) t hpos
  exact hnonzero (by simpa using hz0)

lemma s_in_closedBall_12 (δ t : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
  ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) ∈
    Metric.closedBall ((3 / 2 : ℂ) + (t : ℝ) * Complex.I) (1 / 2) := by
  -- Compute the difference to the center
  have hdiff :
      ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)
        = ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) := by
    simp
  have hreal :
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) = ((δ - (1 / 2 : ℝ)) : ℂ) := by
    have h' : ((1 + δ : ℝ) - (3 / 2 : ℝ)) = δ - (1 / 2 : ℝ) := by
      calc
        (1 + δ) - (3 / 2 : ℝ) = δ + 1 - (3 / 2 : ℝ) := by ac_rfl
        _ = δ + (1 - (3 / 2 : ℝ)) := by simp [add_sub_assoc]
        _ = δ + (- (1 / 2 : ℝ)) := by norm_num
        _ = δ - (1 / 2 : ℝ) := by simp [sub_eq_add_neg]
    calc
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)
          = ((1 + δ : ℝ) : ℂ) - (3 / 2 : ℂ) := by
              push_cast; ring
      _ = (↑((1 + δ : ℝ) - (3 / 2 : ℝ)) : ℂ) := by
              simp [Complex.ofReal_sub]
      _ = ((δ - (1 / 2 : ℝ)) : ℂ) := by simp [h']
  have hnormle :
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
        ≤ (1 / 2 : ℝ) := by
    calc
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
          = ‖((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)‖ := by simp [hdiff]
      _ = ‖((δ - (1 / 2 : ℝ)) : ℂ)‖ := by simp [hreal]
      _ = |δ - (1 / 2 : ℝ)| := by simpa using complex_abs_real_cast (δ - (1 / 2 : ℝ))
      _ ≤ 1 / 2 := by
        have hleft : - (1 / 2 : ℝ) ≤ δ - 1 / 2 := by linarith [hδ_pos]
        have hright : δ - 1 / 2 ≤ 1 / 2 := by linarith [hδ_lt]
        simpa using (abs_le.mpr ⟨hleft, hright⟩)
  -- Conclude membership in the closed ball
  simpa [Metric.mem_closedBall, Complex.dist_eq] using hnormle

lemma lem_explicit1deltat :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          ‖(∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite t),
                    (analyticOrderNatAt riemannZeta rho1 : ℂ) /
                      (((1 : ℂ) + δ + t * Complex.I) - rho1))
                - logDerivZeta ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I)‖
          ≤ C * Real.log (|t| + 2) := by
  -- Fixed radii and parameters
  let r1 : ℝ := (1/2 : ℝ)
  let r  : ℝ := (2/3 : ℝ)
  rcases Zeta1_Zeta_Expansion r1 r (by norm_num) (by norm_num) (by norm_num) with ⟨c, hc1, hc2⟩
  refine ⟨c * (1 / (r - r1) ^ 3 + 1), ?_, ?_⟩
  · apply one_lt_mul hc1.le
    simp
    norm_num
  peel hc2 with t ht hc2
  intro δ hδ
  have := zerosetKfRc_eq_ZetaZerosNearPoint t
  rw [mul_comm] at this
  simp +contextual only [this] at hc2
  specialize hc2 (ZetaZerosNearPoint_finite t) (1 + δ + t * Complex.I)
  have :   1 + δ + t * Complex.I ∈ Metric.closedBall (3 / 2 + Complex.I * ↑t) r1 \ ZetaZerosNearPoint t := by
    constructor
    · apply Set.mem_of_mem_of_subset ( s_in_closedBall_12 δ t hδ.1 hδ.2)
      rw [mul_comm]
    · exact s_notin_ZetaZerosNearPoint _ _ hδ.1
  specialize hc2 this
  rw [norm_sub_rev]
  grw [hc2]
  gcongr
  linarith

lemma lem_explicit1RealReal :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          |(logDerivZeta ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I)).re
            - (∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite t),
                  ((analyticOrderNatAt riemannZeta rho1 : ℂ) /
                    (((1 : ℂ) + δ + t * Complex.I) - rho1)).re)|
          ≤ C * Real.log (|t| + 2) := by
  rcases lem_explicit1deltat with ⟨C, hCpos, hE⟩
  refine ⟨C, hCpos, ?_⟩
  peel hE with t ht δ hδ hE
  rw [← Complex.re_sum, ← Complex.sub_re]
  grw [Complex.abs_re_le_norm]
  rwa [norm_sub_rev]

-- Updated lem_explicit2Real
lemma lem_explicit2Real :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          |(logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I)).re
            - (∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)),
                  ((analyticOrderNatAt riemannZeta rho1 : ℂ) /
                    (((1 : ℂ) + δ + (2 * t) * Complex.I) - rho1)).re)|
          ≤ C * Real.log (|2 * t| + 2) := by
  rcases lem_explicit1RealReal with ⟨C, hCpos, hEv⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
  -- Apply hEv to (2*t)
  have h_2t : 2 < |2 * t| := by
    rw [abs_mul, abs_two]
    linarith [ht]
  have h_bound := hEv (2 * t) h_2t δ hδ
  -- Simplify the cast operations
  simp only [Complex.ofReal_mul] at h_bound
  exact h_bound

lemma lem_Re1deltatge0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
(1 / ((1 : ℂ) + delta + t * Complex.I - rho1)).re ≥ 0 := by
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
    mul_one, sub_self, add_zero, ge_iff_le]
  apply div_nonneg _ <| Complex.normSq_nonneg _
  linarith [lem_sigmale1Zt t rho1 h_rho1_in_Zt]

lemma lem_Re1deltatge0m (delta : ℝ) (hdelta : delta > 0) (t : ℝ)
  (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint t) :
  ((analyticOrderNatAt riemannZeta rho1 : ℂ) /
    (((1 : ℂ) + delta + t * Complex.I) - rho1)).re ≥ 0 := by
  simp only [div_eq_mul_inv, Complex.mul_re, Complex.natCast_re, Complex.inv_re, Complex.sub_re,
    Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, mul_one, sub_self, add_zero, Complex.natCast_im, Complex.inv_im, Complex.sub_im,
    Complex.add_im, Complex.one_im, Complex.mul_im, zero_add, neg_sub, zero_mul, sub_zero,
    ge_iff_le]
  refine mul_nonneg (by positivity) <| mul_nonneg ?_ (inv_nonneg.mpr (Complex.normSq_nonneg _))
  linarith [lem_sigmale1Zt t rho1 h_rho1_in_Zt]

lemma lem_Re1delta2tge0 (delta : ℝ) (hdelta : delta > 0) (t : ℝ) (rho1 : ℂ) (h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint (2 * t)) :
((analyticOrderNatAt riemannZeta rho1 : ℂ) / ((1 : ℂ) + delta + (2 * t) * Complex.I - rho1)).re ≥ 0 := by
  -- Apply lem_Re1deltatge0 with (2 * t) in place of t
  convert lem_Re1deltatge0m delta hdelta (2 * t) rho1 h_rho1_in_Zt
  simp

lemma lem_sumrho2ge (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)), ((analyticOrderNatAt riemannZeta rho1 : ℂ) / ((1 : ℂ) + delta + (2 * t) * Complex.I - rho1)).re ≥ 0 := by
  apply Finset.sum_nonneg
  intro rho1 h_rho1_in_finset
  -- Convert membership in finite set to membership in original set
  have h_rho1_in_Zt : rho1 ∈ ZetaZerosNearPoint (2 * t) := by
    rwa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite (2 * t))] at h_rho1_in_finset
  -- Apply lem_Re1delta2tge0
  exact lem_Re1delta2tge0 delta hdelta t rho1 h_rho1_in_Zt

lemma lem_sumrho2ge02 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite (2 * t)),
        (analyticOrderNatAt riemannZeta rho1 : ℂ) / (((1 : ℂ) + delta + (2 * t) * Complex.I) - rho1)).re ≥ 0 := by
  rw [Complex.re_sum]
  -- Apply lem_sumrho2ge to show the sum of real parts is ≥ 0
  exact lem_sumrho2ge t delta hdelta

private lemma neg_le_sub_of_abs_sub_le {X S M : ℝ} (h : |X - S| ≤ M) : -X ≤ M - S := by
  have := (abs_le.mp h).1
  linarith

private lemma neg_le_of_abs_sub_le_of_nonneg {X S M : ℝ} (h : |X - S| ≤ M) (hS : 0 ≤ S) :
    -X ≤ M :=
  le_trans (neg_le_sub_of_abs_sub_le h) (sub_le_self M hS)

lemma lem_explicit2Real2 :
  ∃ C > 1,
      ∀ t : ℝ, 2 < |t| →
        ∀ δ : ℝ, 0 < δ ∧ δ < 1 →
          ((-logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I)).re)
          ≤ C * Real.log (|2 * t| + 2) := by
  rcases lem_explicit2Real with ⟨C, hCpos, hEv⟩
  refine ⟨C, hCpos, ?_⟩
  intro t ht δ hδ
  refine neg_le_of_abs_sub_le_of_nonneg (hEv t ht δ hδ) ?_
  convert lem_sumrho2ge02 t δ hδ.1|>.le
  simp

lemma lem_Z2bound :
  ∃ C > 1,
     ∀ t : ℝ, 2 < |t| →
      ∀ δ, 0 < δ ∧ δ < 1 →
        (-(logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I))).re
          ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C₁, hC₁_pos, hbound₁⟩ := lem_explicit2Real2
  refine ⟨2 * C₁, (by linarith), fun t ht δ hδ ↦ hbound₁ t ht δ hδ|>.trans ?_⟩
  suffices Real.log (|2 * t| + 2) ≤ 2 * Real.log (|t| + 2) by
    grw [this]
    exact le_of_eq (by ring)
  calc
    _ ≤ Real.log (4 * (|t| + 2)) := by
      gcongr; simp; linarith
    _ = Real.log 4 + Real.log (|t| + 2) := by
      exact Real.log_mul (by norm_num) (by linarith)
    _ ≤ Real.log (|t| + 2) + Real.log (|t| + 2) := by gcongr; linarith
    _ = 2 * Real.log (|t| + 2) := by ring

lemma lem_Z1split (delta : ℝ) (rho : ℂ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    ∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im),
        ((analyticOrderNatAt riemannZeta rho1 : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re =
    ((analyticOrderNatAt riemannZeta rho : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re +
    ∑ rho1 ∈ (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho,
        ((analyticOrderNatAt riemannZeta rho1 : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re := by
  have hmem : rho ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im) := by
    simp_all
  rw [← Finset.insert_erase hmem, Finset.sum_insert (Finset.notMem_erase rho _)]
  simp


lemma re_ofReal_div_ge_one (a : ℝ) (z : ℂ) (ha : 1 ≤ a) (hz : 0 ≤ (1 / z).re) : ((a : ℂ) / z).re ≥ (1 / z).re := by
  have hrepr : ((a : ℂ) / z).re = a * (1 / z).re := by
    simp [div_eq_mul_inv, Complex.mul_re]
  have hmul : (1 : ℝ) * (1 / z).re ≤ a * (1 / z).re :=
    mul_le_mul_of_nonneg_right ha hz
  calc
    ((a : ℂ) / z).re = a * (1 / z).re := hrepr
    _ ≥ 1 * (1 / z).re := by exact hmul
    _ = (1 / z).re := by simp [one_mul]

lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  exact analyticOn_riemannZeta s (by simpa)

lemma riemannZeta_not_eventually_zero_of_ne_one {s : ℂ} (hs : s ≠ 1) :
  ¬ (∀ᶠ z in nhds s, riemannZeta z = 0) := by
  intro hEvZero
  have := analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (IsConnected.isPreconnected (isConnected_compl_singleton_of_one_lt_rank (by simp) _)) (by simpa)
    hEvZero (x := 0) (by simp_all)
  simp_all [riemannZeta_zero]


lemma analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero {f : ℂ → ℂ} {z0 : ℂ}
  (hf : AnalyticAt ℂ f z0) (hzero : f z0 = 0)
  (hnot : ¬ (∀ᶠ z in nhds z0, f z = 0)) :
  1 ≤ analyticOrderNatAt f z0 := by
  -- The analytic order is nonzero since f z0 = 0
  have hne0 : analyticOrderAt f z0 ≠ 0 := by
    intro h0
    have hzne : f z0 ≠ 0 := (AnalyticAt.analyticOrderAt_eq_zero hf).1 h0
    exact hzne hzero
  -- The analytic order is not top since f is not eventually zero near z0
  have hneTop : analyticOrderAt f z0 ≠ ⊤ := by
    intro htop
    exact hnot ((analyticOrderAt_eq_top).1 htop)
  -- Hence it is a finite natural number n
  unfold analyticOrderNatAt
  rcases WithTop.ne_top_iff_exists.mp hneTop with ⟨n, hn⟩
  rw [← hn] at ⊢ hne0 hneTop
  suffices 1 ≤ n by simpa
  refine Nat.one_le_iff_ne_zero.mpr fun hn0 ↦ (hne0 ?_)
  simp [hn0]
  rfl

lemma lem_Z1splitge (delta : ℝ) (hdelta_pos : delta > 0) (rho : ℂ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    ∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im), ((analyticOrderNatAt riemannZeta rho1 : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re ≥
(1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re := by
  -- Split off the rho term
  rw [lem_Z1split delta rho h_rho_in_Zt]
  -- Show the first term ≥ (1/(...)).re
  have h_rho_ne_one : rho ≠ (1 : ℂ) := by
    intro h
    exact riemannZeta_one_ne_zero (by simpa [h] using! h_rho_in_Zt.1)
  have hAnal : AnalyticAt ℂ riemannZeta rho := analyticAt_riemannZeta_of_ne_one h_rho_ne_one
  have hNotEv : ¬ (∀ᶠ z in nhds rho, riemannZeta z = 0) :=
    riemannZeta_not_eventually_zero_of_ne_one h_rho_ne_one
  have horder_nat : 1 ≤ analyticOrderNatAt riemannZeta rho :=
    analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero
      hAnal (by simpa using! h_rho_in_Zt.1) hNotEv
  have ha_real : (1 : ℝ) ≤ (analyticOrderNatAt riemannZeta rho : ℝ) := by exact_mod_cast horder_nat
  have hz_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re :=
    lem_Re1deltatge0 delta hdelta_pos rho.im rho h_rho_in_Zt
  have hfirst :
      (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re
        ≤ ((((analyticOrderNatAt riemannZeta rho : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho))).re := by
    -- use re_ofReal_div_ge_one
    simpa [ge_iff_le] using
      (re_ofReal_div_ge_one (analyticOrderNatAt riemannZeta rho : ℝ)
        ((((1 : ℂ) + delta + rho.im * Complex.I) - rho)) ha_real hz_nonneg)
  -- Next, show the remaining sum is ≥ 0
  have hsum_nonneg :
      0 ≤ ∑ rho1 ∈ (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho,
          ((analyticOrderNatAt riemannZeta rho1 : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    have : (analyticOrderNatAt riemannZeta rho1 : ℂ) = ((analyticOrderNatAt riemannZeta rho1 : ℝ) : ℂ) := by norm_cast
    rw [← mul_one_div, this, Complex.re_ofReal_mul]
    rcases Finset.mem_erase.mp hmem with ⟨_, hmemS⟩
    -- membership in the original set
    have hZt : rho1 ∈ ZetaZerosNearPoint rho.im := by
      simpa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using hmemS
    exact mul_nonneg (by positivity) <| lem_Re1deltatge0 delta hdelta_pos rho.im rho1 hZt
  -- Combine the two bounds
  convert! add_le_add hfirst hsum_nonneg|>.ge using 1
  ring

lemma lem_1deltatrho0 (delta : ℝ) (rho : ℂ) :
((1 : ℂ) + delta + rho.im * Complex.I - rho) = ((1 : ℝ) + delta - rho.re) := by
  nth_rw 2 [← Complex.re_add_im rho]
  push_cast
  ring

lemma lem_1delsigReal2 (delta : ℝ) (rho : ℂ) :
(1 / ((1 : ℂ) + delta - rho.re)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
  rw [(by simp : (1 : ℂ) + delta - rho.re = (1 + delta - rho.re : ℝ)), Complex.div_ofReal_re]
  simp

lemma lem_re_inv_one_plus_delta_minus_rho_real (delta : ℝ) (rho : ℂ) :
(1 / ((1 : ℂ) + delta + rho.im * Complex.I - rho)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
  rw [lem_1deltatrho0 delta rho]
  exact lem_1delsigReal2 delta rho

lemma lem_Z1splitge2 (delta : ℝ) (hdelta : delta > 0) (rho : ℂ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    ∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im),
        ((analyticOrderNatAt riemannZeta rho1 : ℂ) / ((1 : ℂ) + delta + rho.im * Complex.I - rho1)).re ≥
1 / ((1 : ℝ) + delta - rho.re) := by
  grw [lem_Z1splitge delta hdelta rho h_rho_in_Zt, lem_re_inv_one_plus_delta_minus_rho_real delta rho]

lemma lem_Z1splitge3 (delta : ℝ) (hdelta : delta > 0) (sigma t : ℝ) (rho : ℂ)
  (h_rho_eq : rho = sigma + t * Complex.I)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint t) :
(∑ rho1 ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite t), (analyticOrderNatAt riemannZeta rho1 : ℂ) / (((1 : ℂ) + delta + t * Complex.I) - rho1)).re ≥ 1 / ((1 : ℝ) + delta - sigma) := by
  rw [Complex.re_sum]
  convert lem_Z1splitge2 delta hdelta rho _ using 1 <;> simp_all

lemma Z1bound :
  ∃ C > 1,
    ∀ (delta : ℝ), (0 < delta ∧ delta < 1) →
      ∀ t : ℝ, 2 < |t| →
        ∀ s : ℂ, s ∈ zeroZ ∧ s.im = t →
          (-(logDerivZeta ((1 : ℂ) + delta + t * Complex.I))).re
            ≤ - (1 / (1 + delta - s.re)) + C * Real.log (|t| + 2) := by
  obtain ⟨C0, hC0gt1, hExp⟩ := lem_explicit1RealReal
  -- Choose a global constant C ≥ C0 and large enough to absorb a fixed constant 3
  have hlog5pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  let C : ℝ := max (C0 + 3 / Real.log 4) 2
  refine ⟨C, (by grind), fun delta hdelta t ht s hs ↦ ?_⟩
  -- From explicit bound: |(logDerivZeta sp).re - Sre| ≤ C0 * log(|t|+2)
  specialize hExp t ht delta hdelta
  -- Basic bound with Sre dropped
  have h_basic : (-(logDerivZeta (1 + delta + t * Complex.I))).re ≤ C0 * Real.log (|t| + 2) := by
    refine neg_le_of_abs_sub_le_of_nonneg hExp ?_
    refine Finset.sum_nonneg fun rho1 hmem ↦ ?_
    have hZt : rho1 ∈ ZetaZerosNearPoint t := by
      simpa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite t)] using hmem
    -- Each term's real part is ≥ 0
    exact lem_Re1deltatge0m delta hdelta.1 t rho1 hZt
  -- Split on whether s ∈ ZetaZerosNearPoint t
  by_cases hmem : s ∈ ZetaZerosNearPoint t
  · -- Case 1: s ∈ Z_t; use the strong lower bound Sre ≥ 1/(1+δ-σ)
    have h_rho_eq : s = s.re + t * Complex.I := by
      simp [← hs.2]
    have h_sum_ge : ∑ rho1 ∈ (ZetaZerosNearPoint_finite t).toFinset, ((analyticOrderNatAt riemannZeta rho1 : ℂ) / (1 + delta + t * Complex.I - rho1)).re ≥ 1 / ((1 : ℝ) + delta - s.re) := by
      convert lem_Z1splitge3 delta hdelta.1 s.re t s h_rho_eq hmem
      simp
    grw [Complex.neg_re, neg_le_sub_of_abs_sub_le hExp, sub_le_sub_left h_sum_ge]
    conv => rhs; rw [add_comm, ← sub_eq_add_neg]
    gcongr
    · exact Real.log_nonneg (by linarith)
    exact le_trans (le_add_of_nonneg_right (div_nonneg (by norm_num) hlog5pos.le)) (le_max_left ..)
  · -- Case 2: s ∉ Z_t. Use geometry to bound 1/(1+δ - s.re) ≤ 3 and then absorb the constant.
    grw [h_basic]
    trans C * Real.log (|t| + 2) - 3
    · suffices C0 * Real.log (|t| + 2) + 3 ≤ C * Real.log (|t| + 2) by linarith
      have : C0 * Real.log (|t| + 2) + 3 ≤ C0 * Real.log (|t| + 2) + (C - C0) * Real.log (|t| + 2) := by
        gcongr
        calc
        _ = (3 / Real.log 4) * Real.log 4 := by field
        _ ≤ (3 / Real.log 4) * Real.log (|t| + 2) := by
          gcongr
          linarith
        _ ≤ (C - C0) * Real.log (|t| + 2) := by
          gcongr
          · exact Real.log_nonneg (by linarith)
          · grind
        _ = _ := by ring
      convert this using 1
      ring
    conv => rhs; rw [add_comm, ← sub_eq_add_neg]
    rw [← one_div_one_div 3]
    gcongr
    -- s is a zero with imaginary part t, so the distance condition must fail
    have h_notle : ¬ ‖s - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) := by
      intro hle
      exact hmem ⟨hs.1, hle⟩
    have hdist_gt : (5/6 : ℝ) < ‖s - ((3/2 : ℂ) + t * Complex.I)‖ := not_le.mp h_notle
    -- Compute the distance as a real absolute value: the difference has zero imaginary part
    have h_re : (s - ((3/2 : ℂ) + t * Complex.I)).re = s.re - (3/2 : ℝ) := by
      simp
    have h_im : (s - ((3/2 : ℂ) + t * Complex.I)).im = 0 := by
      simp [hs.2]
    have h_eq : s - ((3/2 : ℂ) + t * Complex.I) = (((s.re - (3/2 : ℝ)) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [h_re]
      · simp [h_im]
    have hdist_real : ‖s - ((3/2 : ℂ) + t * Complex.I)‖ = |s.re - (3/2 : ℝ)| := by
      simpa [h_eq] using complex_abs_of_real (s.re - (3/2 : ℝ))
    have habs_gt : (5/6 : ℝ) < |s.re - (3/2 : ℝ)| := by simpa [hdist_real] using hdist_gt
    -- Zeta zero implies s.re ≤ 1
    have h0 : riemannZeta (s.re + s.im * Complex.I) = 0 := by
      simpa [Complex.re_add_im] using! hs.1
    rw [abs_of_neg (by linarith [lem_sigmale1 s.re s.im h0])] at habs_gt
    linarith

lemma absorb_pos_constant_into_log {L A c : ℝ} (hL : 1 ≤ L) (hc : 0 ≤ c) : A * L + c ≤ (A + c) * L := by
  ring_nf
  gcongr
  exact le_mul_of_one_le_left hc hL

lemma zeta1zetaseriesxy (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * Complex.I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * n ^ (-(x + y * Complex.I)) := by
  unfold logDerivZeta
  convert ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa : 1 < (x + y * Complex.I).re)|>.symm using 1
  · ring
  · simp only [LSeries, LSeries.term_def]
    refine tsum_congr fun n ↦ ?_
    split_ifs with h
    · simp [h]
    · rw [div_eq_mul_inv, Complex.cpow_neg]

lemma ReZconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * Complex.I))).re) := by
  have h_re_gt_one : 1 < (x + y * Complex.I).re := by
    simpa
  have h_L_summable := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re_gt_one
  unfold LSeriesSummable LSeries.term at h_L_summable
  apply summable_complex_then_summable_real_part
  convert h_L_summable using 2
  split_ifs with h
  · simp [h]
  congr
  rw [Complex.cpow_neg]

lemma lem_nxy (n : ℕ) (hn : n ≥ 1) (x y : ℝ) :
    (n : ℂ) ^ (-(x + y * Complex.I)) = (n : ℂ) ^ ((-x) : ℂ) * (n : ℂ) ^ (-(y * Complex.I)) := by
  -- Rewrite -(x + y * Complex.I) as (-x) + (-(y * Complex.I))
  have h : -(x + y * Complex.I) = (-x : ℂ) + (-(y * Complex.I)) := by ring
  rw [h]
  exact Complex.cpow_add _ _ (by norm_cast; linarith)

lemma lem_zeta1zetaseriesxy2 (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * Complex.I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * ((n : ℂ) ^ ((-x) : ℂ)) * ((n : ℂ) ^ (-(y * Complex.I))) := by
  -- Apply zeta1zetaseriesxy
  rw [zeta1zetaseriesxy x y hx]
  -- Transform the sum by rewriting each term
  congr 1
  ext n
  -- For n ≥ 1, apply lem_nxy; for n = 0, both sides are 0
  by_cases h : n = 0
  · -- Case n = 0: both terms are 0
    simp [h]
  · -- Case n ≠ 0: can apply lem_nxy
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_nxy n hn x y]
    -- Rearrange multiplication: (a * b) * c = a * (b * c)
    ring

lemma Zseriesconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ ((-x) : ℂ) * (n : ℂ) ^ (-(y * Complex.I))) := by
  -- The series is exactly the von Mangoldt L-series at s = x + y * Complex.I
  -- Apply the von Mangoldt L-series summability result
  have h_re : 1 < (x + y * Complex.I).re := by
    simpa
  have h_summable := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re
  unfold LSeriesSummable LSeries.term at h_summable
  convert h_summable using 2
  split_ifs with h
  · simp [h]
  rw [mul_assoc, ← lem_nxy _ (by grind), Complex.cpow_neg]
  field

lemma lem_realnx (n : ℕ) (x : ℝ) :
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x) ≥ 0 := by
  exact mul_nonneg (by simp) (Real.rpow_nonneg (by grind) _)

lemma lem_sumRealZ (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * Complex.I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ ((-x) : ℂ) * (n : ℂ) ^ (-(y * Complex.I))).re := by
  -- Apply lem_zeta1zetaseriesxy2 and then take real part
  rw [lem_zeta1zetaseriesxy2 x y hx]
  exact Complex.re_tsum <| Zseriesconverges1 x y hx

lemma complex_cpow_neg_real (n : ℕ) (x : ℝ) (_hn : n ≥ 1) : (n : ℂ) ^ ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
  -- Since n ≥ 1, we have 0 ≤ (n : ℝ)
  have h_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  -- Apply Complex.ofReal_cpow in reverse direction
  rw [Complex.ofReal_cpow h_nonneg (-x)]
  -- Need to show that coercions are equal
  congr 1
  -- Show (n : ℂ) = ((n : ℝ) : ℂ)
  simp

lemma RealLambdaxy (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (_hx : 1 < x) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ ((-x) : ℂ) * (n : ℂ) ^ (-(y * Complex.I))).re =
((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * ((n : ℂ) ^ (-(y * Complex.I))).re := by
  -- Let b = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)
  let b := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)

  -- The key step: show that (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ ((-x) : ℂ) = (b : ℂ)
  have h1 : (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ ((-x) : ℂ) = (b : ℂ) := by
    -- Use the added lemma complex_cpow_neg_real
    have h_real_pow : (n : ℂ) ^ ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
      exact complex_cpow_neg_real n x hn

    rw [h_real_pow]
    rw [← Complex.ofReal_mul]

  -- Use associativity: a * b * c = (a * b) * c
  have h2 : (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ ((-x) : ℂ) * (n : ℂ) ^ (-(y * Complex.I)) =
           ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ ((-x) : ℂ)) * (n : ℂ) ^ (-(y * Complex.I)) := by
    rw [mul_assoc]

  rw [h2, h1]
  simp [b]


lemma ReZseriesRen (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * Complex.I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * ((n : ℂ) ^ (-(y * Complex.I))).re := by
  rw [lem_sumRealZ x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact RealLambdaxy n x y hn hx

lemma Rezeta1zetaseries (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * Complex.I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
  rw [ReZseriesRen x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [← lem_eacosalog3 n hn y]
    -- Need to show ((n : ℂ) ^ (-(y * Complex.I))).re = ((n : ℂ) ^ (-y * Complex.I)).re
    congr 1
    -- Show -(y * Complex.I) = -y * Complex.I
    simp

lemma complex_vonMangoldt_real_part_eq (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (hx : 1 < x) :
((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * Complex.I))).re =
(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
  -- Step 1: Use lem_nxy to split the complex power
  rw [lem_nxy n hn x y]

  -- Step 2: Rearrange to match RealLambdaxy format
  rw [← mul_assoc]

  -- Step 3: Use RealLambdaxy to connect the product form to real terms
  rw [RealLambdaxy n x y hn hx]

  -- Step 4: handle Complex.I sign for lem_eacosalog3
  have h_I : -(y * Complex.I) = -y * Complex.I := by
    simp

  -- Apply the conversion
  rw [h_I]

  -- Now apply lem_eacosalog3 to rewrite the imaginary power part
  rw [lem_eacosalog3 n hn y]

lemma Rezetaseries_convergence (x y : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) := by
  -- Apply ReZconverges1 to get summability of the complex series real part
  have h1 : Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * Complex.I))).re) :=
    ReZconverges1 x y hx

  -- Show pointwise equality between the complex series and our target series
  have h2 : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * Complex.I))).re =
                      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
    intro n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      exact complex_vonMangoldt_real_part_eq n x y hn hx

  -- Apply the pointwise equality to transfer summability
  have h3 : (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * Complex.I))).re) =
            (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) :=
    funext h2
  rwa [← h3]

lemma Rezetaseries2t (x t : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (2 * t * Real.log (n : ℝ))) := by
  -- Apply Rezetaseries_convergence with y = 2 * t
  exact Rezetaseries_convergence x (2 * t) hx

lemma lem_cost0 (n : ℕ) (_hn : n ≥ 1) (t : ℝ) (ht : t = 0) : Real.cos (t * Real.log (n : ℝ)) = 1 := by
  rw [ht]
  simp

lemma Rezetaseries0 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
  -- Apply Rezetaseries_convergence with y = 0
  have h1 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (0 * Real.log (n : ℝ))) :=
    Rezetaseries_convergence x 0 hx
  -- Use lem_cost0 to show cos(0 * log n) = 1
  convert h1 using 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_cost0 n hn 0 rfl]
    ring

lemma uniform_bound_Z0_complex : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 := by
  -- Define the function appearing in Z0bound
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))
  -- Start from the big-O statement near 0+
  have hO := Z0bound
  -- Unpack the big-O into an eventual bound with some constant c
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
  have h_event : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
    -- simplify ‖(1 : ℂ)‖ = 1
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℂ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    simpa [this] using hδ
  -- Turn the eventual statement into existence of a concrete set S in the filter
  rcases (Filter.eventually_iff_exists_mem).1 h_event with ⟨S, hS_in, hS_bound⟩
  -- Since S ∈ nhdsWithin 0 (0, ∞), it contains an interval (0, δ0]
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
  -- Choose C0 = max c 0 to ensure nonnegativity and preserve the bound
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
  -- δ belongs to (0, δ0] ⊆ S
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
  -- Hence we have the bound on the norm
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
  -- Strengthen to a nonnegative constant C0 = max c 0
  exact le_trans hnorm_le_c (le_max_left _ _)

/-- There exists a constant `C > 0` such that for all `δ > 0`,
`‖ -logDerivZeta (1 + δ) - 1/δ ‖ ≤ C`. -/
lemma Z0bound_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ‖ -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C := by
  -- Small-delta uniform bound from big-O near 0+
  rcases uniform_bound_Z0_complex with ⟨δ0, hδ0pos, C0, hC0nonneg, hsmall⟩
  have large : ∀ δ ≥ δ0, ‖logDerivZeta (1 + δ)‖ ≤ ‖logDerivZeta (1 + δ0)‖ := by
    intro δ hδ
    convert dlog_riemannZeta_bdd_on_vertical_lines_generalized (1 + δ0) (1 + δ) 0 (by linarith) (by linarith) using 1
      <;> simp [logDerivZeta]
  have: ∀ δ ≥ δ0, ‖-logDerivZeta (1 + δ) - 1 / δ‖ ≤ ‖logDerivZeta (1 + δ0)‖  + 1 / δ0 := by
    intro δ hδ
    grw [norm_sub_le]
    gcongr
    · rw [norm_neg]
      exact large _ hδ
    · simp only [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith)]
      gcongr
  exact ⟨max 2 (max C0 (‖logDerivZeta (1 + ↑δ0)‖ + 1 / δ0)), (by grind), (by grind)⟩

/-- There exists a constant `C > 0` such that for all `δ > 0`,
`Re(-logDerivZeta (1 + δ)) - 1/δ ≤ C`. -/
lemma Z0boundRe_const3 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    (-logDerivZeta ((1 : ℂ) + δ)).re - (1 / δ) ≤ C := by
  -- Use Z0bound_const to get a bound on the norm, then unwind the real part of (1/δ : ℂ)
  rcases Z0bound_const with ⟨C, hCpos, hC⟩
  use C, hCpos
  peel hC with δ hδ hC
  grw [← hC, ← Complex.re_le_norm]
  simp

lemma Z341bounds_const :
  ∃ C > 1, ∀ (δ : ℝ) (_ : δ > 0) (_ : δ < 1), ∀ t : ℝ, 2 < |t| → ∀ σ : ℝ,
    (σ + t * Complex.I) ∈ zeroZ →
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re
    + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re
    +     (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
    ≤ 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by
  -- Apply the three lemmas mentioned in informal proof: Z0boundRe_const3, Z1bound, Z2bound
  rcases Z0boundRe_const3 with ⟨C0, hC0pos, hZ0⟩
  rcases Z1bound with ⟨C1, hC1pos, hZ1⟩
  rcases lem_Z2bound with ⟨C2, hC2pos, hZ2⟩

  -- Choose final constant
  let C := 3 * C0 + 4 * C1 + C2
  refine ⟨C, (by linarith), ?_⟩
  · intro δ hδpos hδ1 t ht σ hσ
    -- Apply the bounds from the referenced lemmas directly
    specialize hZ0 δ hδpos
    have hZ0_bound : (-logDerivZeta ((1 : ℂ) + δ)).re ≤ C0 + (1 / δ) := by linarith
    specialize hZ1 δ ⟨hδpos, hδ1⟩ t ht (σ + t * Complex.I) ⟨hσ, (by simp)⟩
    have hZ1_bound : (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re ≤ -(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2) := by
      convert hZ1
      simp
    grw [hZ0_bound, hZ1_bound, hZ2 t ht δ ⟨hδpos, hδ1⟩]
    calc
      _ = 3 / δ - 4 / (1 + δ - σ) + ((4 * C1 + C2) * Real.log (|t| + 2) + 3 * C0) := by ring
      _ ≤ 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2 + 3 * C0) * Real.log (|t| + 2) := by
        gcongr
        refine absorb_pos_constant_into_log ?_ (by linarith)
        exact Real.le_log_iff_exp_le (by linarith)|>.mpr (by linarith [Real.exp_one_lt_three])
      _ = 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by ring


lemma Rezeta1zetaseries1 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + t * Complex.I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) := by
  -- Apply Rezeta1zetaseries with x = 1 + delta and y = t
  have h1 : 1 < 1 + delta := by linarith [hdelta]
  convert Rezeta1zetaseries (1 + delta) t h1
  -- Show that the complex expressions are equal
  simp [Complex.ofReal_add]

lemma Rezeta1zetaseries2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * Complex.I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)) := by
  -- Apply Rezeta1zetaseries with x = 1 + delta and y = 2 * t
  have h1 : 1 < 1 + delta := by linarith [hdelta]
  -- Rewrite the left side to match the pattern exactly, ensuring real arithmetic
  have h2 : (1 : ℂ) + delta + (2 * t) * Complex.I = (1 + delta : ℝ) + ((2 * t) : ℝ) * Complex.I := by
    simp [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  rw [h2]
  exact Rezeta1zetaseries (1 + delta) (2 * t) h1

lemma Rezeta1zetaseries0 (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
  -- Start with Rezeta1zetaseries1 with t = 0
  have h_series : (-logDerivZeta ((1 : ℂ) + delta + 0 * Complex.I)).re =
                  ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) :=
    Rezeta1zetaseries1 0 delta hdelta

  -- Simplify the LHS: (1 : ℂ) + delta + 0 * Complex.I = (1 : ℂ) + delta
  have h_lhs : (-logDerivZeta ((1 : ℂ) + delta + 0 * Complex.I)).re = (-logDerivZeta ((1 : ℂ) + delta)).re := by
    congr 2
    simp

  -- Simplify the RHS using lem_cost0: cos(0 * log n) = 1
  have h_rhs : ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) =
               ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
    congr 1
    funext n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      rw [lem_cost0 n hn 0 rfl, mul_one]

  -- Combine the results
  rw [← h_lhs, h_series, h_rhs]

lemma Z341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * Complex.I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * Complex.I)).re)
    =
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
     4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) +
     ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Rezeta1zetaseries0 delta hdelta, Rezeta1zetaseries1 t delta hdelta, Rezeta1zetaseries2 t delta hdelta]


lemma lem341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)))
    + (4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)))
    + (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)))
    = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  -- First establish that 1 < 1 + delta
  have h1 : 1 < 1 + delta := by linarith [hdelta]

  -- Apply the convergence results from the context
  have h2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) :=
    Rezetaseries0 (1 + delta) h1

  have h3 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    Rezetaseries_convergence (1 + delta) t h1

  have h4 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) :=
    Rezetaseries2t (1 + delta) t h1

  -- Use scalar multiplication properties of tsum (in reverse direction)
  rw [← Summable.tsum_mul_left 3 h2]
  rw [← Summable.tsum_mul_left 4 h3]

  -- Use additivity of tsum
  rw [← Summable.tsum_add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)]
  rw [← Summable.tsum_add]
  -- Factor out common terms
  · congr 1
    ext n
    ring
  -- Apply the final summability result
  · exact Summable.add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)
  · exact h4

lemma lem_341series2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * Complex.I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * Complex.I)).re)
    =
    ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Z341series t delta hdelta]
  exact lem341series t delta hdelta

lemma lem_Lambda_pos_trig_sum (n : ℕ) (delta : ℝ) (t : ℝ) (hn : n ≥ 1) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply mul_nonneg
  · -- Show ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + delta)) ≥ 0
    apply lem_realnx n (1 + delta)
  · -- Show 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) ≥ 0
    exact lem_postriglogn n hn t

lemma lem_seriespos (t : ℝ) (delta : ℝ) :
    0 ≤ ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply tsum_nonneg
  intro n
  by_cases h : n = 0
  · -- Case n = 0: von Mangoldt function is 0, so the term is 0
    simp [h]
  · -- Case n ≠ 0: apply lem_Lambda_pos_trig_sum
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact lem_Lambda_pos_trig_sum n delta t hn

lemma Z341pos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ 3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
        4 * (-logDerivZeta ((1 : ℂ) + delta + t * Complex.I)).re +
        (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * Complex.I)).re := by
  rw [lem_341series2 t delta hdelta]
  exact lem_seriespos t delta


lemma pos_delta_from_C_L {C L : ℝ} (hC : 0 < C) (hL : 0 < L) : 0 < 1 / (2 * C * L) := by
  positivity

lemma log_abs_two_pos (t : ℝ) : 0 < Real.log (|t| + 2) := by
  exact Real.log_pos (by grind)

lemma two_C_log_pos {C t : ℝ} (hC : 0 < C) : 0 < 2 * C * Real.log (|t| + 2) := by
  have hL : 0 < Real.log (|t| + 2) := log_abs_two_pos t
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hCL : 0 < C * Real.log (|t| + 2) := mul_pos hC hL
  have : 0 < 2 * (C * Real.log (|t| + 2)) := mul_pos h2 hCL
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma rhs_eval_of_inv (C L δ : ℝ) (h : 1 / δ = 2 * C * L) : 3 / δ + C * L = 7 * C * L := by
  rw [← mul_one_div, h]
  ring

lemma lem341tsC :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    4 / (1 - s.re + 1 / (2 * C * Real.log (|s.im| + 2))) ≤ 7 * C * Real.log (|s.im| + 2) := by
  -- Get the constant C from Z341bounds_const
  obtain ⟨C, hCpos, hbound⟩ := Z341bounds_const
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTim

  -- Define L = log(|s.im| + 2) and δ = 1/(2CL)
  let L : ℝ := Real.log (|s.im| + 2)
  have hLpos : 0 < L := log_abs_two_pos (s.im)
  let δ : ℝ := 1 / (2 * C * L)

  -- Show δ > 0
  have hCpos_weak : 0 < C := lt_trans zero_lt_one hCpos
  have hδpos : 0 < δ := pos_delta_from_C_L hCpos_weak hLpos

  -- Show δ < 1: need 1 < 2*C*L
  have hδlt : δ < 1 := by
    -- Since |s.im| > 3, we have L > log(5) > 1
    have hL_gt_1 : 1 < L := by
      have h5_lt : 4 < |s.im| + 2 := by linarith [hTim]
      have hL_gt_log5 : Real.log 4 < L := Real.log_lt_log (by norm_num) h5_lt
      have hlog5_gt_1 : 1 < Real.log 4 := by
        have h5_gt_e : Real.exp 1 < 4 := by linarith[Real.exp_one_lt_d9]
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) h5_gt_e
      linarith [hlog5_gt_1, hL_gt_log5]
    -- Now 2*C*L > 2*1*1 = 2 > 1 since C > 1 and L > 1
    have h2CL_gt_1 : 1 < 2 * C * L := by
      -- Since C > 1 and L > 1, we have C*L > 1*1 = 1, so 2*C*L > 2*1 = 2 > 1
      have hCL_gt_1 : 1 < C * L := by
        calc C * L
          > 1 * L := by exact mul_lt_mul_of_pos_right hCpos hLpos
          _ = L := by simp
          _ > 1 := hL_gt_1
      have h2_pos : (0 : ℝ) < 2 := by norm_num
      calc 2 * C * L
        = 2 * (C * L) := by ring
        _ > 2 * 1 := by exact mul_lt_mul_of_pos_left hCL_gt_1 h2_pos
        _ = 2 := by simp
        _ > 1 := by norm_num
    -- Therefore δ = 1/(2*C*L) < 1
    simp only [δ]
    rw [div_lt_one_iff]
    left
    exact ⟨two_C_log_pos hCpos_weak, h2CL_gt_1⟩

  -- Apply Z341bounds_const
  have hmem : (s.re + s.im * Complex.I) ∈ zeroZ := by
    simpa [Complex.re_add_im] using hs.1
  have hupper := hbound δ hδpos hδlt (s.im) hTim (s.re) hmem

  -- Apply Z341pos for non-negativity
  have hpos := Z341pos (s.im) δ hδpos

  -- Combine: 0 ≤ LHS ≤ RHS, so rearranging gives the desired inequality
  have hRHS_nonneg : 0 ≤ 3 / δ - 4 / (1 + δ - s.re) + C * L := le_trans hpos hupper
  have hineq1 : 4 / (1 + δ - s.re) ≤ 3 / δ + C * L := by linarith [hRHS_nonneg]

  -- Rewrite denominator: 1 + δ - s.re = 1 - s.re + δ
  have hineq2 : 4 / (1 - s.re + δ) ≤ 3 / δ + C * L := by
    convert hineq1 using 2
    ring

  -- Substitute δ = 1/(2CL) and use rhs_eval_of_inv
  have hinv : 1 / δ = 2 * C * L := by
    simp only [δ, one_div, inv_inv]

  have hrhs_eval : 3 / δ + C * L = 7 * C * L := rhs_eval_of_inv C L δ hinv

  have hfinal : 4 / (1 - s.re + δ) ≤ 7 * C * L := by
    rw [← hrhs_eval]
    exact hineq2

  -- The goal is exactly what we have with L and δ substituted
  convert hfinal

lemma lem341tsC2 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
          1 - s.re + 1 / (2 * C * Real.log (|s.im| + 2)) ≥ 4 / (7 * C * Real.log (|s.im| + 2)) := by
  -- Obtain the constant and bound from lem341tsC
  rcases lem341tsC with ⟨C, hCpos, hT⟩
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTs
  -- Define a and b to flip the inequality 4/a ≤ b into 4/b ≤ a
  set a := 1 - s.re + 1 / (2 * C * Real.log (|s.im| + 2)) with ha
  set b := 7 * C * Real.log (|s.im| + 2) with hb
  have hineq : 4 / a ≤ b := by
    simpa [ha, hb] using hT s hs hTs
  -- Show b &gt; 0
  have h_abs_nonneg : 0 ≤ |s.im| := abs_nonneg _
  have h_two_le : (2 : ℝ) ≤ |s.im| + 2 := by
    linarith
  have h_one_lt : (1 : ℝ) < |s.im| + 2 := lt_of_lt_of_le one_lt_two h_two_le
  have hx0 : 0 ≤ |s.im| + 2 := by linarith [h_abs_nonneg]
  have hlogpos : 0 < Real.log (|s.im| + 2) := (Real.log_pos_iff hx0).2 h_one_lt
  have h7pos : 0 < (7 : ℝ) := by exact_mod_cast (by decide : (0 : ℕ) < 7)
  have hbpos : 0 < b := by
    have h7Cpos : 0 < 7 * C := by linarith
    exact mul_pos h7Cpos hlogpos
  -- Show a &gt; 0
  rcases hs with ⟨_, hRepos, hRelt⟩
  have h1 : 0 < 1 - s.re := sub_pos.mpr hRelt
  have h2pos : 0 < (2 : ℝ) := lt_trans zero_lt_one one_lt_two
  have h2Cpos : 0 < (2 : ℝ) * C := by linarith
  have hdenpos : 0 < 2 * C * Real.log (|s.im| + 2) := mul_pos h2Cpos hlogpos
  have hinvpos : 0 < 1 / (2 * C * Real.log (|s.im| + 2)) := one_div_pos.mpr hdenpos
  have hapos : 0 < a := by
    have := add_pos h1 hinvpos
    simpa [ha] using this
  -- Flip 4/a ≤ b to 4/b ≤ a via cross-multiplication
  have hres : 4 / b ≤ a := by
    rw [div_le_iff₀ hapos] at hineq
    rw [div_le_iff₀ hbpos, mul_comm]
    exact hineq
  simpa [ha, hb] using hres

lemma simplify_4_7_2 (C L : ℝ) : 4 / (7 * C * L) - 1 / (2 * C * L) = 1 / (14 * C * L) := by
  -- Regroup the products in the denominators
  have h1 : (4 : ℝ) / (7 * (C * L)) = (4 : ℝ) / (7 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (4 : ℝ)) (b := (7 : ℝ)) (c := C * L))
  have h2 : (1 : ℝ) / (2 * (C * L)) = (1 : ℝ) / (2 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (1 : ℝ)) (b := (2 : ℝ)) (c := C * L))
  -- Compute the scalar difference (4/7 - 1/2) = 1/14
  have h3' : ((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹ = (14 : ℝ)⁻¹ := by
    have h3 : ((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (14 : ℝ) := by
      norm_num
    simpa [one_div] using h3
  calc
    4 / (7 * C * L) - 1 / (2 * C * L)
        = (4 : ℝ) / (7 * (C * L)) - (1 : ℝ) / (2 * (C * L)) := by
          simp [mul_assoc]
    _ = (4 : ℝ) / (7 : ℝ) / (C * L) - (1 : ℝ) / (2 : ℝ) / (C * L) := by
          simp [h1, h2]
    _ = (((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ))) / (C * L) := by
          simpa using (sub_div (a := ((4 : ℝ) / (7 : ℝ))) (b := ((1 : ℝ) / (2 : ℝ))) (c := C * L)).symm
    _ = (((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹) / (C * L) := by
          simp [one_div]
    _ = (14 : ℝ)⁻¹ / (C * L) := by
          simp [h3']
    _ = 1 / (14 * (C * L)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using
            (div_mul_eq_div_div (a := (1 : ℝ)) (b := (14 : ℝ)) (c := C * L)).symm
    _ = 1 / (14 * C * L) := by simp [mul_assoc]

lemma fraction_diff_lower_bound (C L a : ℝ) : 4 / (7 * C * L) ≤ a + 1 / (2 * C * L) → 1 / (14 * C * L) ≤ a := by
  intro h
  have h' : 4 / (7 * C * L) - 1 / (2 * C * L) ≤ a := (sub_le_iff_le_add).mpr h
  have hdiff : 1 / (14 * C * L) = 4 / (7 * C * L) - 1 / (2 * C * L) := by
    symm
    exact simplify_4_7_2 C L
  calc
    1 / (14 * C * L)
        = 4 / (7 * C * L) - 1 / (2 * C * L) := hdiff
    _ ≤ a := h'

lemma lem341tsC3 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    1 - s.re ≥ 1 / (14 * C * Real.log (|s.im| + 2)) := by
  obtain ⟨C, hCpos, hT⟩ := lem341tsC2
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTle
  have h := hT s hs hTle
  -- Convert the inequality to the form required by fraction_diff_lower_bound
  have h' : 4 / (7 * C * Real.log (|s.im| + 2)) ≤
      (1 - s.re) + 1 / (2 * C * Real.log (|s.im| + 2)) := by
    simpa [ge_iff_le, add_comm, add_left_comm, add_assoc] using h
  -- Apply the algebraic rearrangement lemma
  have h'' := fraction_diff_lower_bound C (Real.log (|s.im| + 2)) (1 - s.re) h'
  -- Conclude
  simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using h''



lemma zerofree :
    ∃ c, c > 0 ∧ c < 1 ∧ ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| → s.re ≤ 1 - c / (Real.log (|s.im| + 2)) := by
  -- Obtain the inequality from lem341tsC3
  rcases lem341tsC3 with ⟨C0, hC0pos, hT⟩
  -- Define the final constant C := 1 / (14 * C0)
  set C : ℝ := 1 / (14 * C0) with hCdef
  -- Show C > 0
  have h14pos : 0 < (14 : ℝ) := by norm_num
  have hC0pos' : 0 < C0 := lt_trans zero_lt_one hC0pos
  have hCpos : 0 < C := by
    have hdenpos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    exact one_div_pos.mpr hdenpos
  -- Show C < 1: Since C0 > 1, we have 14 * C0 > 14 > 1, so C = 1/(14*C0) < 1
  have hClt1 : C < 1 := by
    have h14C0_pos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    have h14C0_gt_1 : 1 < 14 * C0 := by
      have h14_gt_1 : (1 : ℝ) < 14 := by norm_num
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ < 14 * 1 := by exact mul_lt_mul_of_pos_right h14_gt_1 zero_lt_one
        _ < 14 * C0 := by exact mul_lt_mul_of_pos_left hC0pos h14pos
    rw [hCdef]
    rw [div_lt_one_iff]
    left
    exact ⟨h14C0_pos, h14C0_gt_1⟩
  -- Provide constants and prove the desired bound
  refine ⟨C, hCpos, hClt1, ?_⟩
  intro s hs hTle
  -- Let L denote the logarithm term
  set L := Real.log (|s.im| + 2) with hLdef
  -- From lem341tsC3 we have: 1 / (14 * C0 * L) ≤ 1 - s.re
  have hb0 := hT s hs hTle
  -- Rewrite the bound to match C / L on the left
  have hb' : C / L ≤ 1 - s.re := by
    simpa [hLdef, hCdef, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb0
  -- Rearranging gives the desired inequality
  have : s.re ≤ 1 - C / L := by linarith
  simpa [hLdef] using this

-- The constant a from the zerofree lemma
noncomputable def zerofree_constant : ℝ := Classical.choose zerofree

lemma zerofree_constant_pos : 0 < zerofree_constant :=
  (Classical.choose_spec zerofree).1

lemma zerofree_constant_lt_one : zerofree_constant < 1 :=
  (Classical.choose_spec zerofree).2.1

noncomputable def deltaz (z : ℂ) : ℝ := (zerofree_constant / 20) / Real.log (|z.im| + 2)

noncomputable def deltaz_t (t : ℝ) : ℝ := deltaz (t * Complex.I)

-- For z∈ℂ we have 0<δ(z)<1/9. For t∈ℝ we have 0<δ_t<1/9.
lemma lem_delta19 :
  (∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9)) ∧
  (∀ t : ℝ, |t| > 2 → (0 < deltaz_t t ∧ deltaz_t t < 1/9)) := by
  -- First, prove the result for complex z
  have h_complex : ∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9) := by
    intro z hz
    constructor
    · -- Show 0 < deltaz z
      have h_num_pos : 0 < zerofree_constant / 20 := by
        exact div_pos zerofree_constant_pos (by norm_num)
      have h_den_pos : 0 < Real.log (|z.im| + 2) := by
        have h_gt_one : (1 : ℝ) < |z.im| + 2 := by
          have h_nonneg : (0 : ℝ) ≤ |z.im| := abs_nonneg _
          linarith [hz]
        exact Real.log_pos h_gt_one
      unfold deltaz
      exact div_pos h_num_pos h_den_pos
    · -- Show deltaz z < 1/9
      -- First establish the key bounds
      have h_den_ge_half : (1/2 : ℝ) ≤ Real.log (|z.im| + 2) := by
        -- log(|z.im| + 2) ≥ log(2) ≥ 1/2
        have h_den_ge_log2 : Real.log 2 ≤ Real.log (|z.im| + 2) := by
          have h_pos : 0 < |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          have h_le : (2 : ℝ) ≤ |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          exact Real.log_le_log (by norm_num) h_le
        -- Show log 2 ≥ 1/2 using exp(1/2) ≤ 2
        have h_log2_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
          have h_exp_half_le_two : Real.exp (1/2) ≤ 2 := by
            -- exp(1/2)^2 = exp(1) < 3 < 4 = 2^2, so exp(1/2) < 2
            have h_exp_one_lt_three : Real.exp 1 < 3 := by linarith[Real.exp_one_lt_d9]
            have h_exp_sq : (Real.exp (1/2))^2 = Real.exp 1 := by
              rw [pow_two, ← Real.exp_add]; norm_num
            have h_exp_sq_lt_four : (Real.exp (1/2))^2 < 4 := by
              rw [h_exp_sq]; linarith [h_exp_one_lt_three]
            -- Use sq_lt_sq to get exp(1/2) < 2
            have h_exp_pos : 0 ≤ Real.exp (1/2) := le_of_lt (Real.exp_pos _)
            have h_two_pos : 0 ≤ (2 : ℝ) := by norm_num
            have h_four_eq : (2 : ℝ)^2 = 4 := by norm_num
            rw [← h_four_eq] at h_exp_sq_lt_four
            have h_lt_abs := (sq_lt_sq).mp h_exp_sq_lt_four
            rw [abs_of_nonneg h_exp_pos, abs_of_nonneg h_two_pos] at h_lt_abs
            exact le_of_lt h_lt_abs
          exact (Real.le_log_iff_exp_le (by norm_num : 0 < (2 : ℝ))).mpr h_exp_half_le_two
        exact le_trans h_log2_ge_half h_den_ge_log2
      -- Now get the bound on the reciprocal
      have h_inv_le_two : 1 / Real.log (|z.im| + 2) ≤ 2 := by
        have h_pos_half : 0 < (1/2 : ℝ) := by norm_num
        have h_ineq := one_div_le_one_div_of_le h_pos_half h_den_ge_half
        convert! h_ineq using 1
        norm_num
      -- Now bound deltaz z
      have h_bound : deltaz z ≤ zerofree_constant / 10 := by
        unfold deltaz
        -- deltaz z = (zerofree_constant / 20) / Real.log (|z.im| + 2)
        --          = (zerofree_constant / 20) * (1 / Real.log (|z.im| + 2))
        rw [div_eq_mul_inv]
        -- Now multiply the inequality 1 / Real.log (|z.im| + 2) ≤ 2 by zerofree_constant / 20
        have h_num_nonneg : 0 ≤ zerofree_constant / 20 := by
          exact le_of_lt (div_pos zerofree_constant_pos (by norm_num))
        have h_mul_ineq := mul_le_mul_of_nonneg_left h_inv_le_two h_num_nonneg
        convert! h_mul_ineq using 1
        -- Show zerofree_constant / 20 * 2 = zerofree_constant / 10
        · field
        ring
      -- Final bound: zerofree_constant / 10 < 1/10 < 1/9
      have h_lt_tenth : zerofree_constant / 10 < 1 / 10 := by
        exact div_lt_div_of_pos_right zerofree_constant_lt_one (by norm_num)
      have h_tenth_lt_ninth : (1 : ℝ) / 10 < 1 / 9 := by norm_num
      exact lt_trans (lt_of_le_of_lt h_bound h_lt_tenth) h_tenth_lt_ninth

  -- Now construct the main result
  constructor
  · exact h_complex
  · -- For real t
    intro t ht
    -- Use deltaz_t t = deltaz (t * Complex.I) and |(t * Complex.I).im| = |t|
    have h_eq : deltaz_t t = deltaz (t * Complex.I) := rfl
    rw [h_eq]
    have h_im_eq : |(t * Complex.I).im| = |t| := by simp
    rw [← h_im_eq] at ht
    exact h_complex (t * Complex.I) ht

lemma closedBall_compact_complex (c : ℂ) (r : ℝ) :
    IsCompact (Metric.closedBall c r) := by
  -- Complex numbers form a proper space where all closed balls are compact
  exact ProperSpace.isCompact_closedBall c r

lemma riemannZeta_no_zeros_accumulate_at_one :
  ∀ Z : Set ℂ, (∀ z ∈ Z, riemannZeta z = 0) → ¬AccPt 1 (Filter.principal Z) := by
  intro Z hZ
  -- Prove by contradiction
  by_contra h_acc

  -- The key fact from the informal proof: riemannZeta has a simple pole at 1 with residue 1
  -- This means (s - 1) * riemannZeta s → 1 as s → 1 (s ≠ 1)
  have h_residue := riemannZeta_residue_one

  -- From the residue formula, for ε = 1/2, there exists δ > 0 such that
  -- for all s with s ≠ 1 and dist(s, 1) < δ, we have dist((s - 1) * riemannZeta s, 1) < 1/2
  rw [Metric.tendsto_nhdsWithin_nhds] at h_residue
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_residue (1/2) (by norm_num : (0 : ℝ) < 1/2)

  -- AccPt 1 (principal Z) means 1 is an accumulation point of Z
  -- By accPt_iff_nhds, for every neighborhood U of 1, there exists y ∈ U ∩ Z with y ≠ 1
  rw [accPt_iff_nhds] at h_acc

  -- Apply this to the ball of radius δ around 1
  obtain ⟨y, ⟨hy_ball, hy_Z⟩, hy_ne⟩ := h_acc (Metric.ball 1 δ) (Metric.ball_mem_nhds 1 hδ_pos)

  -- y is a zero of riemannZeta
  have hy_zero : riemannZeta y = 0 := hZ y hy_Z

  -- y is in the complement of {1}, i.e., y ≠ 1
  have hy_in_compl : y ∈ ({1} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hy_ne

  have hy_dist : dist y 1 < δ := hy_ball

  -- Apply the residue bound
  have h_bound := hδ_bound hy_in_compl hy_dist

  -- We have dist((y - 1) * riemannZeta y, 1) < 1/2
  -- But riemannZeta y = 0, so (y - 1) * riemannZeta y = 0
  -- Thus dist(0, 1) < 1/2
  rw [hy_zero, mul_zero] at h_bound

  -- Now dist(0, 1) in ℂ equals |0 - 1| = |-1| = |1| = 1
  have h_dist_eq : dist (0 : ℂ) (1 : ℂ) = 1 := by
    rw [Complex.dist_eq]
    norm_num

  rw [h_dist_eq] at h_bound
  -- This gives 1 < 1/2, which is a contradiction
  norm_num at h_bound

set_option backward.isDefEq.respectTransparency false in
lemma complex_minus_singleton_connected : IsPreconnected ({s : ℂ | s ≠ 1} : Set ℂ) := by
  -- The set {s : ℂ | s ≠ 1} is the complement of the singleton {1}
  have h_eq : {s : ℂ | s ≠ 1} = ({1} : Set ℂ)ᶜ := by
    ext x
    simp [Set.mem_compl_iff, Set.mem_singleton_iff]

  -- Rewrite using this equality
  rw [h_eq]

  -- ℂ is a 2-dimensional real vector space, so rank ℝ ℂ = 2 > 1
  have h_rank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    -- Now need to show 1 < 2 in Cardinal
    norm_num

  -- Apply the theorem that complement of singleton is connected in dimension > 1
  have h_connected := isConnected_compl_singleton_of_one_lt_rank h_rank (1 : ℂ)

  -- IsConnected implies IsPreconnected
  exact h_connected.isPreconnected

lemma eventually_eq_zero_implies_frequently_eq_zero_punctured (f : ℂ → ℂ) (z₀ : ℂ) :
  (∀ᶠ z in nhds z₀, f z = 0) → (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0) := by
  intro h_eventually
  -- Following the informal proof:
  -- If f is eventually zero in a neighborhood of z₀, there exists an open set U
  -- containing z₀ where f is zero. Since U is open and contains z₀, it must contain
  -- infinitely many points different from z₀. All these points satisfy f(z) = 0
  -- and are in the punctured neighborhood, so f is frequently zero there.

  -- The punctured neighborhood is NeBot (non-trivial) for complex numbers
  -- Using the standard notation 𝓝[≠] for punctured neighborhoods
  have h_nebot : Filter.NeBot (nhdsWithin z₀ {z₀}ᶜ) := by
    -- Complex numbers form a normed field, so punctured neighborhoods are NeBot
    exact NormedField.nhdsNE_neBot z₀

  -- Since nhdsWithin z₀ {z₀}ᶜ ≤ nhds z₀, if f is eventually zero in nhds z₀,
  -- it's also eventually zero in nhdsWithin z₀ {z₀}ᶜ
  have h_eventually_punctured : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0 := by
    -- Use the fact that nhdsWithin is smaller than nhds
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds h_eventually

  -- In a NeBot filter, if something is eventually true, it's frequently true
  exact h_eventually_punctured.frequently

lemma riemannZeta_zeros_finite_of_compact (K : Set ℂ) (hK : IsCompact K) :
    {z ∈ K | riemannZeta z = 0}.Finite := by
  -- The proof follows from the fact that zeros of meromorphic functions are isolated
  -- and isolated points in a compact set must be finite

  -- Suppose for contradiction that the set of zeros is infinite
  by_contra! h_not_finite
  -- Let Z be the set of zeros in K
  let Z := {z ∈ K | riemannZeta z = 0}

  -- Since Z is infinite and contained in the compact set K,
  -- by the Bolzano-Weierstrass theorem, Z has an accumulation point in K
  have hZ_inf : Z.Infinite := h_not_finite
  have hZ_sub : Z ⊆ K := fun z hz => hz.1

  -- Apply Bolzano-Weierstrass to get an accumulation point
  obtain ⟨z₀, hz₀_K, hz₀_acc⟩ := hZ_inf.exists_accPt_of_subset_isCompact hK hZ_sub

  -- Case 1: If z₀ = 1
  by_cases h_eq_one : z₀ = 1
  · -- z₀ = 1, use riemannZeta_no_zeros_accumulate_at_one directly
    subst h_eq_one
    -- The set Z consists of zeros of riemannZeta
    have hZ_zeros : ∀ z ∈ Z, riemannZeta z = 0 := fun z hz => hz.2
    -- This contradicts riemannZeta_no_zeros_accumulate_at_one
    exact riemannZeta_no_zeros_accumulate_at_one Z hZ_zeros hz₀_acc

  · -- z₀ ≠ 1, use analyticity argument
    -- The Riemann zeta function is analytic at z₀ (since z₀ ≠ 1)
    have h_analytic : AnalyticAt ℂ riemannZeta z₀ :=
      zetaanalOnnot1 z₀ h_eq_one

    -- Apply the principle of isolated zeros
    obtain h_ev_zero | h_ev_ne := h_analytic.eventually_eq_zero_or_eventually_ne_zero

    · -- Case: riemannZeta is eventually zero in a neighborhood of z₀
      -- This would make it identically zero on the connected set {s : ℂ | s ≠ 1}

      -- Convert eventually to frequently in punctured neighborhood
      have h_freq := eventually_eq_zero_implies_frequently_eq_zero_punctured riemannZeta z₀ h_ev_zero

      -- Apply the identity theorem on the preconnected set {s : ℂ | s ≠ 1}
      have h_eq_on_zero := zetaanalOnnot1.eqOn_zero_of_preconnected_of_frequently_eq_zero
        complex_minus_singleton_connected h_eq_one h_freq

      -- This says riemannZeta is zero on {s : ℂ | s ≠ 1}
      -- But riemannZeta(0) = -1/2 ≠ 0
      have : riemannZeta 0 = 0 := h_eq_on_zero (by simp : (0 : ℂ) ∈ {s | s ≠ 1})
      rw [riemannZeta_zero] at this
      norm_num at this

    · -- Case: riemannZeta is eventually non-zero in punctured neighborhoods
      -- But z₀ is an accumulation point of Z, so there are zeros arbitrarily close
      -- This contradicts the isolation property

      -- AccPt means the punctured neighborhood filter intersected with principal Z is NeBot
      unfold AccPt at hz₀_acc

      -- From eventually ne zero, we get eventually not in Z in punctured neighborhoods
      have h_ev_not_Z : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, z ∉ Z := by
        apply Filter.Eventually.mono h_ev_ne
        intro z hz hz_in_Z
        exact hz hz_in_Z.2

      -- This means in the intersection filter, we eventually have False
      have h_ev_false : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z, False := by
        rw [Filter.eventually_inf_principal]
        exact h_ev_not_Z

      -- By eventually_false_iff_eq_bot, this filter equals ⊥
      have h_eq_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z = ⊥ :=
        Filter.eventually_false_iff_eq_bot.mp h_ev_false

      -- But hz₀_acc says this filter is NeBot
      -- NeBot means the filter is not equal to ⊥
      have h_ne_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z ≠ ⊥ := hz₀_acc.ne

      -- This is a contradiction
      exact h_ne_bot h_eq_bot

-- For z∈ℂ, if Re(z) > 1 - 9δ(z) then ζ(z)≠0
lemma lem_ZFRdelta :
  ∀ z : ℂ, 2 < |z.im| → z.re > 1 - 9 * deltaz z → riemannZeta z ≠ 0 := by
  intro z him hre
  by_cases h1 : 1 ≤ z.re
  · -- In the half-plane Re z ≥ 1, ζ ≠ 0
    simpa using riemannZeta_ne_zero_of_one_le_re h1
  -- Now assume Re z < 1
  have hzlt1 : z.re < 1 := lt_of_not_ge h1
  -- From |Im z| > 2, get 0 < δ(z) and δ(z) < 1/9
  have hgt : |z.im| > 2 := by simpa using him
  have hδ := (lem_delta19).1 z hgt
  rcases hδ with ⟨hδ_pos, hδ_lt_19⟩
  -- Then 9 * δ(z) < 1, so 0 < 1 - 9 * δ(z) < z.re, hence 0 < z.re
  have h9δ_lt1 : 9 * deltaz z < 1 := by
    have h := mul_lt_mul_of_pos_left hδ_lt_19 (by norm_num : 0 < (9 : ℝ))
    have h9 : (9 : ℝ) * (1 / 9) = 1 := by norm_num
    simpa [h9] using h
  have hzre_pos : 0 < z.re := by
    have : 0 < 1 - 9 * deltaz z := sub_pos.mpr h9δ_lt1
    exact lt_trans this hre
  -- Suppose for contradiction that ζ z = 0
  by_contra hzero
  have hzmem : z ∈ zeroZ := by simpa [zeroZ] using hzero
  -- Apply the zero-free region inequality with the chosen constant
  have hprop := (Classical.choose_spec zerofree).2.2
  have hbound : z.re ≤ 1 - zerofree_constant / Real.log (|z.im| + 2) :=
    hprop z ⟨hzmem, hzre_pos, hzlt1⟩ him
  -- Let L = log(|Im z| + 2) and note L > 0
  set L : ℝ := Real.log (|z.im| + 2) with hLdef
  have hLpos : 0 < L := by
    have hone_lt : (1 : ℝ) < |z.im| + 2 := by
      have : (0 : ℝ) ≤ |z.im| := abs_nonneg _
      linarith
    have := Real.log_pos hone_lt
    simpa [hLdef] using this
  -- Compare 1 - c/L and 1 - 9 * δ(z)
  have hb_le_a' : ((9 : ℝ) / 20) * (zerofree_constant / L) ≤ zerofree_constant / L := by
    have hcoef_le1 : ((9 : ℝ) / 20) ≤ 1 := by norm_num
    have ha_nonneg : 0 ≤ zerofree_constant / L := le_of_lt (div_pos zerofree_constant_pos hLpos)
    have := mul_le_mul_of_nonneg_right hcoef_le1 ha_nonneg
    simpa [one_mul] using this
  have h9d_eq : 9 * deltaz z = ((9 : ℝ) / 20) * (zerofree_constant / L) := by
    simp [deltaz, hLdef, div_eq_mul_inv, mul_left_comm, mul_assoc]
  have hdelta_le : 9 * deltaz z ≤ zerofree_constant / L := by
    simpa [h9d_eq] using hb_le_a'
  have h_le_rhs : 1 - zerofree_constant / L ≤ 1 - 9 * deltaz z := by
    have hneg := neg_le_neg hdelta_le
    simpa [sub_eq_add_neg] using add_le_add_right hneg 1
  -- Combine to contradict hre
  have hle : z.re ≤ 1 - 9 * deltaz z := le_trans hbound h_le_rhs
  have hcontr : z.re < z.re := lt_of_le_of_lt hle hre
  exact (lt_irrefl (z.re)) hcontr

-- lem_ZFRinD: For t∈ℝ with |t|>3, c=3/2+it and z=σ+it with 1-δ_t ≤ σ ≤ 3/2, we have z∈ D̄_{2/3}(c)

lemma complex_sub_ofReal_I_real_eq_ofReal (z : ℂ) (a t : ℝ) (him : z.im = t) :
  z - ((a : ℂ) + Complex.I * t) = ((z.re - a) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [him]

lemma lem_ZFRinD (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∈ Metric.closedBall c (2/3) := by
  intro c h
  rcases h with ⟨h_low, hrest⟩
  rcases hrest with ⟨h_high, him⟩
  have hsub : z - c = ((z.re - (3/2)) : ℂ) := by
    simpa [c] using! complex_sub_ofReal_I_real_eq_ofReal z (3/2) t him
  have h1 : dist z c = ‖((z.re - (3/2)) : ℂ)‖ := by
    simp [dist_eq_norm, hsub]
  have h2 : ‖((z.re - (3/2)) : ℂ)‖ = ‖z.re - (3/2)‖ := by
    simpa using (Complex.norm_real (z.re - (3/2)))
  have hdist_abs : dist z c = |z.re - (3/2)| := by
    have h4 : dist z c = ‖z.re - (3/2)‖ := h1.trans h2
    simpa [Real.norm_eq_abs] using h4
  have hnonpos : z.re - (3/2) ≤ 0 := sub_nonpos_of_le h_high
  have habs : |z.re - (3/2)| = 3/2 - z.re := by
    have := abs_of_nonpos hnonpos
    simpa [neg_sub] using this
  have hdist_eq : dist z c = 3/2 - z.re := hdist_abs.trans habs
  have h_le : dist z c ≤ 1/2 + deltaz_t t := by
    calc
      dist z c = 3/2 - z.re := hdist_eq
      _ ≤ 3/2 - (1 - deltaz_t t) := by linarith
      _ = 1/2 + deltaz_t t := by ring
  have hδlt : deltaz_t t < 1/9 := (lem_delta19.2 t ht).2
  have h12δ_lt : (1/2 : ℝ) + deltaz_t t < (1/2 : ℝ) + 1/9 := by
    have := add_lt_add_right hδlt (1/2 : ℝ)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have h123_lt : (1/2 : ℝ) + 1/9 < (2/3 : ℝ) := by norm_num
  have h_lt : (1/2 : ℝ) + deltaz_t t < (2/3 : ℝ) := lt_trans h12δ_lt h123_lt
  have hdist_le : dist z c ≤ 2/3 := le_trans h_le (le_of_lt h_lt)
  exact (Metric.mem_closedBall).2 hdist_le

-- lem_ZFRnotK: For t∈ℝ with |t|>3, c=3/2+it and z=σ+it with 1-δ_t ≤ σ ≤ 3/2, we have z∉ K_ζ(5/6;c)
lemma lem_ZFRnotK (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∉ zerosetKfRc (5/6) c riemannZeta := by
  intro c h

  -- Extract the conjunction components
  obtain ⟨h_ge, h_le, h_im⟩ := h

  -- Key relationship: when z.im = t, we have deltaz z = deltaz_t t
  have h_delta_eq : deltaz z = deltaz_t t := by
    rw [deltaz_t, deltaz]
    -- Need to show the denominators are equal
    congr 1
    congr 1
    -- Show |z.im| = |(t * Complex.I).im|
    rw [h_im]
    -- Now show |t| = |(t * Complex.I).im|
    -- Since (t * Complex.I).im = t, this is |t| = |t|
    simp only [Complex.mul_I_im, Complex.ofReal_re]

  -- Convert the deltaz_t bound to a deltaz bound
  have h_ge_delta : 1 - deltaz z ≤ Complex.re z := by
    rwa [← h_delta_eq] at h_ge

  -- Get positivity of deltaz z from lem_delta19
  have h_im_gt : |z.im| > 2 := by
    rw [h_im]
    exact ht

  have h_delta_pos : 0 < deltaz z := by
    exact (lem_delta19.1 z h_im_gt).1

  -- Since deltaz z > 0, we have deltaz z < 9 * deltaz z
  have h_delta_lt_9delta : deltaz z < 9 * deltaz z := by
    linarith [h_delta_pos]

  -- Therefore Complex.re z > 1 - 9 * deltaz z
  have h_strict : Complex.re z > 1 - 9 * deltaz z := by
    linarith [h_ge_delta, h_delta_lt_9delta]

  -- Apply the zero-free region lemma
  have h_zeta_ne_zero : riemannZeta z ≠ 0 :=
    lem_ZFRdelta z h_im_gt h_strict

  -- Now prove z ∉ zerosetKfRc (5/6) c riemannZeta by contradiction
  intro h_mem
  -- By definition, z ∈ zerosetKfRc should imply riemannZeta z = 0
  have h_zero : riemannZeta z = 0 := h_mem.2
  -- This contradicts h_zeta_ne_zero
  exact h_zeta_ne_zero h_zero

-- lem_Zeta_Expansion_ZFR: Zeta expansion in the zero-free region
lemma lem_Zeta_Expansion_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + Complex.I * t;
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
        ‖(deriv riemannZeta z / riemannZeta z) -
          (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ))‖
        ≤ C_1 * Real.log |t| := by
  obtain ⟨C, hC_gt_one, hC_expansion⟩ :=
    Zeta1_Zeta_Expansion (2/3) (3/4)
    (by norm_num : (0 : ℝ) < 2/3)
    (by norm_num : (2/3 : ℝ) < 3/4)
    (by norm_num : (3/4 : ℝ) < 5/6)
  let C_1 := C * (1 / ((3/4 : ℝ) - 2/3)^3 + 1)
  have hC_1_gt_1 : C_1 > 1 := by
    have h_coeff : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 + 1 > 1 := by
      have h_pos : ((3/4 : ℝ) - 2/3)^3 > 0 := by norm_num
      have h_div_pos : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 > 0 := div_pos one_pos h_pos
      linarith
    have h_ge_1 : (1 : ℝ) ≤ C := le_of_lt hC_gt_one
    exact one_lt_mul_of_le_of_lt h_ge_1 h_coeff
  refine ⟨C_1, hC_1_gt_1, ?_⟩
  intro t ht c hfin z hz
  have ht2 : |t| > 2 := by linarith
  have hz_in_ball : z ∈ Metric.closedBall c (2/3) := by
    simpa [c] using (lem_ZFRinD t ht2 z hz)
  have hz_not_in_K : z ∉ zerosetKfRc (5/6) c riemannZeta := by
    simpa [c] using (lem_ZFRnotK t ht2 z hz)
  have hz_in_diff : z ∈ Metric.closedBall c (2/3) \ zerosetKfRc (5/6) c riemannZeta :=
    ⟨hz_in_ball, hz_not_in_K⟩
  have h_expansion := hC_expansion t ht2 hfin z hz_in_diff
  rw [show logDerivZeta z = deriv riemannZeta z / riemannZeta z from rfl] at h_expansion
  exact h_expansion

-- lem_abszrhoReRe: For z,ρ∈ℂ we have |z-ρ| ≥ Re(z) - Re(ρ)
lemma lem_abszrhoReRe (z ρ : ℂ) : ‖z - ρ‖ ≥ z.re - ρ.re := by
  have h1 : (z - ρ).re ≤ ‖z - ρ‖ := Complex.re_le_norm (z - ρ)
  have h2 : (z - ρ).re = z.re - ρ.re := Complex.sub_re z ρ
  rw [← h2]
  exact h1

-- lem_Rerhotodeltarho: For ρ∈ K_ζ(5/6;c) we have Re(ρ) ≤ 1 - 9δ(ρ)
lemma lem_Rerhotodeltarho {ρ : ℂ} :
  ∀ t : ℝ, |t| > 3 → ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) (3/2+ t* Complex.I) riemannZeta) → ρ.re ≤ 1 - 9 * deltaz ρ := by
  intro t ht h_mem
  -- From ρ ∈ zerosetKfRc, we get riemannZeta ρ = 0
  have h_zero : riemannZeta ρ = 0 := h_mem.2

  -- ρ is in a closed ball of radius 5/6 around 3/2 + t*Complex.I
  have h_ball : ρ ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6) := h_mem.1

  -- This means dist(ρ, 3/2 + t*Complex.I) ≤ 5/6
  have h_dist : dist ρ (3/2 + t * Complex.I) ≤ 5/6 := by
    rwa [Metric.mem_closedBall] at h_ball

  -- We need |ρ.im| > 2 to apply lem_ZFRdelta
  have h_im : 2 < |ρ.im| := by
    -- The imaginary part of ρ is close to t, so |ρ.im - t| ≤ 5/6
    have h_im_bound : |ρ.im - t| ≤ 5/6 := by
      -- |ρ.im - t| ≤ ||ρ - (3/2 + t*Complex.I)||
      have h_le_norm : |ρ.im - t| ≤ ‖ρ - (3/2 + t * Complex.I)‖ := by
        have : |(ρ - (3/2 + t * Complex.I)).im| ≤ ‖ρ - (3/2 + t * Complex.I)‖ :=
          Complex.abs_im_le_norm _
        have h_im_eq : (ρ - (3/2 + t * Complex.I)).im = ρ.im - t := by
          simp
        rwa [← h_im_eq]
      rw [← Complex.dist_eq] at h_le_norm
      linarith [h_le_norm, h_dist]

    -- Apply triangle inequality: |t| - |ρ.im| ≤ |t - ρ.im| = |ρ.im - t|
    have triangle := abs_sub_abs_le_abs_sub t ρ.im
    -- This gives |t| - |ρ.im| ≤ |t - ρ.im|
    -- Rewrite |t - ρ.im| = |ρ.im - t|
    have eq_comm : |t - ρ.im| = |ρ.im - t| := abs_sub_comm t ρ.im
    rw [eq_comm] at triangle
    -- Now triangle : |t| - |ρ.im| ≤ |ρ.im - t|
    -- Rearrange to get |ρ.im| ≥ |t| - |ρ.im - t|
    have h_ge : |ρ.im| ≥ |t| - |ρ.im - t| := by linarith [triangle]

    -- Since |t| > 3 and |ρ.im - t| ≤ 5/6, we get |ρ.im| ≥ 3 - 5/6 = 13/6 > 2
    have : |ρ.im| ≥ |t| - 5/6 := by linarith [h_ge, h_im_bound]
    have : |ρ.im| > 3 - 5/6 := by linarith [ht]
    have h_calc : (3 : ℝ) - 5/6 = 13/6 := by norm_num
    have h_gt2 : (13 : ℝ)/6 > 2 := by norm_num
    rw [h_calc] at *
    linarith [h_gt2]

  -- Apply contrapositive of lem_ZFRdelta
  -- lem_ZFRdelta: 2 < |z.im| → z.re > 1 - 9 * deltaz z → riemannZeta z ≠ 0
  -- contrapositive: riemannZeta z = 0 → ¬(z.re > 1 - 9 * deltaz z)
  have h_not_gt : ¬(ρ.re > 1 - 9 * deltaz ρ) := by
    intro h_gt
    have h_ne_zero := lem_ZFRdelta ρ h_im h_gt
    exact h_ne_zero h_zero

  exact le_of_not_gt h_not_gt

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have |Im(z)| ≤ |t|+2δ_t
lemma lem_DImt2d :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| ≤ |t| + 5/6 := by
  intro t ht z hz
  -- z is in the closed ball, so ‖z - (3/2 + t * Complex.I)‖ ≤ 5/6
  rw [Metric.mem_closedBall] at hz
  -- The center has imaginary part t
  have center_im : (3/2 + t * Complex.I).im = t := by simp
  -- So (z - center).im = z.im - t
  have diff_im : (z - (3/2 + t * Complex.I)).im = z.im - t := by
    rw [Complex.sub_im, center_im]
  -- We know |z.im - t| ≤ ‖z - center‖
  have h1 : |z.im - t| ≤ ‖z - (3/2 + t * Complex.I)‖ := by
    rw [← diff_im]
    exact Complex.abs_im_le_norm _
  -- Combining with the ball constraint
  rw [dist_eq_norm_sub] at hz
  have h2 : |z.im - t| ≤ 5/6 := le_trans h1 hz
  -- Use triangle inequality: since z.im = (z.im - t) + t, we have |z.im| ≤ |z.im - t| + |t|
  have h3 : |z.im| ≤ |z.im - t| + |t| := by
    conv_lhs => rw [show z.im = (z.im - t) + t by ring]
    exact abs_add_le (z.im - t) t
  linarith

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have |Im(z)|+2 ≤ (|t|+2)²
lemma lem_DIMt2 :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| + 2 ≤ (|t| + 2)^3 := by
  intro t ht z hz
  -- From the previous lemma, |z.im| ≤ |t| + 5/6
  have h1' := lem_DImt2d t ht z hz
  -- Add 2 to both sides and simplify
  have h1a : |z.im| + 2 ≤ |t| + 17/6 := by
    simpa [show |t| + 5/6 + 2 = |t| + 17/6 by ring] using add_le_add_left h1' 2
  -- Bound |t| + 17/6 by |t| + 3
  have h17le3 : |t| + 17/6 ≤ |t| + 3 := by
    have : (17 : ℝ) / 6 ≤ 3 := by norm_num
    gcongr
  -- Show |t| + 3 ≤ (|t| + 2)^3 by expanding and using nonnegativity
  have h_nonneg_poly : 0 ≤ |t|^3 + 6 * |t|^2 + 11 * |t| + 5 := by
    have h0 : 0 ≤ |t|^3 := by exact pow_nonneg (abs_nonneg _) 3
    have h1 : 0 ≤ 6 * |t|^2 := by
      have : 0 ≤ (6 : ℝ) := by norm_num
      exact mul_nonneg this (sq_nonneg _)
    have h2 : 0 ≤ 11 * |t| := by
      have : 0 ≤ (11 : ℝ) := by norm_num
      exact mul_nonneg this (abs_nonneg _)
    have h3 : 0 ≤ (5 : ℝ) := by norm_num
    exact add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3
  have h_add : |t| + 3 ≤ (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    simpa using (le_add_of_nonneg_right (a := |t| + 3) h_nonneg_poly)
  have h_expand : (|t| + 2)^3 = (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    ring
  have h3 : |t| + 3 ≤ (|t| + 2)^3 := by
    simpa [h_expand] using h_add
  -- Chain the inequalities
  exact le_trans (le_trans h1a h17le3) h3

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have log(|Im(z)|+2) ≤ 2log(|t|+2)
lemma lem_DlogImlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    Real.log (|z.im| + 2) ≤ 3 * Real.log (|t| + 2) := by
  intro t ht z hz
  -- From lem_DIMt2 we have the key inequality on the arguments of the logs
  have h1 : |z.im| + 2 ≤ (|t| + 2)^3 := lem_DIMt2 t ht z hz
  -- Positivity of the left argument of log
  have h2 : 0 < |z.im| + 2 := by
    have : 0 ≤ |z.im| := abs_nonneg _
    linarith
  -- Monotonicity of log
  have hlog := Real.log_le_log h2 h1
  -- Rewrite the RHS using log_pow
  simpa [Real.log_pow] using hlog

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have 1/log(|t|+2) ≤ 2/log(|Im(z)|+2)
lemma lem_D1logtlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    (1 : ℝ) / Real.log (|t| + 2) ≤ 3 / Real.log (|z.im| + 2) := by
  intro t ht z hz
  have h1 := lem_DlogImlog t ht z hz
  -- We need log(|t| + 2) > 0 and log(|z.im| + 2) > 0
  have ht_pos : |t| + 2 > 1 := by linarith [abs_nonneg t]
  have hz_pos : |z.im| + 2 > 1 := by linarith [abs_nonneg z.im]
  have log_t_pos : Real.log (|t| + 2) > 0 := Real.log_pos ht_pos
  have log_z_pos : Real.log (|z.im| + 2) > 0 := Real.log_pos hz_pos
  -- From h1: log(|z.im| + 2) ≤ 2 * log(|t| + 2)
  -- We want: 1/log(|t| + 2) ≤ 2/log(|z.im| + 2)
  -- Cross multiply: 1 * log(|z.im| + 2) ≤ 2 * log(|t| + 2)
  rw [div_le_div_iff₀ log_t_pos log_z_pos]
  simp only [one_mul]
  exact h1

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have δ_t ≤ 2δ(z)
lemma lem_Ddt2dz :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    deltaz_t t ≤ 3 * deltaz z := by
  intro t ht z hz
  have h := lem_D1logtlog t ht z hz
  have hpos : 0 ≤ zerofree_constant / 20 := by
    have ha : 0 < zerofree_constant := zerofree_constant_pos
    have h9 : 0 < (20 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt ha) (le_of_lt h9)
  have h2 := mul_le_mul_of_nonneg_left h hpos
  calc
    deltaz_t t
        = (zerofree_constant / 20) / Real.log (|t| + 2) := by
            simp [deltaz_t, deltaz]
    _ = (zerofree_constant / 20) * (1 / Real.log (|t| + 2)) := by simp [div_eq_mul_inv]
    _ ≤ (zerofree_constant / 20) * (3 / Real.log (|z.im| + 2)) := h2
    _ = 3 * ((zerofree_constant / 20) * (1 / Real.log (|z.im| + 2))) := by
            field
    _ = 3 * deltaz z := by simp [deltaz, div_eq_mul_inv, mul_left_comm, mul_assoc]

lemma lem_deltarhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → deltaz ρ ≥ (1/3) * deltaz_t t := by
  intro c hρK
  rcases hρK with ⟨hball, _hzero⟩
  have hball' : ρ ∈ Metric.closedBall ((3/2 : ℂ) + t * Complex.I) (5/6) := by
    simpa [c, mul_comm] using! hball
  have hmain : deltaz_t t ≤ 3 * deltaz ρ := lem_Ddt2dz t ht ρ hball'
  have hthird_nonneg : 0 ≤ (1/3 : ℝ) := by norm_num
  have h_mul : (1/3 : ℝ) * deltaz_t t ≤ (1/3 : ℝ) * (3 * deltaz ρ) :=
    mul_le_mul_of_nonneg_left hmain hthird_nonneg
  have h_simplify : (1/3 : ℝ) * (3 * deltaz ρ) = deltaz ρ := by
    ring
  have : (1/3 : ℝ) * deltaz_t t ≤ deltaz ρ := by
    simpa [h_simplify] using h_mul
  simpa [mul_comm] using this

-- lem_Rerhotodeltat: For ρ∈ K_ζ(5/6;c) we have Re(ρ) ≤ 1 - 3δ_t
lemma lem_Rerhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → ρ.re ≤ 1 - 3 * deltaz_t t := by
  intros c h_rho_in
  -- Apply lem_Rerhotodeltarho to get Re(ρ) ≤ 1 - 9 * δ(ρ)
  have h1 : ρ.re ≤ 1 - 9 * deltaz ρ :=
    lem_Rerhotodeltarho (ρ := ρ) t ht (by simpa [c, mul_comm] using! h_rho_in)
  -- Apply lem_deltarhotodeltat to get δ(ρ) ≥ (1/3) * δ_t
  have h2 : deltaz ρ ≥ (1/3) * deltaz_t t := lem_deltarhotodeltat t ht ρ h_rho_in
  -- From h2, we get 9 * δ(ρ) ≥ 9 * (1/3) * δ_t = 3 * δ_t
  have h3 : 9 * deltaz ρ ≥ 3 * deltaz_t t := by
    calc
      9 * deltaz ρ
          ≥ 9 * ((1/3) * deltaz_t t) := by
                exact mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 9)
      _ = 9 * (1/3) * deltaz_t t := by ring
      _ = 3 * deltaz_t t := by norm_num
  -- Therefore 1 - 9 * δ(ρ) ≤ 1 - 3 * δ_t
  have h4 : 1 - 9 * deltaz ρ ≤ 1 - 3 * deltaz_t t := by
    linarith [h3]
  -- By transitivity: Re(ρ) ≤ 1 - 9 * δ(ρ) ≤ 1 - 3 * δ_t
  exact le_trans h1 h4

-- lem_RezRerho: Re(z) - Re(ρ) ≥ 2δ_t
lemma lem_RezRerho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    z.re - ρ.re ≥ 2 * deltaz_t t := by
  intro c h_rho_mem h_z
  -- Use lem_Rerhotodeltat to get upper bound on ρ.re
  have h_rho_bound := lem_Rerhotodeltat t ht ρ h_rho_mem
  -- Extract lower bound on z.re from hypothesis
  have h_z_lower := h_z.1
  -- Calculate: z.re - ρ.re ≥ (1 - deltaz_t t) - (1 - 3 * deltaz_t t) = 2 * deltaz_t t
  linarith [h_z_lower, h_rho_bound]

-- lem_abszrhodelta: |z-ρ| ≥ 2δ_t
lemma lem_abszrhodelta (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖z - ρ‖ ≥ 2 * deltaz_t t := by
  intro c h_rho_in_K h_z_conditions
  -- Use lem_RezRerho to get z.re - ρ.re ≥ 2 * deltaz_t t
  have h1 : z.re - ρ.re ≥ 2 * deltaz_t t := (lem_RezRerho t ht z ρ) h_rho_in_K h_z_conditions
  -- Use lem_abszrhoReRe to get ‖z - ρ‖ ≥ z.re - ρ.re
  have h2 : ‖z - ρ‖ ≥ z.re - ρ.re := lem_abszrhoReRe z ρ
  -- Combine by transitivity: 2 * deltaz_t t ≤ z.re - ρ.re ≤ ‖z - ρ‖
  exact le_trans h1 h2

-- lem_1abszrho: 1/|z-ρ| ≤ 1/(2δ_t)
lemma lem_1abszrho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) := by
  intro c hρ hz
  -- Apply one_div_le_one_div_of_le with the needed conditions
  apply one_div_le_one_div_of_le
  -- First need to prove 0 < 2 * deltaz_t t
  · have h_delta_pos : 0 < deltaz_t t := by
      have h_delta19 := lem_delta19
      exact (h_delta19.2 t (by linarith [ht] : |t| > 2)).1
    linarith [h_delta_pos]
  -- Second need to prove 2 * deltaz_t t ≤ ‖z - ρ‖
  · exact lem_abszrhodelta t ht z ρ hρ hz

lemma lem_finiteKzeta (t : ℝ) :
    let c := (3/2 : ℂ) + Complex.I * t
    (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite := by
  intro c
  have hK : IsCompact (Metric.closedBall c (5 / (6 : ℝ))) :=
    closedBall_compact_complex c (5 / (6 : ℝ))
  simpa [zerosetKfRc] using
    (riemannZeta_zeros_finite_of_compact (Metric.closedBall c (5 / (6 : ℝ))) hK)

lemma lem_triangle_ZFR (t : ℝ) (z : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖(∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ))‖ ≤
    (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖z - ρ‖) := by
  -- Introduce variables correctly: c (center), hfin (finiteness proof), hz_cond (conditions on z)
  intros c hfin hz_cond

  -- Apply triangle inequality: ||∑ f_i|| ≤ ∑ ||f_i||
  apply le_trans (norm_sum_le _ _)

  -- Show each term satisfies the bound: ||m_ρ / (z-ρ)|| ≤ m_ρ / ||z-ρ||
  apply Finset.sum_le_sum
  intro ρ hρ

  -- Apply norm_div
  rw [norm_div]

  -- The norm of a natural number cast to ℂ equals the real cast
  rw [Complex.norm_natCast]

-- lem_Zeta_Triangle_ZFR: Triangle inequality bound for zeta'/zeta
lemma lem_Zeta_Triangle_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + Complex.I * t
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
        ‖deriv riemannZeta z / riemannZeta z‖ ≤
        ‖(∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ))‖ +
        C_1 * Real.log |t| := by
  obtain ⟨C1, hC1, hbound⟩ := lem_Zeta_Expansion_ZFR
  refine ⟨C1, hC1, ?_⟩
  intro t ht c hfin z hz
  -- Let S denote the finite sum over zeros
  let S := (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (z - ρ))
  have hbound1 := hbound t ht hfin z hz
  have htri : ‖deriv riemannZeta z / riemannZeta z‖ ≤ ‖(deriv riemannZeta z / riemannZeta z) - S‖ + ‖S‖ := by
    have hn := norm_add_le ((deriv riemannZeta z / riemannZeta z) - S) S
    have hrewrite : (deriv riemannZeta z / riemannZeta z) - S + S = (deriv riemannZeta z / riemannZeta z) := by
      simp [sub_eq_add_neg]
    simpa [S, hrewrite] using hn
  have hsum := add_le_add_left hbound1 ‖S‖
  have : ‖deriv riemannZeta z / riemannZeta z‖ ≤ C1 * Real.log |t| + ‖S‖ := le_trans htri hsum
  simpa [S, add_comm] using this

-- lem_sumK1abs: Sum bound
lemma lem_sumK1abs (t : ℝ) (ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + Complex.I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖z - ρ‖) ≤
    (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) := by
  intro c hfin hzcond
  -- Pointwise bound using lem_1abszrho
  have hptwise : ∀ ρ ∈ hfin.toFinset,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖z - ρ‖ ≤
      (1 / (2 * deltaz_t t)) * (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    intro ρ hρmem
    have hρ_in : ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρmem
    have hbase : 1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) :=
      lem_1abszrho t ht z ρ hρ_in hzcond
    have hnonneg : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      exact_mod_cast (Nat.zero_le (analyticOrderNatAt riemannZeta ρ))
    have := mul_le_mul_of_nonneg_left hbase hnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hsum := Finset.sum_le_sum hptwise
  -- Rewrite the right-hand side sum as a constant times the sum
  have hrw :=
    (Finset.mul_sum (s := hfin.toFinset)
      (f := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
      (a := (1 / (2 * deltaz_t t))))
  have hsum2 := hsum
  -- Use the rewriting equality in the desired direction
  rw [← hrw] at hsum2
  -- Finish
  simpa [div_eq_mul_inv] using hsum2

lemma helper_analyticOnNhd_shift_div (f : ℂ → ℂ) (c : ℂ)
    (h : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z) :
    AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (Metric.closedBall (0 : ℂ) 1) := by
  -- Unfold the definition of AnalyticOnNhd on a set: pointwise AnalyticAt on the set
  intro z hz
  -- From hz : z ∈ closedBall 0 1, we get ‖z‖ ≤ 1
  have hz_norm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  -- Hence z + c belongs to the translated ball: dist (z + c) c ≤ 1
  have hz_addc_mem : z + c ∈ Metric.closedBall c 1 := by
    -- Show dist (z + c) c ≤ 1 from ‖z‖ ≤ 1
    have : dist (z + c) c ≤ 1 := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz_norm
    simpa [Metric.mem_closedBall] using this
  -- f is analytic at z + c by the hypothesis h
  have h_f_at : AnalyticAt ℂ f (z + c) := h (z + c) hz_addc_mem
  -- The translation z ↦ z + c is analytic at z
  have h_addc : AnalyticAt ℂ (fun w => w + c) z := by
    simpa using! (analyticAt_id.add analyticAt_const)
  -- Therefore, the composition z ↦ f (z + c) is analytic at z
  have h_comp : AnalyticAt ℂ (fun w => f (w + c)) z :=
    (AnalyticAt.fun_comp h_f_at h_addc)
  -- Multiplication by the constant (1 / f c) is analytic; hence division by f c is analytic
  have h_mul_const : AnalyticAt ℂ (fun w => (1 / f c) * f (w + c)) z :=
    (analyticAt_const.mul h_comp)
  -- Rewrite to the desired form
  simpa [div_eq_mul_inv, mul_comm] using h_mul_const


lemma helper_bound_shifted (B R : ℝ)
    (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
    (h_bound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ :=
by
  intro z hz
  -- From z ∈ closedBall 0 R, we get ‖z‖ ≤ R
  have hz_norm : ‖z‖ ≤ R := by
    have hz' : dist z (0 : ℂ) ≤ R := by simpa [Metric.mem_closedBall] using hz
    simpa [Complex.dist_eq] using hz'
  -- Hence z + c ∈ closedBall c R
  have hz_ballc : z + c ∈ Metric.closedBall c R := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel] using hz_norm
  -- Apply the bound on f over the translated ball
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_ballc
  -- Since f c ≠ 0, its norm is positive
  have hpos : 0 < ‖f c‖ := (norm_pos_iff).2 hc
  -- Divide the inequality by ‖f c‖
  have hdiv : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ := (div_le_div_iff_of_pos_right hpos).2 hfb
  -- Rewrite the left-hand side using norm_div
  have hnorm_eq : ‖(fun w => f (w + c) / f c) z‖ = ‖f (z + c)‖ / ‖f c‖ := by
    change ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖
    simp
  simpa [hnorm_eq] using hdiv

lemma helper_g_zero_eq_one (f : ℂ → ℂ) (c : ℂ) (hc : f c ≠ 0) :
  (fun z => f (z + c) / f c) 0 = 1 := by
  simp [hc]

lemma helper_zerosetKfR_eq_center0 (r : ℝ) (f : ℂ → ℂ) :
  zerosetKfR r f = zerosetKfRc r (0 : ℂ) f := by
  ext ρ; simp [zerosetKfR, zerosetKfRc]

lemma helper_apply_jensen_to_g
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : AnalyticOnNhd ℂ g (Metric.closedBall 0 1))
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, (analyticOrderNatAt g ρ : ℝ)) ≤ Real.log B / Real.log (R / R1) := by
  classical
  have hbound :=
    lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R       g (h_g_analytic.mono (Metric.closedBall_subset_closedBall hR_lt_1.le)) hg0_one hfin_g  hg_le_B
  -- Rewrite to the desired division form
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound

lemma helper_sum_f_equals_sum_g
  (r : ℝ) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (hfin : (zerosetKfRc r c f).Finite) :
  (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℝ))
  =
  (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
      ((analyticOrderNatAt (fun z => f (z + c) / f c) ρ') : ℝ)) :=
by
  classical
  -- Notation
  let S : Finset ℂ := hfin.toFinset
  let φ : ℂ → ℂ := fun ρ => ρ - c
  let g' : ℂ → ℂ := fun z => f (z + c) / f c

  -- Relate the RHS indexing Finset to the image of S under φ
  have himg : (φ '' zerosetKfRc r c f).Finite := hfin.image φ
  have h_img_toFinset : ((hfin.image φ).toFinset) = S.image φ := by
    simpa [S] using (Set.Finite.toFinset_image (s := (zerosetKfRc r c f)) (f := φ)
      (hs := hfin) (h := himg))

  -- First, change the summand using equality of analytic orders at corresponding points
  have h_orders_match :
      (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderNatAt g' (φ ρ)) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρS
    -- ρ is in the zero set of f within the ball centered at c of radius r
    have hρ_mem : ρ ∈ zerosetKfRc r c f :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρS
    have hρ_ball : ρ ∈ Metric.closedBall c r := hρ_mem.1
    have hρ_fzero : f ρ = 0 := hρ_mem.2
    -- Show that ρ' = ρ - c is in the zero set for g' centered at 0
    have hρ'_ball : (φ ρ) ∈ Metric.closedBall (0 : ℂ) r := by
      -- dist ρ c ≤ r
      have hdist_le : dist ρ c ≤ r := by
        simpa [Metric.mem_closedBall] using hρ_ball
      -- translate the inequality to the origin
      have : dist (φ ρ) 0 ≤ r := by
        simpa [φ, dist_eq_norm] using (by simpa [dist_eq_norm] using hdist_le)
      simpa [Metric.mem_closedBall] using this
    have hρ'_gzero : g' (φ ρ) = 0 := by
      simp [g', φ, hρ_fzero, sub_eq_add_neg, add_comm]
    have hρ'_mem : (φ ρ) ∈ zerosetKfRc r (0 : ℂ) g' := ⟨hρ'_ball, hρ'_gzero⟩
    -- Apply fc_m_order to equate multiplicities
    have h_m_eq := fc_m_order c f hc (ρ' := φ ρ)
    -- (φ ρ) + c = ρ
    have h_m_eq' : analyticOrderAt g' (φ ρ) = analyticOrderAt f ρ := by
      simpa [g', φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_m_eq
    rw [analyticOrderNatAt, analyticOrderNatAt, h_m_eq']
  -- Next, rewrite the sum over the image using Finset.sum_image
  have h_inj : Function.Injective φ := by
    intro x y hxy
    -- add c to both sides to cancel the subtraction
    have := congrArg (fun z => z + c) hxy
    simpa [φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

  have h_sum_image :
      (∑ ρ' ∈ S.image φ, ((analyticOrderNatAt g' ρ') : ℝ)) =
      (∑ ρ ∈ S, (analyticOrderNatAt g' (φ ρ) : ℝ)) := by
    refine Finset.sum_image ?h
    intro x hx y hy hxy
    -- need x = y from φ x = φ y
    exact h_inj hxy

  -- Put everything together
  calc
    (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℝ))
        = (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ)) := by rfl
    _ = (∑ ρ ∈ S, (analyticOrderNatAt g' (φ ρ) : ℝ)) := h_orders_match
    _ = (∑ ρ' ∈ S.image φ, ((analyticOrderNatAt g' ρ') : ℝ)) := h_sum_image.symm
    _ = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderNatAt (fun z => f (z + c) / f c) ρ') : ℝ)) := by
          -- rewrite the index and the function names
          simp [S, φ, g', h_img_toFinset]

lemma helper_zero_set_shift_eq
  (r : ℝ) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0) :
  zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
  = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  simpa using fc_zeros r c f hc

lemma helper_fin_zero_g_is_image
  (r : ℝ) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (hfin : (zerosetKfRc r c f).Finite) :
  (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)).Finite :=
by
  classical
  have hset : zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
      = (fun ρ => ρ - c) '' (zerosetKfRc r c f) :=
    by simpa using fc_zeros r c f hc
  have hfin_img : ((fun ρ => ρ - c) '' (zerosetKfRc r c f)).Finite := hfin.image _
  simpa [hset] using hfin_img

lemma helper_AnalyticOnNhd_to_pointwise {S : Set ℂ} {f : ℂ → ℂ}
  (h : AnalyticOnNhd ℂ f S) : ∀ z ∈ S, AnalyticAt ℂ f z := by
  intro z hz
  exact h z hz

lemma no_zero_of_bound_one_and_center_one
  (R : ℝ) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_one : g 0 = 1)
  (hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1) :
  ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 := by
  intro z hz
  by_cases hRpos : 0 < R
  · -- differentiability inside the open ball
    have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) := by
      intro x hx
      have hxlt : ‖x‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans (le_of_lt hxlt) (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact ((h_g_analytic x hx_in1).differentiableAt).differentiableWithinAt
    -- continuity on the closed ball of radius R
    have hcont : ContinuousOn g (Metric.closedBall (0 : ℂ) R) := by
      intro x hx
      have hxleR : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans hxleR (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact (h_g_analytic x hx_in1).continuousAt.continuousWithinAt
    have hdcc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) :=
      DiffContOnCl.mk_ball hdiff hcont
    -- maximum of the modulus at 0 on the open ball of radius R
    have hIsMax : IsMaxOn (fun z => ‖g z‖) (Metric.ball (0 : ℂ) R) 0 := by
      intro y hy
      have hynormlt : ‖y‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hy
      have hyle : ‖y‖ ≤ R := le_of_lt hynormlt
      have hgy : ‖g y‖ ≤ 1 := hg_le_one y hyle
      simpa [hg0_one] using hgy
    -- apply maximum modulus principle on the closed ball
    have hEqOn :=
      Complex.eqOn_closedBall_of_isMaxOn_norm (z := (0 : ℂ)) (r := R) hdcc hIsMax
    have hz_eq : g z = (fun _ => g 0) z := hEqOn hz
    have hz_eq1 : g z = g 0 := by simpa using hz_eq
    have gz_one : g z = 1 := by simpa [hg0_one] using hz_eq1
    simp [gz_one]
  · -- If R ≤ 0, then any z in closedBall(0,R) must be 0, hence g z = 1 ≠ 0
    have hRle : R ≤ 0 := le_of_not_gt hRpos
    have hz_le : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
    have hz_norm_eq : ‖z‖ = 0 :=
      le_antisymm (le_trans hz_le hRle) (norm_nonneg z)
    have hz_zero : z = 0 := by
      simpa [norm_eq_zero] using hz_norm_eq
    simp [hz_zero, hg0_one]

lemma helper_sum_over_equal_finite_sets_orders
  {S T : Set ℂ} (g : ℂ → ℂ)
  (hS : S.Finite) (hT : T.Finite) (hST : S = T) :
  (∑ x ∈ hS.toFinset, (analyticOrderNatAt g x : ℝ))
  = (∑ x ∈ hT.toFinset, (analyticOrderNatAt g x : ℝ)) := by
  classical
  have hF : hS.toFinset = hT.toFinset := by
    ext x
    simp [Set.Finite.mem_toFinset, hST]
  simp [hF]

lemma helper_bound_on_ball_to_norm_imp
  {R : ℝ} {g : ℂ → ℂ} {M : ℝ}
  (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ M) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ M := by
  intro z hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R := by
    have : dist z (0 : ℂ) ≤ R := by
      simpa [dist_eq_norm] using hz
    simpa [Metric.mem_closedBall] using this
  exact hg z hz'

lemma lem_sum_m_rho_bound_c (B R R1 : ℝ)
  (hR1_pos : 0 < R1)
  (hR1_lt_R : R1 < R)
  (hR_lt_1 : R < 1)
  (f : ℂ → ℂ)
  (c : ℂ)
  (h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
  (h_f_nonzero_at_zero : f c ≠ 0)
  (hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B)
  (hfin : (zerosetKfRc R1 c f).Finite) :
      ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℝ) ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
  classical
  -- Define the shifted function g(z) = f(z+c)/f(c)
  let g : ℂ → ℂ := fun z => f (z + c) / f c

  -- g is analytic on the unit closed ball centered at 0
  have h_g_analyticOn : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
    helper_analyticOnNhd_shift_div f c h_f_analytic
  have h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z :=
    helper_AnalyticOnNhd_to_pointwise h_g_analyticOn

  -- g(0) = 1 and hence g(0) ≠ 0
  have hg0_one : g 0 = 1 := helper_g_zero_eq_one f c h_f_nonzero_at_zero
  have hg0_ne : g 0 ≠ 0 := by simp [hg0_one]

  -- Finiteness of zeros of g in radius R1 and set equalities
  have hfin_g0 : (zerosetKfRc R1 (0 : ℂ) g).Finite :=
    helper_fin_zero_g_is_image R1 c f h_f_nonzero_at_zero hfin
  have hZR_eq : zerosetKfR R1 g = zerosetKfRc R1 (0 : ℂ) g :=
    helper_zerosetKfR_eq_center0 R1 g
  have hfin_g : (zerosetKfR R1 g).Finite := by
    simpa [hZR_eq] using hfin_g0

  -- Bound on g on the closed ball of radius R
  have h_bound_shift : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_shifted B R c f
      h_f_nonzero_at_zero (fun z hz => hf_le_B z <| by simpa using hz)
  have hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_on_ball_to_norm_imp (R := R) (g := g) (M := B / ‖f c‖) h_bound_shift

  -- Show 1 ≤ B / ‖f c‖ to split into cases
  have hfc_le : ‖f c‖ ≤ B := by
    have : c ∈ Metric.closedBall c R := by
      have hRpos' : 0 ≤ R := le_of_lt (lt_trans hR1_pos hR1_lt_R)
      have : dist c c ≤ R := by simpa [dist_self] using hRpos'
      simpa [Metric.mem_closedBall] using this
    exact hf_le_B c this
  have hfc_pos : 0 < ‖f c‖ := (norm_pos_iff).2 h_f_nonzero_at_zero
  have hBdiv_ge_one : 1 ≤ B / ‖f c‖ := by
    have hdiv := (div_le_div_iff_of_pos_right hfc_pos).mpr hfc_le
    simpa [div_self (ne_of_gt hfc_pos)] using hdiv

  -- Equality between sums over zeros of f and zeros of g (shifted)
  have hsum_fg_eq :
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℝ))
        = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderNatAt g ρ') : ℝ)) :=
    helper_sum_f_equals_sum_g (r := R1) (c := c)
      (f := f) (hc := h_f_nonzero_at_zero) (hfin := hfin)

  -- Equality of sets for g-zeros and the image of f-zeros
  have hST_g_img : zerosetKfR R1 g
      = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) := by
    have h1 : zerosetKfR R1 g = zerosetKfRc R1 (0 : ℂ) g :=
      helper_zerosetKfR_eq_center0 R1 g
    have h2 : zerosetKfRc R1 (0 : ℂ) g
        = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
      helper_zero_set_shift_eq R1 c f h_f_nonzero_at_zero
    simpa [h1] using h2

  -- Now split into cases depending on whether B/‖f c‖ > 1 or = 1
  rcases lt_or_eq_of_le hBdiv_ge_one with hBdiv_gt_one | hBdiv_eq_one
  · -- Strict case: apply Jensen bound to g with B' = B / ‖f c‖
    have hsum_g_bound :=
      helper_apply_jensen_to_g (B := B / ‖f c‖) (R := R) (R1 := R1)
        (hB := hBdiv_gt_one)
        (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
        (g := g) (h_g_analytic := h_g_analyticOn)
        (hg0_one := hg0_one) (hfin_g := hfin_g) (hg_le_B := hg_le_B)
    -- Replace the indexing finite set using equality of sets S = image set
    have hsum_g_reindex :
        (∑ ρ ∈ hfin_g.toFinset, (analyticOrderNatAt g ρ : ℝ))
          = (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, (analyticOrderNatAt g ρ : ℝ)) :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
    -- Combine bounds and equalities to obtain the desired inequality
    have :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, (analyticOrderNatAt g ρ : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simpa [hsum_g_reindex] using hsum_g_bound
    -- Replace g-sum by f-sum using hsum_fg_eq
    simpa [hsum_fg_eq] using this
  · -- Equality case: B / ‖f c‖ = 1; show no zeros for g inside radius R, hence sum = 0
    have hBdiv_eq_one' : B / ‖f c‖ = 1 := by
      simpa [eq_comm] using hBdiv_eq_one
    have hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1 := by
      intro z hz
      have := hg_le_B z hz
      simpa [hBdiv_eq_one'] using this
    have g_nonzero_on_ball : ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 :=
      no_zero_of_bound_one_and_center_one R hR_lt_1 g h_g_analytic hg0_one hg_le_one
    -- zeroset within radius R1 is empty; hence the finite sum is zero
    have hS_empty : zerosetKfR R1 g = (∅ : Set ℂ) := by
      ext z; constructor
      · intro hz
        rcases hz with ⟨hzball, hzzero⟩
        have hzR1 : ‖z‖ ≤ R1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
        have hzR : ‖z‖ ≤ R := le_trans hzR1 (le_of_lt hR1_lt_R)
        have hzR' : z ∈ Metric.closedBall (0 : ℂ) R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
        exact (g_nonzero_on_ball z hzR') hzzero
      · intro hzfalse
        cases hzfalse
    have hsum_g_zero :
        (∑ ρ ∈ hfin_g.toFinset, (analyticOrderNatAt g ρ : ℝ)) = 0 := by
      have h :=
        helper_sum_over_equal_finite_sets_orders (g := g)
          (S := zerosetKfR R1 g) (T := (∅ : Set ℂ))
          (hS := hfin_g) (hT := Set.finite_empty) (hST := hS_empty)
      simpa using h
    -- Transport zero sum to the image-of-f sum via equality of finite sets S = image set
    have hsum_reindex :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
    have hsum_img_eq :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, (analyticOrderNatAt g ρ : ℝ))
          = (∑ ρ ∈ hfin_g.toFinset, (analyticOrderNatAt g ρ : ℝ)) := by
      simpa using hsum_reindex.symm
    have hsum_img_zero :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, (analyticOrderNatAt g ρ : ℝ)) = 0 := by
      simp [hsum_img_eq, hsum_g_zero]
    -- Hence the sum over f is zero via hsum_fg_eq
    have hsum_f_zero :
        (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℝ)) = 0 := by
      simpa [hsum_img_zero] using hsum_fg_eq
    -- Right-hand side equals zero since log(1) = 0
    have hRHS_zero : Real.log (B / ‖f c‖) / Real.log (R / R1) = 0 := by
      simp [hBdiv_eq_one']
    -- Conclude the desired inequality
    have :
        (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simp [hsum_f_zero, hRHS_zero]
    exact this

lemma lem_sum_m_rho_zeta :
    ∃ C_2 > 1, ∀ (t : ℝ) (_ : |t| > 3),
    let c := (3/2 : ℂ) + Complex.I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ C_2 * Real.log |t| := by
  classical
  -- Constants from auxiliary bounds
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨a, ha_pos, ha_bound⟩ := zeta_low_332
  -- Radii
  let R1 : ℝ := 5 / 6
  let R : ℝ := 8 / 9
  let logRatio : ℝ := Real.log (R / R1)
  -- Define constant from b and a
  let u : ℝ := Real.log (b / a)
  let C2 : ℝ := max 2 ((1 + |u|) / logRatio)
  have hC2_gt_one : 1 < C2 := by
    have htwo_lt : (1 : ℝ) < 2 := by norm_num
    have hle : (2 : ℝ) ≤ C2 := by
      have := le_max_left (2 : ℝ) ((1 + |u|) / logRatio)
      simp [C2]
    exact lt_of_lt_of_le htwo_lt hle
  refine ⟨C2, hC2_gt_one, ?_⟩
  intro t ht c hfin
  -- Numeric facts about radii
  have hR1_pos : 0 < R1 := by dsimp [R1]; norm_num
  have hR1_lt_R : R1 < R := by dsimp [R1, R]; norm_num
  have hR_lt_1 : R < 1 := by dsimp [R]; norm_num
  have hR_le_one : R ≤ (1 : ℝ) := by dsimp [R]; norm_num
  -- Analyticity on closedBall c 1: ζ is analytic off {1}, and the ball avoids 1 for |t|>1
  have ht1 : |t| > 1 := lt_trans (by norm_num) ht
  have h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ riemannZeta z := by
    intro z hz
    have hz_ne_one : z ≠ (1 : ℂ) := (D1cinTt_pre t ht1) z (by simpa [c] using hz)
    exact zetaanalOnnot1 z hz_ne_one
  -- Nonzero at center
  have h_nonzero : riemannZeta c ≠ 0 := by simpa [c] using zetacnot0 t
  -- Upper bound on |ζ| on closedBall c R with B = b * |t|
  have ht2 : |t| > 2 := by linarith
  have h_upper_on_ball1 : ∀ z ∈ Metric.closedBall c 1, ‖riemannZeta z‖ < b * |t| := by
    have h := hb_bound t ht2
    intro z hz; simpa [c] using h z (by simpa [c] using hz)
  have hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖riemannZeta z‖ ≤ b * |t| := by
    intro z hz
    have hz1 : z ∈ Metric.closedBall c 1 :=
      (Metric.closedBall_subset_closedBall hR_le_one) hz
    exact le_of_lt (h_upper_on_ball1 z hz1)
  -- Show B = b * |t| > 1
  have hb_pos : 0 < b := lt_trans (by norm_num) hb_gt1
  have htabove1 : (1 : ℝ) ≤ |t| := le_of_lt ht1
  have hb_le_B : b ≤ b * |t| := by
    have := mul_le_mul_of_nonneg_left htabove1 (le_of_lt hb_pos)
    simpa [one_mul] using this
  have hBpos : 1 < b * |t| := lt_of_lt_of_le hb_gt1 hb_le_B
  -- Apply the Jensen-type bound centered at c, with R1=5/6, R=8/9
  have h_sum_bound :=
    lem_sum_m_rho_bound_c (B := b * |t|) (R := R) (R1 := R1)
      (hR1_pos := hR1_pos)
      (hR1_lt_R := hR1_lt_R)
      (hR_lt_1 := hR_lt_1)
      (f := riemannZeta) (c := c)
      (h_f_analytic := h_f_analytic)
      (h_f_nonzero_at_zero := h_nonzero)
      (hf_le_B := hf_le_B)
      (hfin := hfin)
  -- Positivity of logRatio
  have hlogRatio_pos : 0 < logRatio := by
    have : 1 < R / R1 := by dsimp [R, R1]; norm_num
    exact Real.log_pos this
  -- Lower bound for |ζ c|
  have h_zeta_ge_a : a ≤ ‖riemannZeta c‖ := by
    simpa [c, mul_comm] using! ha_bound t
  -- Now convert RHS to a multiple of log |t|
  -- First, bound the log of the quotient using a ≤ ‖ζ c‖
  have ht_abs_pos : 0 < |t| := lt_trans (by norm_num) ht
  have hζ_norm_pos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr h_nonzero
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have ht_abs_ne : (|t| : ℝ) ≠ 0 := ne_of_gt ht_abs_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hlog_split1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        = (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖ := by
    have : Real.log (b * |t|) = Real.log b + Real.log |t| :=
      Real.log_mul hb_ne ht_abs_ne
    have :
        Real.log ((b * |t|) / ‖riemannZeta c‖)
          = Real.log (b * |t|) - Real.log ‖riemannZeta c‖ :=
      Real.log_div (by exact mul_ne_zero hb_ne ht_abs_ne) (ne_of_gt hζ_norm_pos)
    simp [this, Real.log_mul hb_ne ht_abs_ne]
  have hlog_div_eq : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div hb_ne ha_ne
  have hlog_a_le : Real.log a ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log (by exact ha_pos) (by exact h_zeta_ge_a)
  have hneg : -(Real.log ‖riemannZeta c‖) ≤ -Real.log a := by
    simpa using (neg_le_neg hlog_a_le)
  have hRHS_le_const :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        ≤ Real.log |t| + Real.log (b / a) := by
    -- Rewrite LHS and RHS and use hneg
    have :
        (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖
          ≤ (Real.log b + Real.log |t|) - Real.log a := by
      simpa [sub_eq_add_neg] using add_le_add_right hneg (Real.log b + Real.log |t|)
    simpa [hlog_split1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hlog_div_eq]
      using this
  -- Divide by positive logRatio
  have hRHS1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖) / logRatio
        ≤ (Real.log |t| + Real.log (b / a)) / logRatio := by
    exact div_le_div_of_nonneg_right hRHS_le_const (le_of_lt hlogRatio_pos)
  -- Bound additive constant by |u|
  have hlogt_ge_one : (1 : ℝ) ≤ Real.log |t| := by
    -- log |t| ≥ log 3 ≥ 1
    have h3le : (3 : ℝ) ≤ |t| := le_of_lt ht
    have hlog3_le : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) h3le
    have h_exp_le : Real.exp (1 : ℝ) ≤ 3 := by linarith[Real.exp_one_lt_d9]
    have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : 0 < (3 : ℝ))).mpr h_exp_le
    exact le_trans hlog3_ge_one hlog3_le
  have hadd_le : Real.log |t| + Real.log (b / a) ≤ (1 + |u|) * Real.log |t| := by
    have haux1 : Real.log (b / a) ≤ |u| := by simpa [u] using le_abs_self (Real.log (b / a))
    have haux2 : |u| ≤ |u| * Real.log |t| := by
      have hnonneg : 0 ≤ |u| := abs_nonneg _
      have h1le : (1 : ℝ) ≤ Real.log |t| := hlogt_ge_one
      simpa [one_mul] using (mul_le_mul_of_nonneg_left h1le hnonneg)
    calc
      Real.log |t| + Real.log (b / a)
          ≤ Real.log |t| + |u| := by gcongr
      _ ≤ Real.log |t| + (|u| * Real.log |t|) := by gcongr
      _ = (1 + |u|) * Real.log |t| := by ring
  have hRHS2 :
      (Real.log |t| + Real.log (b / a)) / logRatio
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := div_le_div_of_nonneg_right hadd_le (le_of_lt hlogRatio_pos)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hfinal :
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ))
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := le_trans h_sum_bound hRHS1
    exact le_trans this hRHS2
  -- Compare with C2 * log |t|
  have hC2_ge : ((1 + |u|) / logRatio) ≤ C2 := by
    have := le_max_right (2 : ℝ) ((1 + |u|) / logRatio)
    simp [C2]
  have hlogt_nonneg : 0 ≤ Real.log |t| := le_trans (by norm_num) hlogt_ge_one
  have hscale := mul_le_mul_of_nonneg_right hC2_ge hlogt_nonneg
  exact le_trans hfinal hscale

lemma lem_sumKdeltatlogt :
  ∃ C_3 > 1, ∀ (t : ℝ) (_ : |t| > 3),
  let c := (3/2 : ℂ) + Complex.I * t;
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖z - ρ‖) ≤
      (C_3 / (deltaz_t t)) * Real.log |t| := by
  -- Extract C_2 from lem_sum_m_rho_zeta
  obtain ⟨C_2, hC_2_pos, hC_2_bound⟩ := lem_sum_m_rho_zeta

  -- Use C_3 = C_2
  use C_2

  constructor
  · -- Prove C_3 > 1, which follows from C_2 > 1
    exact hC_2_pos

  · -- Main proof
    intro t ht c hfin z hz

    -- Apply lem_sumK1abs to get the first bound
    have h1 := lem_sumK1abs t ht z hfin hz

    -- Apply lem_sum_m_rho_zeta to get the second bound
    have h2 := hC_2_bound t ht hfin

    -- Get positivity of deltaz_t t
    have ht2 : |t| > 2 := by linarith [ht]
    have h_delta_pos : 0 < deltaz_t t := (lem_delta19.2 t ht2).1

    -- Show that |t| ≥ 1 for log nonnegative
    have h_t_ge_one : (1 : ℝ) ≤ |t| := by linarith [ht]

    -- Combine the bounds
    calc
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖z - ρ‖)
        ≤ (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) := h1
      _ ≤ (1 / (2 * deltaz_t t)) * (C_2 * Real.log |t|) := by
          apply mul_le_mul_of_nonneg_left h2
          apply div_nonneg (by norm_num)
          apply mul_nonneg (by norm_num) (le_of_lt h_delta_pos)
      _ = (C_2 / (2 * deltaz_t t)) * Real.log |t| := by ring
      _ ≤ (C_2 / deltaz_t t) * Real.log |t| := by
          apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg h_t_ge_one)
          -- Show C_2 / (2 * deltaz_t t) ≤ C_2 / deltaz_t t
          apply div_le_div_of_nonneg_left (le_of_lt (lt_trans zero_lt_one hC_2_pos))
          · exact h_delta_pos
          · -- Show deltaz_t t ≤ 2 * deltaz_t t
            calc deltaz_t t
              = 1 * deltaz_t t := by rw [one_mul]
            _ ≤ 2 * deltaz_t t := by
              apply mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt h_delta_pos)

private lemma log_add_two_lt_two_mul_log {t : ℝ} (ht : 3 < |t|) :
    Real.log (|t| + 2) < 2 * Real.log |t| := by
  have h_t_pos : 0 < |t| := by linarith [abs_nonneg t]
  have h_ineq : |t| + 2 < 2 * |t| := by linarith
  have h_log_ineq := Real.log_lt_log (by linarith [abs_nonneg t] : (0 : ℝ) < |t| + 2) h_ineq
  rw [Real.log_mul (by norm_num) (ne_of_gt h_t_pos)] at h_log_ineq
  have h_log2_bound : Real.log 2 < Real.log |t| :=
    Real.log_lt_log (by norm_num) (by linarith : (2 : ℝ) < |t|)
  linarith [h_log_ineq, h_log2_bound]

lemma lem_sumKlogt2 :
  ∃ C_4 > 1, ∀ (t : ℝ) (_ : |t| > 3),
  let c := (3/2 : ℂ) + Complex.I * t
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖z - ρ‖) ≤
      C_4 * Real.log |t|^2 := by
  -- Apply lem_sumKdeltatlogt to get C_3
  obtain ⟨C_3, hC_3_gt, hC_3⟩ := lem_sumKdeltatlogt

  -- Define C_4 large enough to absorb constant factors
  use max (100 * C_3 / zerofree_constant) 2

  constructor
  · exact lt_max_of_lt_right (by norm_num : (2 : ℝ) > 1)

  · intro t ht c hfin z hz
    -- Apply the bound from lem_sumKdeltatlogt
    have h_bound := hC_3 t ht hfin z hz

    -- Essential positivity conditions
    have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
    have h_log_t_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
    have hC_3_pos : 0 < C_3 := lt_trans zero_lt_one hC_3_gt
    have h_zerofree_pos : 0 < zerofree_constant := zerofree_constant_pos

    -- Key bound: log(|t| + 2) ≤ 2 * log|t| for |t| > 3
    have h_log_bound : Real.log (|t| + 2) ≤ 2 * Real.log |t| :=
      (log_add_two_lt_two_mul_log ht).le

    -- Use the definition of deltaz_t to bound the key ratio
    have h_deltaz_eq : deltaz_t t = (zerofree_constant / 20) / Real.log (|t| + 2) := by
      simp [deltaz_t, deltaz]

    -- The key insight: bound C_3 / deltaz_t t * log|t| using the definition and log bound
    have h_main_bound : C_3 / deltaz_t t * Real.log |t| ≤
                        40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by
      -- Substitute deltaz_t definition
      rw [h_deltaz_eq]

      -- Use basic division properties to rewrite
      have h_div_rewrite : C_3 / ((zerofree_constant / 20) / Real.log (|t| + 2)) =
                          C_3 * Real.log (|t| + 2) * 20 / zerofree_constant := by
        field [ne_of_gt h_zerofree_pos, ne_of_gt (Real.log_pos (by linarith [abs_nonneg t] : (1 : ℝ) < |t| + 2))]

      rw [h_div_rewrite]
      -- Now bound using the logarithm inequality
      have h_pos_factor : 0 ≤ C_3 * 20 / zerofree_constant :=
        div_nonneg (mul_nonneg (le_of_lt hC_3_pos) (by norm_num)) (le_of_lt h_zerofree_pos)

      calc C_3 * Real.log (|t| + 2) * 20 / zerofree_constant * Real.log |t|
          = C_3 * 20 / zerofree_constant * Real.log (|t| + 2) * Real.log |t| := by ring
      _ ≤ C_3 * 20 / zerofree_constant * (2 * Real.log |t|) * Real.log |t| := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_log_bound h_pos_factor)
                (le_of_lt h_log_t_pos)
      _ = 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by simp [pow_two]; ring

    -- Final bound using C_4 definition
    calc (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖z - ρ‖)
        ≤ C_3 / deltaz_t t * Real.log |t| := h_bound
    _ ≤ 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := h_main_bound
    _ ≤ max (100 * C_3 / zerofree_constant) 2 * (Real.log |t|)^2 := by
        have h_factor_bound : 40 * C_3 / zerofree_constant ≤ max (100 * C_3 / zerofree_constant) 2 := by
          have h_coeff_ineq : 40 * C_3 ≤ 100 * C_3 := by
            -- Use mul_le_mul_of_nonneg_right: if a ≤ b and 0 ≤ c, then a * c ≤ b * c
            have h_coeff : (40 : ℝ) ≤ 100 := by norm_num
            exact mul_le_mul_of_nonneg_right h_coeff (le_of_lt hC_3_pos)
          have h_div_ineq : 40 * C_3 / zerofree_constant ≤ 100 * C_3 / zerofree_constant := by
            -- Apply division monotonicity
            exact div_le_div_of_nonneg_right h_coeff_ineq (le_of_lt h_zerofree_pos)
          exact le_trans h_div_ineq (le_max_left _ _)
        exact mul_le_mul_of_nonneg_right h_factor_bound (sq_nonneg _)


lemma lem_logDerivZetalogt0 :
  ∃ C > 1,
  ∀ (t : ℝ) (_ : |t| > 3),
    ∀ s : ℂ, (1 - deltaz_t t) ≤ s.re ∧ s.re ≤ 3/2 ∧ s.im = t →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log |t|^2 := by
  -- Apply the two main lemmas as stated in the informal proof
  obtain ⟨C_1, hC_1_gt, hC_1⟩ := lem_Zeta_Triangle_ZFR
  obtain ⟨C_4, hC_4_gt, hC_4⟩ := lem_sumKlogt2

  -- Set C = C_1 + C_4
  use C_1 + C_4

  constructor
  · -- Prove C > 1
    linarith [hC_1_gt, hC_4_gt]

  · -- Main proof
    intro t ht s hs

    -- Define the center and get finiteness
    let c := (3/2 : ℂ) + Complex.I * t
    have hfin := lem_finiteKzeta t

    -- Apply lem_Zeta_Triangle_ZFR
    have h_triangle := hC_1 t ht hfin s hs

    -- Apply lem_triangle_ZFR to bound the sum norm
    have h_triangle_ineq := lem_triangle_ZFR t s hfin hs

    -- Apply lem_sumKlogt2 to bound the sum
    have h_sum_bound := hC_4 t ht hfin s hs

    -- Show that log |t| ≤ (log |t|)^2 for |t| > 3
    have h_log_sq_ge : Real.log |t| ≤ Real.log |t|^2 := by
      have h_log_ge_one : (1 : ℝ) ≤ Real.log |t| := by
        -- Since |t| > 3 > e, we have log |t| > log e = 1
        have h_t_gt_e : Real.exp 1 < |t| := by
          have h_e_bound : Real.exp 1 < 3 := by linarith[Real.exp_one_lt_d9]
          linarith [ht]
        -- Apply log monotonicity: exp 1 ≤ |t| implies 1 ≤ log |t|
        have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (le_of_lt h_t_gt_e)
      have h_log_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
      rw [pow_two]
      exact le_mul_of_one_le_right (le_of_lt h_log_pos) h_log_ge_one

    -- Combine the bounds
    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ ‖(∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))‖ + C_1 * Real.log |t| := h_triangle
      _ ≤ (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖s - ρ‖) + C_1 * Real.log |t| := by
          gcongr
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t| := by
          gcongr
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t|^2 := by
          -- Use the fact that log |t| ≤ (log |t|)^2
          have h_c1_nonneg : 0 ≤ C_1 := le_of_lt (lt_trans zero_lt_one hC_1_gt)
          exact add_le_add_right (mul_le_mul_of_nonneg_left h_log_sq_ge h_c1_nonneg) _
      _ = (C_4 + C_1) * Real.log |t|^2 := by ring
      _ = (C_1 + C_4) * Real.log |t|^2 := by ring



-- lemma exists_T_growth (c : ℝ) (hc : 0 < c) :
--   ∀ t : ℝ, |t| > 3 →
--     (Real.log (|t| + 2))^2 * (|t| + 2) > 3 * c / 4 := by
--   refine ⟨max (Real.exp 1) (3 * c / 4), ?_⟩
--   intro t ht
--   have hpos : 0 < |t| + 2 := by
--     have : (0 : ℝ) ≤ |t| := abs_nonneg t
--     linarith
--   have habsp : |t| < |t| + 2 := by
--     have : (0 : ℝ) < 2 := by norm_num
--     linarith
--   have hexp_lt_abs : Real.exp 1 < 3 := by
--     simpa using lem_three_gt_e
--   have hexp_lt_abs_plus : Real.exp 1 < |t| + 2 := lt_trans hexp_lt_abs habsp
--   have hltlog : 1 < Real.log (|t| + 2) :=
--     (Real.lt_log_iff_exp_lt hpos).mpr hexp_lt_abs_plus
--   have hlog_pos : 0 < Real.log (|t| + 2) := lt_trans (by norm_num) hltlog
--   have hone_lt_sq : 1 < (Real.log (|t| + 2))^2 := by
--     have hlog_lt_sq : Real.log (|t| + 2) < (Real.log (|t| + 2))^2 := by
--       have : 1 * Real.log (|t| + 2) < Real.log (|t| + 2) * Real.log (|t| + 2) :=
--         mul_lt_mul_of_pos_right hltlog hlog_pos
--       simpa [one_mul, pow_two] using this
--     exact lt_trans hltlog hlog_lt_sq
--   have hprod_gt_absplus : (|t| + 2) < (Real.log (|t| + 2))^2 * (|t| + 2) := by
--     have : 1 * (|t| + 2) < (Real.log (|t| + 2))^2 * (|t| + 2) :=
--       mul_lt_mul_of_pos_right hone_lt_sq hpos
--     simpa [one_mul] using this
--   have hc_le_T : 3 * c / 4 ≤ max (Real.exp 1) (3 * c / 4) := le_max_right _ _
--   have h3c4_lt_abs : 3 * c / 4 < |t| := lt_of_le_of_lt hc_le_T ht
--   have h1 : 3 * c / 4 < |t| + 2 := lt_trans h3c4_lt_abs habsp
--   have hchain : 3 * c / 4 < (Real.log (|t| + 2))^2 * (|t| + 2) := lt_trans h1 hprod_gt_absplus
--   exact hchain


-- lemma exists_T_im_large (c T0 : ℝ) (hc : 0 < c) :
--   ∃ T : ℝ, T > 0 ∧ ∀ t : ℝ, |t| > T → |t| - (c / 4) / Real.log (|t| + 2) ≥ T0 := by
--   refine ⟨max (T0 + 1) (Real.exp (c / 4)), ?_, ?_⟩
--   · have hpos : 0 < Real.exp (c / 4) := by simpa using Real.exp_pos (c / 4)
--     exact lt_of_lt_of_le hpos (le_max_right _ _)
--   · intro t ht
--     have hpos_arg : 0 < |t| + 2 := by
--       have : (0 : ℝ) ≤ |t| := abs_nonneg t
--       linarith
--     -- |t| is large
--     have habs_gt : |t| > T0 + 1 := lt_of_le_of_lt (le_max_left _ _) ht
--     -- log(|t|+2) is large
--     have hexp_le_T : Real.exp (c / 4) ≤ max (T0 + 1) (Real.exp (c / 4)) := by
--       exact le_max_right _ _
--     have hexp_lt_abs : Real.exp (c / 4) < 3 := lt_of_le_of_lt hexp_le_T ht
--     have habs_lt_abs_plus : |t| < |t| + 2 := by
--       have : (0 : ℝ) < 2 := by norm_num
--       linarith
--     have hexp_lt_abs_plus : Real.exp (c / 4) < |t| + 2 := lt_trans hexp_lt_abs habs_lt_abs_plus
--     have hlog_gt : c / 4 < Real.log (|t| + 2) :=
--       (Real.lt_log_iff_exp_lt hpos).mpr hexp_lt_abs_plus
--     have hc4pos : 0 < c / 4 := by
--       have : 0 < (4 : ℝ) := by norm_num
--       exact div_pos hc this
--     have hlog_pos : 0 < Real.log (|t| + 2) := lt_trans hc4pos hlog_gt
--     have hfrac_lt_one : (c / 4) / Real.log (|t| + 2) < 1 :=
--       (div_lt_one hlog_pos).2 hlog_gt
--     -- conclude
--     have hgt : |t| - (c / 4) / Real.log (|t| + 2) > T0 := by
--       have : |t| - (c / 4) / Real.log (|t| + 2) > (T0 + 1) - 1 := by
--         linarith [habs_gt, hfrac_lt_one]
--       simpa using this
--     exact le_of_lt hgt

lemma lem_term_real_nonneg (n : ℕ) (σ : ℝ) : ∃ r ≥ (0:ℝ), ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r : ℂ) := by
  -- Define the real number r to be the real quotient
  let r : ℝ := (ArithmeticFunction.vonMangoldt n) / ((n : ℝ) ^ σ)
  refine ⟨r, ?_, ?_⟩
  · -- Show r ≥ 0 using nonnegativity of vonMangoldt and nonnegativity of the denominator
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_nonneg : 0 ≤ (n : ℝ) ^ σ := by
      simpa using (Real.rpow_nonneg hbase_nonneg σ)
    -- r = vonMangoldt n * ((n:ℝ)^σ)⁻¹ ≥ 0
    have hv_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n) := by
      simp
    have : 0 ≤ (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ σ)⁻¹ :=
      mul_nonneg hv_nonneg (inv_nonneg.mpr hden_nonneg)
    simpa [r, div_eq_mul_inv] using this
  · -- Show the complex quotient equals (r : ℂ)
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_eq : (((n : ℝ) ^ σ : ℝ) : ℂ) = (n : ℂ) ^ (σ : ℂ) := by
      simpa using (Complex.ofReal_cpow (x := (n : ℝ)) (hx := hbase_nonneg) (y := σ))
    calc
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ)))
          = ((ArithmeticFunction.vonMangoldt n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) := by
              simp [hden_eq.symm]
      _ = (((ArithmeticFunction.vonMangoldt n : ℝ) / ((n : ℝ) ^ σ)) : ℝ) := by
              simp
      _ = (r : ℂ) := by rfl


lemma lem_norm_logDeriv_le_tsum (s : ℂ) (hs : 1 < s.re) :
  ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := by
  classical
  -- Define f(n) = Λ(n) as complex-valued coefficients
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  -- Summability of the L-series terms on Re s > 1
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs)
  -- Hence the sum of norms is summable as well in ℂ (finite-dimensional over ℝ)
  have hsum_norm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    (summable_norm_iff).mpr hsum_term
  -- Identification of the L-series with the negative logarithmic derivative
  have hEq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [f] using! (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs)
  -- Pointwise identification of the norm of the L-series term with the explicit quotient
  have hpoint : (fun n : ℕ => ‖LSeries.term f s n‖)
                = (fun n : ℕ => ‖f n / ((n : ℂ) ^ s)‖) := by
    funext n
    by_cases h0 : n = 0
    · -- At n = 0, both sides are 0
      subst h0
      -- Use that Λ(0) = 0 since it is a ZeroHom
      have hf0r : ArithmeticFunction.vonMangoldt 0 = 0 := by
        simp
      have hf0 : f 0 = 0 := by simp [f, hf0r]
      simp [LSeries.term, f, hf0]
    · -- For n ≠ 0, the term is exactly f n / (n^s)
      simp [LSeries.term, f, h0]
  -- Apply the inequality ‖tsum f‖ ≤ ∑ ‖f‖ and rewrite
  calc
    ‖deriv riemannZeta s / riemannZeta s‖
        = ‖- deriv riemannZeta s / riemannZeta s‖ := by simp [norm_neg]
    _ = ‖∑' n : ℕ, LSeries.term f s n‖ := by simp [hEq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ :=
          norm_tsum_le_tsum_norm (f := fun n : ℕ => LSeries.term f s n) hsum_norm
    _ = ∑' n : ℕ, ‖f n / ((n : ℂ) ^ s)‖ := by simp [hpoint]
    _ = ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := rfl

lemma lem_tsum_norm_vonMangoldt_depends_on_Re_cast (s : ℂ) (σ : ℝ)
  (hσ : σ = s.re) (hs : 1 < s.re) :
  (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
    = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  -- s.re ≠ 0 and σ ≠ 0
  have hre_ne_zero : s.re ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have hσ_ne_zero : σ ≠ 0 := by
    have : 0 < σ := by simpa [hσ] using (lt_trans zero_lt_one hs)
    exact ne_of_gt this
  -- Show equality of the summands for each n, then conclude by congrArg on tsum
  have hterm : (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
      = (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n
    -- Denominator norms depend only on real part of exponent
    have hden_s : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n hre_ne_zero
    have hden_σ : ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ (σ : ℂ).re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa [Complex.ofReal_re] using hσ_ne_zero)
    calc
      ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖
          = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ s‖ := by simp
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ s.re) := by
            simp [hden_s, Complex.norm_real]
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ σ) := by simp [hσ]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ (σ : ℂ)‖ := by
            simp [hden_σ, Complex.ofReal_re, Complex.norm_real]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖ := by simp
  simpa using congrArg (fun f : ℕ → ℝ => ∑' n, f n) hterm

lemma helper_norm_neg_logDeriv_eq_tsum_norm (σ : ℝ) (hσ : 1 < σ) :
  ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ =
    (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  classical
  -- Set s = σ as a complex number
  let s : ℂ := (σ : ℂ)
  -- Define the coefficient function f(n) = Λ(n) as a complex-valued function
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  -- Define the series terms u n = LSeries.term f s n
  let u : ℕ → ℂ := fun n => LSeries.term f s n
  -- Summability of the L-series terms for Re s > 1
  have hs_re : 1 < s.re := by simpa using! hσ
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs_re)
  -- Thus u is summable
  have hsum_u : Summable u := hsum_term
  -- Equality of the sum with the logarithmic derivative
  have hL_eq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs_re)
  have hsum_eq : (∑' n, u n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [u] using hL_eq
  -- For each n, the term u n is a nonnegative real number (as a complex number)
  -- Using the explicit expression of LSeries.term
  have hterm_as_div : ∀ n,
      u n = ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) := by
    intro n; by_cases h0 : n = 0
    · -- n = 0
      subst h0; simp [u, LSeries.term, f, s]
    · -- n ≠ 0
      simp [u, LSeries.term, f, s, h0]
  -- Choose a nonnegative real representative for each term
  let r : ℕ → ℝ := fun n => Classical.choose (lem_term_real_nonneg n σ)
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ)).1
  have hr_cast : ∀ n,
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r n : ℂ) := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ)).2
  have hr_eq' : ∀ n, u n = (r n : ℂ) := by
    intro n; simpa [hterm_as_div n] using (hr_cast n)
  -- Summability of the real sequence r
  have hsum_rc : Summable (fun n => (r n : ℂ)) := by
    simpa [u, hr_eq'] using hsum_u
  have hsum_r : Summable r := (Complex.summable_ofReal).1 hsum_rc
  -- Identify the complex sum with the real sum cast to ℂ
  have hsum_u_as_real : (∑' n, u n) = ((∑' n, r n) : ℝ) := by
    have hru : (fun n => (r n : ℂ)) = u := by
      funext n; symm; exact hr_eq' n
    have := (Complex.ofReal_tsum (f := r) (L := SummationFilter.unconditional _))
    -- ((∑' n, r n) : ℂ) = ∑' n, (r n : ℂ)
    -- hence (∑' n, u n) = ((∑' n, r n) : ℝ)
    simpa [hru] using this.symm
  -- Equality of the sum of norms with the real sum S = ∑ r n
  have hpoint_norm : (fun n : ℕ => ‖u n‖)
        = (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n; by_cases h0 : n = 0
    · subst h0; simp [u, LSeries.term, f, s]
    · simp [u, LSeries.term, f, s, h0]
  have hnorm_fun : (fun n : ℕ => ‖u n‖) = r := by
    funext n; simp [hr_eq' n, Complex.norm_real, abs_of_nonneg (hr_nonneg n)]
  -- Rewrite both sides in terms of the real sum S
  set S : ℝ := ∑' n, r n
  have hS_nonneg : 0 ≤ S := tsum_nonneg hr_nonneg
  -- Conclude equality of norms and sum of norms
  have h_left : ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
      = ‖∑' n, u n‖ := by
    have : - deriv riemannZeta s / riemannZeta s = ∑' n, u n := by simpa [hsum_u_as_real] using hsum_eq.symm
    simp [s, this]
  have h_mid : ‖∑' n, u n‖ = S := by
    -- Norm of a nonnegative real equals itself
    have : ‖((S : ℝ) : ℂ)‖ = S := by simp [Complex.norm_real, abs_of_nonneg hS_nonneg]
    simpa [S, hsum_u_as_real] using this
  have h_right : (∑' n : ℕ, ‖u n‖) = S := by simp [S, hnorm_fun]
  -- Final rewrite to the desired expression
  calc
    ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = ‖∑' n, u n‖ := h_left
    _ = S := h_mid
    _ = (∑' n : ℕ, ‖u n‖) := h_right.symm
    _ = (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
          simp [hpoint_norm]

theorem lem_zetacenterbd :
  ∀ t : ℝ,
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤
      ‖deriv riemannZeta σ / riemannZeta σ‖ := by
  intro t σ hσge
  -- Set s = σ + it
  set s : ℂ := Complex.mk σ t
  -- Since σ ≥ 3/2 > 1, we have 1 < s.re and 1 < σ
  have hs : 1 < s.re := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
  have hσgt1 : 1 < σ := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
  -- First bound by sum of norms of the L-series terms at s
  have h_le_sum := lem_norm_logDeriv_le_tsum s hs
  have h1 : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := by
    simpa [norm_div, Complex.norm_real] using h_le_sum
  -- The sum of norms depends only on the real part of s, i.e., equals the sum at σ ∈ ℝ
  have h_dep :
      (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    -- here s.re = σ
    have hre : σ = s.re := by simp [s]
    simpa using (lem_tsum_norm_vonMangoldt_depends_on_Re_cast s σ hre hs)
  have h_dep_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖)
        = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := by
    simpa [norm_div, Complex.norm_real] using h_dep
  -- At real σ, the sum of norms equals the norm of -ζ'/ζ(σ)
  have h_sum_eq_norm :
      ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) :=
    helper_norm_neg_logDeriv_eq_tsum_norm σ hσgt1
  have h_sum_eq_norm_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖)
        = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    simpa [norm_div, Complex.norm_real] using h_sum_eq_norm.symm
  -- Chain the inequalities/equalities
  have h_main : ‖deriv riemannZeta s / riemannZeta s‖ ≤ ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          ≤ (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := h1
      _ = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := h_dep_ratio
      _ = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := h_sum_eq_norm_ratio
  -- Finally, remove the minus sign and rewrite s = σ + it
  simpa [s, norm_neg] using h_main

lemma lem_logDerivZetalogt32 :
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C := by
  -- Obtain the constant from the real-axis bound near 1
  obtain ⟨C0, hC0_gt1, hC0_bound⟩ := Z0bound_const
  -- Choose a convenient constant C = C0 + 2
  refine ⟨C0 + 2, by linarith, ?_⟩
  intro t ht σ hσ
  -- Reduce to the real axis using the center bound
  have h_center := lem_zetacenterbd t σ hσ
  -- Set δ = σ - 1 (> 0 and ≥ 1/2)
  set δ : ℝ := σ - 1
  have hδ_pos : 0 < δ := by linarith [hσ]
  have hδ_ge_half : (1 / 2 : ℝ) ≤ δ := by linarith [hσ]
  -- Apply the constant bound near 1 on the real axis
  have hZ0 := hC0_bound δ hδ_pos
  -- Triangle inequality to bound ‖-logDerivZeta (1+δ)‖ by the sum of the two terms
  have h_tri : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤
      ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ + ‖(1 / (δ : ℂ))‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) (1 / (δ : ℂ)))
  -- Bound ‖1/(δ : ℂ)‖ ≤ 2 using δ ≥ 1/2
  have h_norm_div_le_two : ‖(1 / (δ : ℂ))‖ ≤ 2 := by
    -- compute ‖1 / (δ:ℂ)‖ = 1 / ‖(δ:ℂ)‖ and ‖(δ:ℂ)‖ = |δ|
    have hnorm_div : ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      simp
    have hnorm_ofReal : ‖(δ : ℂ)‖ = |δ| := by
      simp
    -- From δ ≥ 1/2 > 0, get 1 / |δ| ≤ 2
    have h_abs_ge : (1 / 2 : ℝ) ≤ |δ| := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [abs_of_nonneg hδ_nonneg] using hδ_ge_half
    have hhalfpos : (0 : ℝ) < 1 / 2 := by norm_num
    have hone_div_abs_le_two : 1 / |δ| ≤ 2 := by
      simpa using (one_div_le_one_div_of_le hhalfpos h_abs_ge)
    -- Conclude the bound on the complex norm
    have : 1 / ‖(δ : ℂ)‖ ≤ 2 := by simpa [hnorm_ofReal] using hone_div_abs_le_two
    -- rewrite ‖1/(δ:ℂ)‖ via hnorm_div
    have hnorm_div' : ‖(1 / (δ : ℂ))‖ = 1 / ‖(δ : ℂ)‖ := by
      simp
    simpa [hnorm_div'] using this
  -- Combine: first use the triangle inequality, then the Z0 bound, then the bound on ‖1/δ‖
  have h_real_axis_bound : ‖logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 := by
    have h1 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + ‖(1 / (δ : ℂ))‖ :=
      le_trans h_tri (add_le_add_left hZ0 _)
    have h2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 :=
      le_trans h1 (add_le_add_right h_norm_div_le_two _)
    simpa [norm_neg] using h2
  -- Rewrite ((1:ℂ)+δ) as σ
  have hσ_real : (1 : ℝ) + δ = σ := by
    simp [δ, sub_eq_add_neg, add_left_comm]
  have hσ_eq : (1 : ℂ) + δ = (σ : ℂ) := by
    have : ((1 + δ : ℝ) : ℂ) = (σ : ℂ) := by simpa using congrArg Complex.ofReal hσ_real
    simpa [Complex.ofReal_add] using this
  have hR_bound : ‖deriv riemannZeta σ / riemannZeta σ‖ ≤ C0 + 2 := by
    -- logDerivZeta equals deriv ζ / ζ by definition
    simpa [logDerivZeta, hσ_eq] using h_real_axis_bound
  -- Conclude using the center bound
  exact le_trans h_center hR_bound

theorem thm_final_result :
  ∃ A : ℝ, A > 0 ∧ A < 1 ∧
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 1 - A / Real.log (|t| + 2) →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C * (Real.log (|t|)) ^ 2 := by
  -- Apply lem_logDerivZetalogt2 and lem_logDerivZetalogt32 as suggested by informal proof
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := lem_logDerivZetalogt0
  obtain ⟨C₃₂, hC₃₂_pos, hC₃₂⟩ := lem_logDerivZetalogt32

  -- Use A = zerofree_constant / 20 (this matches deltaz_t definition)
  use zerofree_constant / 20

  constructor
  · -- Prove A > 0
    apply div_pos zerofree_constant_pos
    norm_num

  constructor
  · -- Prove A < 1
    rw [div_lt_one (by norm_num : (0 : ℝ) < 20)]
    -- Need to show zerofree_constant < 20
    have h1 : zerofree_constant < 1 := zerofree_constant_lt_one
    linarith

  -- Use C = max C₀ C₃₂
  use max C₀ C₃₂

  constructor
  · -- Prove C > 1
    exact lt_max_of_lt_left hC₀_pos

  · -- Main bound
    intro t ht σ hσ

    -- Key insight: A / Real.log (|t| + 2) = deltaz_t t when A = zerofree_constant / 20
    have h_eq : zerofree_constant / 20 / Real.log (|t| + 2) = deltaz_t t := by
      unfold deltaz_t deltaz
      simp

    -- So the condition becomes σ ≥ 1 - deltaz_t t
    have hσ' : σ ≥ 1 - deltaz_t t := by
      rw [← h_eq]
      exact hσ

    by_cases! h : σ ≥ 3/2
    · -- Case σ ≥ 3/2: use lem_logDerivZetalogt32
      have bound := hC₃₂ t ht σ h
      have hC_le : C₃₂ ≤ max C₀ C₃₂ := le_max_right _ _
      -- Need to show C₃₂ ≤ C₃₂ * (Real.log (|t|))^2
      have hlog_ge_one : 1 ≤ Real.log (|t|) := by
        have h_ge : Real.exp 1 ≤ |t| := by
          -- Since |t| > 3 and e < 3, we have e < |t|
          have he_lt_3 : Real.exp 1 < 3 := by linarith[Real.exp_one_lt_d9]
          linarith [ht, abs_nonneg t]
        exact (Real.le_log_iff_exp_le (by linarith [abs_nonneg t])).2 h_ge
      have h_one_le_sq : 1 ≤ (Real.log (|t|)) ^ 2 := by
        have h_sq : (Real.log (|t|)) ^ 2 = Real.log (|t|) * Real.log (|t|) := by
          rw [pow_two]
        rw [h_sq]
        have h_mul : 1 * 1 ≤ Real.log (|t|) * Real.log (|t|) :=
          mul_self_le_mul_self (zero_le_one) hlog_ge_one
        simpa using h_mul
      have h_pos : 0 < C₃₂ := lt_trans zero_lt_one hC₃₂_pos
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₃₂ := bound
        _ = C₃₂ * 1 := by rw [mul_one]
        _ ≤ C₃₂ * (Real.log (|t|)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left h_one_le_sq (le_of_lt h_pos)
        _ ≤ max C₀ C₃₂ * (Real.log (|t|)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

    · -- Case σ < 3/2: use lem_logDerivZetalogt0
      have h_conditions : 1 - deltaz_t t ≤ σ ∧ σ ≤ 3/2 ∧ t = t := by
        exact ⟨hσ', le_of_lt h, rfl⟩
      have bound := hC₀ t ht ⟨σ, t⟩ h_conditions
      have hC_le : C₀ ≤ max C₀ C₃₂ := le_max_left _ _
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₀ * Real.log |t| ^ 2 := bound
        _ ≤ max C₀ C₃₂ * Real.log |t| ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)


private lemma sigma_gt_one_sub_div {c A L L' σ : ℝ} (hc : 0 < c) (hA_le : A ≤ c / 2)
    (hL : 0 < L) (hL' : 0 < L') (hLL' : L' < 2 * L) (hσ : 1 - A / L ≤ σ) :
    1 - c / L' < σ := by
  have h_inv_comp : 1 / (2 * L) < 1 / L' := one_div_lt_one_div_of_lt hL' hLL'
  have hstep2 : (c / 2) / L < c / L' := by
    have := mul_lt_mul_of_pos_left h_inv_comp hc
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hstep1 : A / L ≤ (c / 2) / L := by
    have := div_le_div_of_nonneg_right hA_le (le_of_lt hL)
    simpa [div_eq_mul_inv] using this
  have hstrict_div : A / L < c / L' := lt_of_le_of_lt hstep1 hstep2
  have hneg' : -(c / L') < -(A / L) := by simpa [neg_div] using neg_lt_neg hstrict_div
  have hsub : 1 - c / L' < 1 - A / L := by simpa [sub_eq_add_neg] using add_lt_add_right hneg' 1
  exact hsub.trans_le hσ

lemma ZetaZeroFree_p :
    ∃ (A : ℝ) (_ : A ∈ Set.Ioc 0 (1 / 2)),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Set.Ico (1 - A / Real.log |t| ^ 1) 1),
    riemannZeta (σ + t * Complex.I) ≠ 0 := by
  -- Global zero location bound: zeros lie to the left of 1 - c / log(|Im|+2)
  obtain ⟨c, hc_pos, hc_lt_one, hbound⟩ := zerofree
  -- Choose a universal constant A small enough
  let A0 : ℝ := min (1 / 2 : ℝ) (c / 2)
  let A : ℝ := min A0 ((1 / 4 : ℝ) * Real.log 3)
  have hA_pos : 0 < A := by
    have h1 : 0 < (1 / 2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc_pos this
    have hA0pos : 0 < A0 := lt_min_iff.mpr ⟨h1, h2⟩
    have hlog3pos : 0 < Real.log (3 : ℝ) :=
      (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 3)).2 (by norm_num)
    have h3 : 0 < (1 / 4 : ℝ) * Real.log 3 := by
      exact mul_pos (by norm_num) hlog3pos
    exact lt_min_iff.mpr ⟨hA0pos, h3⟩
  have hA_le_half : A ≤ 1/2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_left _ _)
  have hA_le_c2 : A ≤ c / 2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_right _ _)
  have hA_le_log3quarter : A ≤ (1 / 4 : ℝ) * Real.log 3 := min_le_right _ _
  refine ⟨A, ?_, ?_⟩
  · exact ⟨hA_pos, hA_le_half⟩
  · intro σ t htgt3 hσI hzero
    -- Notation for logs
    set L := Real.log |t| with hLdef
    set Lp := Real.log (|t| + 2) with hLpdef
    have hpos_abs : 0 ≤ |t| := abs_nonneg t
    have hLpos : 0 < L := (Real.log_pos_iff hpos_abs).2 (lt_trans (by norm_num) htgt3)
    have hLp_pos_arg : 0 < |t| + 2 := by linarith
    have hLp_pos : 0 < Lp := (Real.log_pos_iff (le_of_lt hLp_pos_arg)).2 (by linarith)
    -- From |t| > 3, we have log 3 ≤ L
    have hlog3_le_L : Real.log 3 ≤ L := by
      have h3pos : 0 < (3 : ℝ) := by norm_num
      have : (3 : ℝ) ≤ |t| := le_of_lt htgt3
      simpa [hLdef] using Real.log_le_log h3pos this
    -- Hence ((1/4) log 3)/L ≤ 1/4
    have hquarter_ratio_le : ((1 / 4 : ℝ) * Real.log 3) / L ≤ (1 / 4 : ℝ) := by
      have h := div_le_div_of_nonneg_right hlog3_le_L (le_of_lt hLpos)
      have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/4)
      have hne : L ≠ 0 := ne_of_gt hLpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne] using h'
    -- Therefore A/L ≤ 1/4
    have hA_over_le_quarter : A / L ≤ (1 / 4 : ℝ) := by
      have := div_le_div_of_nonneg_right hA_le_log3quarter (le_of_lt hLpos)
      exact this.trans hquarter_ratio_le
    -- Deduce σ ≥ 3/4 > 0 and σ < 1
    have hlow : 1 - A / L ≤ σ := by simpa [hLdef, pow_one] using hσI.1
    have hσ_ge_34 : (3 / 4 : ℝ) ≤ σ := by
      have : (3 / 4 : ℝ) ≤ 1 - A / L := by linarith
      exact this.trans hlow
    have hσ_pos : 0 < σ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3/4 : ℝ)) hσ_ge_34
    have hσ_lt_one : σ < 1 := hσI.2
    -- Show Lp < 2L
    have hlog_lt : Lp < 2 * L := by
      rw [hLpdef, hLdef]
      exact log_add_two_lt_two_mul_log htgt3
    -- Hence σ > 1 - c/Lp by the interval's lower bound
    have hσ_gt : 1 - c / Lp < σ :=
      sigma_gt_one_sub_div hc_pos hA_le_c2 hLpos hLp_pos hlog_lt hlow
    -- Contradiction with zero location bound
    let s : ℂ := Complex.mk σ t
    have hs_zero : riemannZeta s = 0 := by simpa [s, Complex.mk_eq_add_mul_I] using hzero
    have hs_in_zeroZ : s ∈ zeroZ := by simpa [zeroZ] using hs_zero
    have hpre : s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1 := by
      refine ⟨hs_in_zeroZ, ?_, ?_⟩
      · simpa [s] using hσ_pos
      · simpa [s] using hσ_lt_one
    have him_bound : 2 < |s.im| := by
      have : 2 < |t| := lt_trans (by norm_num) htgt3
      simpa [s] using this
    have hbound_applied : s.re ≤ 1 - c / Real.log (|s.im| + 2) := hbound s hpre him_bound
    have hle : σ ≤ 1 - c / Lp := by simpa [s, hLpdef] using hbound_applied
    have hcontr : σ < σ := lt_of_le_of_lt hle hσ_gt
    exact (lt_irrefl _ : ¬ σ < σ) hcontr

open Set Function Filter Complex Real
lemma LogDerivZetaBndUnif2 :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 1)), ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      C * Real.log |t| ^ 2 := by
  classical
  obtain ⟨c, hc, hc2, K, hK, hfinal⟩ := thm_final_result
  -- Choose constants
  let A : ℝ := min (1/2 : ℝ) (c / 2)
  have hApos : 0 < A := by
    have h1 : 0 < (1/2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc this
    exact (lt_min_iff).2 ⟨h1, h2⟩
  have hAle : A ≤ (1/2 : ℝ) := min_le_left _ _
  have hA_in : A ∈ Ioc 0 (1/2) := ⟨hApos, hAle⟩
  let C : ℝ := K
  have hCpos : 0 < C := by
    have hKpos : 0 < K := lt_trans (by norm_num : (0 : ℝ) < 1) hK
    exact hKpos
  refine ⟨A, hA_in, C, hCpos, ?_⟩
  intro σ t htgt3 hσI
  -- Notation for logs
  let x := |t|
  have hxpos : 0 ≤ x := abs_nonneg t
  have hxgt3 : 3 < x := htgt3
  let L := Real.log x
  let L' := Real.log (x + 2)
  have hLpos : 0 < L := (Real.log_pos_iff hxpos).2 (lt_trans (by norm_num) hxgt3)
  have hL'pos : 0 < L' :=
    (Real.log_pos_iff (by linarith : 0 ≤ x + 2)).2 (by linarith [hxpos, hxgt3])
  -- From the Ici-bound we have σ ≥ 1 - A / L
  have hσ_ge : 1 - A / L ≤ σ := by simpa [pow_one, L, x] using hσI
  -- Show L' < 2L
  have hL'_lt_2L : L' < 2 * L := log_add_two_lt_two_mul_log hxgt3
  -- Build strict inequality σ > 1 - c/L'
  have hA_le_c2 : A ≤ c / 2 := min_le_right _ _
  have hσ_gt : σ > 1 - c / L' :=
    sigma_gt_one_sub_div hc hA_le_c2 hLpos hL'pos hL'_lt_2L hσ_ge
  -- Apply the global bound from thm_final_result
  have hmain' : ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      K * (Real.log |t|) ^ 2 := by
    have h_eq : σ + t * Complex.I = Complex.mk σ t := by
      rw [Complex.mk_eq_add_mul_I]
    rw [h_eq]
    have hσ_ge_required : σ ≥ 1 - c / Real.log (|t| + 2) := by
      have h_abs_eq : |t| = |t| := by simp
      rw [h_abs_eq]
      exact le_of_lt hσ_gt
    exact hfinal t htgt3 σ hσ_ge_required
  -- The bound is already what we need since C = K
  simpa [C, L, x] using hmain'

#print axioms ZetaZeroFree_p
#print axioms LogDerivZetaBndUnif2
