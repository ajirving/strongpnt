import PrimeNumberTheoremAnd.MediumPNT
import StrongPNT.ZetaZeroFree

set_option lang.lemmaCmd true

open Set Function Filter Complex Real


local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ
local notation "ψ" => ChebyshevPsi

lemma LogDerivZetaBoundedAndHolo : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound 1 2 A C
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
    convert zeta_bnd2 σ t ht (by simpa [pow_one] using hσ')
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

/-- *** Prime Number Theorem (Strong_ Strength) *** The `ChebyshevPsi` function is asymptotic to `x`. -/
theorem Strong_PNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := by
  convert GenStrengthPNT _ (by norm_num : 0 < (1 : ℝ)) (by norm_num : 0 < (2 : ℝ))
  · norm_num
  unfold LogDerivZetaBoundedAndHoloGenProp
  convert LogDerivZetaBoundedAndHolo
  simp

#print axioms Strong_PNT

