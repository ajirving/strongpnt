import StrongPNT.PNT4_ZeroFreeRegion
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Group.Basic
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.MellinCalculus
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Order.Group.Lattice
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Bound
import Mathlib.NumberTheory.LSeries.PrimesInAP
import PrimeNumberTheoremAnd.Fourier
import PrimeNumberTheoremAnd.ZetaBounds

set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics
local notation (name := riemannzeta') "ζ" => riemannZeta
local notation (name := derivriemannzeta') "ζ'" => deriv riemannZeta

local notation "I" => Complex.I

/-%%
\begin{lemma}[LogDerivZetaHolcLargeT]\label{LogDerivZetaHolcLargeT}\lean{LogDerivZetaHolcLargeT}\leanok
There is an $A>0$ so that for all $T>3$, the function
$
\frac {\zeta'}{\zeta}(s)
$
is holomorphic on $\{1-A/\log^9 T \le \Re s \le 2, |\Im s|\le T \}\setminus\{1\}$.
\end{lemma}
%%-/

theorem LogDerivZetaHolcLargeT' :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree_p
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ 1)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact notMem_diff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ 1 := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1

  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ 1 := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ 1 := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ 1)) / Real.log 3 ^ 1:= by
        gcongr
        apply min_le_right
      _ = _ := by field_simp

/-%%
\begin{proof}\uses{ZetaZeroFree}\leanok
The derivative of $\zeta$ is holomorphic away from $s=1$; the denominator $\zeta(s)$ is nonzero
in this range by Lemma \ref{ZetaZeroFree}.
\end{proof}
%%-/
