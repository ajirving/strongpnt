import PrimeNumberTheoremAnd.ZetaBounds
import StrongPNT.PNT3_RiemannZeta
open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta1) "ζ" => riemannZeta
local notation (name := derivriemannzeta1) "ζ'" => deriv riemannZeta

lemma Z0bound_aux :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -(ζ' / ζ) ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := by
  -- The statement is that `-(ζ'(s)/ζ(s)) - 1/(s-1)` is bounded as `s -> 1` from the right.
  -- This is a direct consequence of `riemannZetaLogDerivResidueBigO`, which states that
  -- this function is `O(1)` in a punctured neighborhood of `1`.

  -- Let `F(s) = -(ζ'(s)/ζ(s)) - 1/(s-1)`.
  let F := fun s : ℂ => -(ζ' / ζ) s - (s - 1)⁻¹

  -- From `riemannZetaLogDerivResidueBigO`, we know `F` is `O(1)` near `1`.
  have h_F_bigO : F =O[𝓝[≠] 1] (1 : ℂ → ℂ) := by
    have h_fun_eq : F = (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
      ext s
      simp only [F, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, neg_div]
    rw [h_fun_eq]
    exact riemannZetaLogDerivResidueBigO


  -- Let `u(delta) = 1 + delta`. As `delta` approaches `0` from the right, `u(delta)` approaches `1`
  -- from the right along the real axis, staying different from `1`.
  let u := fun (delta : ℝ) => (1 : ℂ) + delta
  have h_tendsto : Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (𝓝[≠] 1) := by
    -- We need to show that u(δ) tends to 1, and that for δ near 0 (and > 0), u(δ) is not 1.
    -- `𝓝[≠] 1` is the intersection of `𝓝 1` and `𝓟 {1}ᶜ`.
    -- We can prove convergence to each part of the intersection separately using `tendsto_inf`.
    apply tendsto_inf.mpr
    constructor
    · -- Part 1: Tendsto to the point `1`.
      have h_cont : Continuous u := continuous_const.add continuous_ofReal
      -- Continuity at 0 implies `Tendsto u (𝓝 0) (𝓝 (u 0))`.
      have h_tendsto_nhds : Tendsto u (𝓝 0) (𝓝 (u 0)) := h_cont.continuousAt.tendsto
      -- The limit is `u 0 = 1 + ↑0 = 1`. We simplify the expression.
      simp only [u, Complex.ofReal_zero, add_zero] at h_tendsto_nhds
      -- Now `h_tendsto_nhds` is `Tendsto u (𝓝 0) (𝓝 1)`.
      -- We want the limit over `𝓝[>] 0`, which is a sub-filter of `𝓝 0`.
      exact h_tendsto_nhds.mono_left nhdsWithin_le_nhds
    · -- Part 2: Eventually not equal to the point `1`.
      -- This is equivalent to `Tendsto u l (𝓟 {1}ᶜ)`.
      simp
      -- For any δ in `Ioi 0`, `u(δ) = 1 + δ ≠ 1`.
      filter_upwards [self_mem_nhdsWithin] with delta h_delta_pos
      simp only [u]

      refine add_ne_left.mpr ?_
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt h_delta_pos

  -- We can compose the `IsBigO` relation with the `tendsto` relation.
  have h_comp := h_F_bigO.comp_tendsto h_tendsto
  -- `h_comp` is `IsBigO (nhdsWithin 0 (Ioi 0)) (F ∘ u) ( (fun _ => 1) ∘ u )`.
  -- This is equivalent to the goal.
  convert h_comp using 1
  ext delta
  -- Unfold definitions to show the functions are the same.
  simp only [F, u, Function.comp_apply, Pi.div_apply]
  rw [inv_eq_one_div]
  aesop


lemma Z0bound :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := Z0bound_aux
