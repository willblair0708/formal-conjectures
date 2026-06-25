/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1150

*Reference:* [erdosproblems.com/1150](https://www.erdosproblems.com/1150)
-/

open scoped Polynomial

namespace Erdos1150

/--
Is there some constant $c > 0$ such that, for all large enough $n$ and all polynomials $P$ of
degree $n$ with coefficients in $\{-1, 1\}$,
$$\max_{|z|=1} |P(z)| > (1 + c) \sqrt{n}?$$
-/
@[category research open, AMS 12 30]
theorem erdos_1150 :
    answer(sorry) ↔ ∃ c > 0, ∀ᶠ n in Filter.atTop,
      ∀ P : ℂ[X],  (∀ i ≤ P.natDegree, P.coeff i = - 1 ∨ P.coeff i = 1) → P.natDegree = n →
        ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ > (1 + c) * Real.sqrt n := by
  sorry

/--
The trivial lower bound from Parseval's identity: for any polynomial $P$ of degree $n$ with
coefficients in $\{-1, 1\}$, we have $\max_{|z|=1} |P(z)| \geq \sqrt{n+1}$.

This follows from Parseval's identity:
$$\frac{1}{2\pi} \int_0^{2\pi} |P(e^{i\theta})|^2 d\theta = \sum_{k=0}^{n} |a_k|^2 = n+1$$
since each $|a_k|^2 = 1$.
-/
@[category textbook, AMS 12 30]
theorem erdos_1150.variants.parseval_lower_bound (P : ℂ[X]) (n : ℕ)
    (hcoeff : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1)
    (hdeg : P.natDegree = n) :
    ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ ≥ Real.sqrt (n + 1) := by
  classical
  -- Set `N = n + 1` and `ω` a primitive `N`-th root of unity (norm `1`).
  set N := n + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos n
  have hdegN : P.natDegree < N := by rw [hdeg]; omega
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have hω0 : ω ≠ 0 := hω.ne_zero hN.ne'
  -- Root-of-unity orthogonality: `∑ⱼ wʲ = N` if `w = 1` and `0` otherwise.
  have orth : ∀ w : ℂ, w ^ N = 1 → ∑ j ∈ Finset.range N, w ^ j = if w = 1 then (N : ℂ) else 0 := by
    intro w hw
    split_ifs with h
    · subst h; simp
    · rw [geom_sum_eq h N, hw, sub_self, zero_div]
  -- Since `‖ω‖ = 1`, conjugation is inversion.
  have hconj : (starRingEnd ℂ) ω = ω⁻¹ := by
    have h1 : Complex.normSq ω = 1 := by rw [Complex.normSq_eq_norm_sq, hωnorm]; norm_num
    field_simp
    rw [mul_comm, Complex.mul_conj]; exact_mod_cast h1
  -- Discrete Parseval: `∑ⱼ |P(ωʲ)|² = N · ∑ₖ |aₖ|²` over the `N`-th roots of unity.
  have hpars : (∑ j ∈ Finset.range N, (Complex.normSq (P.eval (ω ^ j)) : ℂ)) =
      N * ∑ k ∈ Finset.range N, (Complex.normSq (P.coeff k) : ℂ) := by
    -- Expand each `|P(ωʲ)|²` as a double sum via `normSq z = conj z * z`.
    have key : ∀ j, (Complex.normSq (P.eval (ω ^ j)) : ℂ) =
        ∑ l ∈ Finset.range N, ∑ k ∈ Finset.range N,
          P.coeff k * (starRingEnd ℂ) (P.coeff l) * (ω ^ k * (ω⁻¹) ^ l) ^ j := by
      intro j
      rw [Complex.normSq_eq_conj_mul_self, Polynomial.eval_eq_sum_range' hdegN, map_sum,
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_pow, map_pow, hconj, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
      ring
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_comm,
      Finset.sum_congr rfl fun l _ => Finset.sum_comm,
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
        (Finset.mul_sum (Finset.range N) (fun j => (ω ^ k * (ω⁻¹) ^ l) ^ j)
          (P.coeff k * (starRingEnd ℂ) (P.coeff l))).symm]
    -- The inner geometric sum is nonzero only on the diagonal `k = l`.
    have hwN : ∀ k l : ℕ, (ω ^ k * (ω⁻¹) ^ l) ^ N = 1 := by
      intro k l
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm l N, pow_mul, pow_mul,
        hω.pow_eq_one, inv_pow, hω.pow_eq_one]
      simp
    rw [Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [orth _ (hwN k l)]]
    have hcond : ∀ k ∈ Finset.range N, ∀ l ∈ Finset.range N, (ω ^ k * (ω⁻¹) ^ l = 1) ↔ k = l := by
      intro k hk l hl
      rw [Finset.mem_range] at hk hl
      rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero l hω0)]
      exact ⟨fun h => hω.pow_inj hk hl h, fun h => by rw [h]⟩
    rw [Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun k hk => by
      rw [if_congr (hcond k hk l hl) rfl rfl], Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_eq_single l]
    · rw [if_pos rfl, mul_comm (P.coeff l), Complex.normSq_eq_conj_mul_self]; ring
    · intro k _ hkl; rw [if_neg hkl]; ring
    · intro h; exact absurd hl h
  -- Each `|aₖ|² = 1` since the coefficients lie in `{-1, 1}`, so `∑ₖ |aₖ|² = N`.
  have hcoeffsum : (∑ k ∈ Finset.range N, (Complex.normSq (P.coeff k) : ℂ)) = N := by
    rw [Finset.sum_congr rfl (fun k hk => by
      rw [Finset.mem_range] at hk
      have hkle : k ≤ P.natDegree := by rw [hdeg]; omega
      rcases hcoeff k hkle with h | h <;> rw [h] <;> simp [Complex.normSq] :
      ∀ k ∈ Finset.range N, (Complex.normSq (P.coeff k) : ℂ) = 1)]
    simp
  rw [hcoeffsum] at hpars
  -- Hence the average of `|P(ωʲ)|²` over the `N` roots equals `N`.
  have hparsR : (∑ j ∈ Finset.range N, Complex.normSq (P.eval (ω ^ j))) = (N : ℝ) * N := by
    have h := hpars; push_cast at h ⊢; exact_mod_cast h
  -- Some root `ωʲ` attains at least the average: `|P(ωʲ)|² ≥ N`.
  obtain ⟨j, -, hjle⟩ : ∃ j ∈ Finset.range N, (N : ℝ) ≤ Complex.normSq (P.eval (ω ^ j)) := by
    apply Finset.exists_le_of_sum_le (by rw [Finset.nonempty_range_iff]; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hparsR]
  have hmem : (ω ^ j) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_pow, hωnorm, one_pow]
  -- So `‖P(ωʲ)‖ ≥ √N = √(n+1)`.
  have hsqrtle : Real.sqrt (n + 1) ≤ ‖P.eval (ω ^ j)‖ := by
    rw [show ((n : ℝ) + 1) = (N : ℝ) by rw [hNdef]; push_cast; ring,
      show ‖P.eval (ω ^ j)‖ = Real.sqrt (Complex.normSq (P.eval (ω ^ j))) by
        rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_le_sqrt hjle
  -- The supremum over the (compact) sphere dominates this single value.
  have hbdd : BddAbove (Set.range fun z : Metric.sphere (0 : ℂ) 1 => ‖P.eval (z : ℂ)‖) := by
    have hcont : Continuous fun z : Metric.sphere (0 : ℂ) 1 => ‖P.eval (z : ℂ)‖ :=
      continuous_norm.comp (P.continuous.comp continuous_subtype_val)
    have := (CompactSpace.isCompact_univ.image hcont).bddAbove
    rwa [Set.image_univ] at this
  exact le_trans hsqrtle (le_ciSup hbdd ⟨ω ^ j, hmem⟩)

end Erdos1150
