/-
Copyright 2025 The Formal Conjectures Authors.

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

namespace Erdos686FourThree

private abbrev Vec3 := Fin 3 → ℤ

private def vec (a b c : ℤ) : Vec3 := ![a, b, c]

private def stepN (x : Vec3) : Vec3 :=
  vec (-x 0 + 2 * x 2) (x 0 - x 1) (x 1 - x 2)

private def stepM (x : Vec3) : Vec3 :=
  vec (x 0 + 2 * x 1 + 2 * x 2) (x 0 + x 1 + 2 * x 2) (x 0 + x 1 + x 2)

private def norm (x : Vec3) : ℤ :=
  x 0 ^ 3 + 2 * x 1 ^ 3 + 4 * x 2 ^ 3 - 6 * x 0 * x 1 * x 2

private noncomputable def rho : ℝ := (2 : ℝ) ^ ((3 : ℝ)⁻¹)

private noncomputable def eval (x : Vec3) : ℝ :=
  x 0 + x 1 * rho + x 2 * rho ^ 2

private noncomputable def eta : ℝ := 1 + rho + rho ^ 2

private lemma rho_cube : rho ^ 3 = 2 := by
  rw [rho]
  simpa using Real.rpow_inv_natCast_pow (x := (2 : ℝ)) (n := 3) (by positivity) (by norm_num)

private lemma rho_pos : 0 < rho := by
  exact Real.rpow_pos_of_pos (by norm_num) _

private lemma rho_gt_one : 1 < rho := by
  rw [rho]
  have h : (0 : ℝ) < (3 : ℝ)⁻¹ := by positivity
  simpa using Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2) h

private lemma rho_lt_thirteen_tenths : rho < (13 : ℝ) / 10 := by
  by_contra h
  have hle : (13 : ℝ) / 10 ≤ rho := le_of_not_gt h
  have hnonneg : 0 ≤ rho := rho_pos.le
  have hmul : ((13 : ℝ) / 10) ^ 3 ≤ rho ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num) hle 3
  rw [rho_cube] at hmul
  norm_num at hmul

private lemma eta_gt_one : 1 < eta := by
  rw [eta]
  nlinarith [rho_pos, sq_nonneg rho]

private lemma eta_lt_four : eta < 4 := by
  rw [eta]
  have hs : rho ^ 2 < ((13 : ℝ) / 10) ^ 2 := by
    nlinarith [rho_pos, rho_lt_thirteen_tenths]
  nlinarith [rho_lt_thirteen_tenths]

private lemma delta_mul_eta : (rho - 1) * eta = 1 := by
  rw [eta]
  nlinarith [rho_cube]

private lemma stepM_stepN (x : Vec3) : stepM (stepN x) = x := by
  funext i
  fin_cases i <;> simp [stepM, stepN, vec] <;> ring

private lemma stepN_stepM (x : Vec3) : stepN (stepM x) = x := by
  funext i
  fin_cases i <;> simp [stepM, stepN, vec] <;> ring

private lemma norm_stepN (x : Vec3) : norm (stepN x) = norm x := by
  simp [norm, stepN, vec]
  ring

private lemma norm_stepM (x : Vec3) : norm (stepM x) = norm x := by
  simp [norm, stepM, vec]
  ring

private lemma eval_stepN (x : Vec3) : eval (stepN x) = (rho - 1) * eval x := by
  simp [eval, stepN, vec]
  nlinarith [rho_cube]

private lemma eval_stepM (x : Vec3) : eval (stepM x) = eta * eval x := by
  simp [eval, stepM, vec, eta]
  nlinarith [rho_cube]

end Erdos686FourThree
