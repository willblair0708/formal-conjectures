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

/-! Auxiliary p-adic lifting lemmas for Erdős Problem 686. -/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos686Padic

abbrev Vec3 := Fin 3 → ℤ
abbrev End3 := Module.End ℤ Vec3

private def affineEnd (c : ℤ) (B : End3) : End3 :=
  LinearMap.id + c • B

private def affineStep (c : ℤ) (B : End3) : Vec3 → Vec3 :=
  fun x => affineEnd c B x

private def remainder (c : ℤ) (B : End3) : ℕ → End3
  | 0 => 0
  | n + 1 =>
      remainder c B n + n • (B.comp B) + c • (B.comp (remainder c B n))

private lemma iterate_affineStep_apply (c : ℤ) (B : End3) (n : ℕ) (x : Vec3) :
    (affineStep c B)^[n] x =
      x + ((n : ℤ) * c) • B x + c ^ 2 • (remainder c B n) x := by
  induction n generalizing x with
  | zero =>
      simp [affineStep, affineEnd, remainder]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      ext i
      simp [affineStep, affineEnd, remainder]
      ring

end Erdos686Padic
