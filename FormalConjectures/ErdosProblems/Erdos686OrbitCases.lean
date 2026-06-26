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

import FormalConjectures.ErdosProblems.Erdos686Orbit

/-! The remaining modular orbit certificates for Erdős Problem 686. -/

namespace Erdos686Orbit

open Matrix
open Erdos686Padic

def c2 : Mat ℤ :=
  !![-4, 6, -2;
      -1, -4, 6;
      3, -1, -4]

def c3 : Mat ℤ :=
  !![0, -2, 2;
      1, 0, -2;
      -1, 1, 0]

def c5 : Mat ℤ :=
  !![0, -32, 40;
      20, 0, -32;
      -16, 20, 0]

def c7 : Mat ℤ :=
  !![-7280, 41382, -40582;
      -20291, -7280, 41382;
      20691, -20291, -7280]

lemma base_block (p L : ℕ) (C : Mat ℤ)
    (hpow : (nMat ℤ) ^ L = 1 + (p : ℤ) • C) :
    (step ℤ)^[L] = affineStep p C.mulVecLin := by
  funext x
  rw [iterate_step, hpow]
  ext i
  simp [step, affineStep, affineEnd]

lemma full_block (p L : ℕ) (C : Mat ℤ)
    (hpow : (nMat ℤ) ^ L = 1 + (p : ℤ) • C) :
    (step ℤ)^[L * p] = affineStep ((p : ℤ) ^ 2) (liftB p C.mulVecLin) := by
  rw [Function.iterate_mul, base_block p L C hpow, first_prime_block]

lemma modular_middle_zero (m k : ℕ) (z : Vec ℤ)
    (hz : ((step ℤ)^[k] z) 1 = 0) :
    ((((nMat (ZMod m)) ^ k) *ᵥ castVec m z) 1 = 0) := by
  have h := congrArg (fun x => x 1) (cast_iterate_step m k z)
  rw [hz, iterate_step] at h
  simpa [castVec] using h.symm

lemma exact_root_of_mod
    (p L r k : ℕ) (hp : p.Prime) (C : Mat ℤ)
    (hpow : (nMat ℤ) ^ L = 1 + (p : ℤ) • C)
    (z : Vec ℤ) (hrlt : r < L * p) (hmod : k % (L * p) = r)
    (hrzero : ((step ℤ)^[r] z) 1 = 0)
    (hderiv : ¬ (p : ℤ) ∣ (liftB p C.mulVecLin ((step ℤ)^[r] z)) 1)
    (hz : ((step ℤ)^[k] z) 1 = 0) :
    k = r := by
  let q := k / (L * p)
  have hk : k = (L * p) * q + r := by
    have h := Nat.mod_add_div k (L * p)
    dsimp [q]
    omega
  have hzblock :
      ((affineStep ((p : ℤ) ^ 2) (liftB p C.mulVecLin))^[q]
        ((step ℤ)^[r] z)) 1 = 0 := by
    rw [hk, Function.iterate_add_apply, Function.iterate_mul,
      full_block p L C hpow] at hz
    exact hz
  have hq := zero_of_affine_iterate_zero p hp ((step ℤ)^[r] z) 1 hrzero
    q 1 (by norm_num) (liftB p C.mulVecLin) hderiv hzblock
  rw [hk, hq]
  simp

def z1 : Vec ℤ := vec (-1) 0 0

def z2 : Vec ℤ := vec 0 (-1) 0

lemma nMat_pow_3 : (nMat ℤ) ^ 3 = 1 + (3 : ℤ) • c3 := by decide
lemma nMat_pow_4 : (nMat ℤ) ^ 4 = 1 + (2 : ℤ) • c2 := by decide

lemma period_1 : (nMat (ZMod (3 ^ 2))) ^ 9 = 1 := by decide
lemma period_2 : (nMat (ZMod (2 ^ 2))) ^ 8 = 1 := by decide

set_option maxRecDepth 100000 in
lemma roots_1 : ∀ r : Fin 9,
    (((((nMat (ZMod (3 ^ 2))) ^ (r : ℕ)) *ᵥ castVec 9 z1) 1 = 0) ↔ r = 0) := by
  decide

set_option maxRecDepth 100000 in
lemma roots_2 : ∀ r : Fin 8,
    (((nMat (ZMod (2 ^ 2))) ^ (r : ℕ)) *ᵥ castVec 4 z2) 1 ≠ 0 := by
  decide

lemma deriv_1 : ¬ (3 : ℤ) ∣ (liftB 3 c3.mulVecLin z1) 1 := by
  norm_num [liftB, remainder, c3, z1, vec, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem orbit_1 (k : ℕ) (hz : ((step ℤ)^[k] z1) 1 = 0) : k = 0 := by
  have hzmod := modular_middle_zero 9 k z1 hz
  rw [pow_eq_pow_mod (nMat (ZMod 9)) 9 k (by norm_num) period_1] at hzmod
  let r : Fin 9 := ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩
  have hr : r = 0 := (roots_1 r).mp hzmod
  have hmod : k % 9 = 0 := congrArg Fin.val hr
  exact exact_root_of_mod 3 3 0 k (by norm_num) c3 nMat_pow_3 z1
    (by norm_num) hmod (by simp [z1, vec]) deriv_1 hz

theorem orbit_2_absurd (k : ℕ) (hz : ((step ℤ)^[k] z2) 1 = 0) : False := by
  have hzmod := modular_middle_zero 4 k z2 hz
  rw [pow_eq_pow_mod (nMat (ZMod 4)) 8 k (by norm_num) period_2] at hzmod
  let r : Fin 8 := ⟨k % 8, Nat.mod_lt _ (by norm_num)⟩
  exact (roots_2 r) hzmod

end Erdos686Orbit
