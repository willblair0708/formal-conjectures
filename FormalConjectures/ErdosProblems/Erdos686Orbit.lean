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

import FormalConjectures.ErdosProblems.Erdos686Padic

/-! Finite modular orbit certificates for Erdős Problem 686. -/

namespace Erdos686Orbit

open Matrix
open Erdos686Padic

abbrev Idx := Fin 3
abbrev Vec (R : Type*) := Idx → R
abbrev Mat (R : Type*) := Matrix Idx Idx R

def vec {R : Type*} [Zero R] (a b c : R) : Vec R := ![a, b, c]

def nMat (R : Type*) [Ring R] : Mat R :=
  !![-1, 0, 2;
      1, -1, 0;
      0, 1, -1]

def step (R : Type*) [CommRing R] (x : Vec R) : Vec R :=
  nMat R *ᵥ x

lemma iterate_step (R : Type*) [CommRing R] (k : ℕ) (x : Vec R) :
    (step R)^[k] x = (nMat R) ^ k *ᵥ x := by
  induction k generalizing x with
  | zero => simp [step]
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih]
      rw [← Matrix.mulVec_mulVec, ← pow_succ]

def castVec (m : ℕ) (x : Vec ℤ) : Vec (ZMod m) :=
  fun i => x i

lemma cast_step (m : ℕ) (x : Vec ℤ) :
    castVec m (step ℤ x) = step (ZMod m) (castVec m x) := by
  ext i
  fin_cases i <;>
    simp [castVec, step, nMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma cast_iterate_step (m k : ℕ) (x : Vec ℤ) :
    castVec m ((step ℤ)^[k] x) = (step (ZMod m))^[k] (castVec m x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, cast_step, ih]

lemma pow_eq_pow_mod {R : Type*} [Monoid R] (A : R) (L k : ℕ)
    (hL : 0 < L) (hperiod : A ^ L = 1) :
    A ^ k = A ^ (k % L) := by
  calc
    A ^ k = A ^ (k % L + L * (k / L)) := by rw [Nat.mod_add_div]
    _ = A ^ (k % L) * A ^ (L * (k / L)) := by rw [pow_add]
    _ = A ^ (k % L) * (A ^ L) ^ (k / L) := by rw [pow_mul]
    _ = A ^ (k % L) := by rw [hperiod, one_pow, mul_one]

def c29 : Mat ℤ :=
  !![-6251293847810685364, 621243982110958014, 9140592059994905392;
      4570296029997452696, -6251293847810685364, 621243982110958014;
      310621991055479007, 4570296029997452696, -6251293847810685364]

def z60 : Vec ℤ := vec (-4) 0 1

set_option maxHeartbeats 1000000 in
lemma nMat_pow_70 : (nMat ℤ) ^ 70 = 1 + (29 : ℤ) • c29 := by
  decide

lemma block_70 : (step ℤ)^[70] = affineStep 29 c29.mulVecLin := by
  funext x
  rw [iterate_step, nMat_pow_70]
  ext i
  simp [step, affineStep, affineEnd]

lemma block_2030 :
    (step ℤ)^[2030] = affineStep ((29 : ℤ) ^ 2) (liftB 29 c29.mulVecLin) := by
  rw [show 2030 = 70 * 29 by norm_num, Function.iterate_mul, block_70,
    first_prime_block]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
lemma period_60 : (nMat (ZMod (29 ^ 2))) ^ 2030 = 1 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
lemma roots_60 : ∀ r : Fin 2030,
    ((((nMat (ZMod (29 ^ 2))) ^ (r : ℕ)) *ᵥ (vec (-4) 0 1)) 1 = 0 ↔ r = 0) := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
lemma liftB_29_derivative :
    ¬ (29 : ℤ) ∣ (liftB 29 c29.mulVecLin z60) 1 := by
  norm_num [liftB, remainder, c29, z60, vec, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
theorem orbit_60 (k : ℕ) (hz : ((step ℤ)^[k] z60) 1 = 0) : k = 0 := by
  have hzmod :
      ((((nMat (ZMod (29 ^ 2))) ^ k) *ᵥ (vec (-4) 0 1)) 1 = 0) := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod (29 ^ 2))) hz
    rw [iterate_step] at hcast
    simpa [z60, vec, castVec, nMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hcast
  have hpow := pow_eq_pow_mod (nMat (ZMod (29 ^ 2))) 2030 k (by norm_num) period_60
  rw [hpow] at hzmod
  let r : Fin 2030 := ⟨k % 2030, Nat.mod_lt _ (by norm_num)⟩
  have hr : r = 0 := (roots_60 r).mp hzmod
  have hmod : k % 2030 = 0 := by
    exact congrArg Fin.val hr
  have hk : k = 2030 * (k / 2030) := by
    have h := Nat.mod_add_div k 2030
    omega
  have hzblock :
      ((affineStep ((29 : ℤ) ^ 2) (liftB 29 c29.mulVecLin))^[k / 2030] z60) 1 = 0 := by
    rw [hk, Function.iterate_mul, block_2030] at hz
    exact hz
  have hq := zero_of_affine_iterate_zero 29 (by norm_num) z60 1 (by simp [z60, vec])
    (k / 2030) 1 (by norm_num) (liftB 29 c29.mulVecLin) liftB_29_derivative hzblock
  rw [hk, hq, mul_zero]

end Erdos686Orbit
