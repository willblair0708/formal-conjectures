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
# Erdős Problem 947

*Reference:* [erdosproblems.com/947](https://www.erdosproblems.com/947)
-/

namespace Erdos947

/-- An *exact covering system* is a finite list of congruence classes `aᵢ (mod nᵢ)`, with
`0 ≤ aᵢ < nᵢ`, such that every integer satisfies exactly one of them. -/
def IsExactCoveringSystem (l : List (ℤ × ℕ)) : Prop :=
  (∀ p ∈ l, 0 ≤ p.1 ∧ p.1 < p.2) ∧
  (∀ m : ℤ, ∃! i : Fin l.length, m ≡ (l.get i).1 [ZMOD (l.get i).2])

/--
Is there an exact covering system with distinct moduli - that is, a finite collection of
congruence classes $a_i\pmod{n_i}$ with distinct $n_i$ such that every integer satisfies
exactly one of these congruence classes?

This is false: no such system exists with at least two classes. Proved independently by
Mirsky and Newman, and by Davenport and Rado.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos947.lean"]
theorem erdos_947 : answer(False) ↔
    ∃ l : List (ℤ × ℕ), IsExactCoveringSystem l ∧
      l.Pairwise (fun p q => p.2 ≠ q.2) ∧ 2 ≤ l.length := by
  sorry

end Erdos947
