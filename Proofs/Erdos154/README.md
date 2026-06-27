# Erdős 154 Sumset Proof

This Lean 4 project proves the $A + A$ sumset distribution statement used for
`FormalConjectures/ErdosProblems/154.lean`.

It combines:

- Wouter van Doorn and Aristotle's formalization of Lindström's residue
  distribution theorem for Sidon sets, as hosted by plby in
  `plby/lean-proofs`.
- A finite/combinatorial transfer from residue distribution of $A$ to residue
  distribution of $A + A$.

Verification:

```bash
lake exe cache get
lake build ErdosProblems.Erdos154Sumset
```

The expected axiom audit is:

```text
'Erdos154.sidon_density_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos154.erdos_154_sumset' depends on axioms: [propext, Classical.choice, Quot.sound]
```
