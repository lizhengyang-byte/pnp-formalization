# P vs NP — Lean 4 formalization

**This repository does NOT contain a proof of P = NP.** P vs NP is an open problem; it has
neither been proved nor refuted. Any artifact claiming otherwise is either relying on
`sorry`, on custom axioms, or on definitions that have been quietly weakened. This
repository is the honest alternative: the parts that *can* be proved, machine-checked in
Lean 4, plus a paper that explains why the open part is still open.

## What is proved

| Theorem | Lean name | Statement |
|---|---|---|
| 1 | `Complexity.PolyBounded.add` | polynomial bounds are closed under pointwise addition |
| 2 | `Complexity.P_subset_NP` | `L ∈ P → L ∈ NP` |
| 3 | `Complexity.InP.compl` | `P` is closed under complement |
| 4 | `Complexity.InP.union` | `P` is closed under union |
| 5 | `Complexity.InP.inter` | `P` is closed under intersection |
| 6 | `Complexity.InP.empty` / `Complexity.InP.univ` | the empty and universal languages are in `P` |
| 7 | `Complexity.P_subset_EXP` | `L ∈ P → L ∈ EXP` (no axioms at all) |
| 8 | `Complexity.InEXP.compl` | `EXP` is closed under complement |
| 9 | `Complexity.P_subset_coNP` | `L ∈ P → L ∈ coNP` |

All proofs are checked by Lean 4.36.0 and audited with `#print axioms`. The only axioms
they depend on are Lean's standard `propext` and `Quot.sound`. There is no `sorry`, no
`admit`, and no custom axiom anywhere in the sources.

```
$ lake env lean Audit.lean
'Complexity.P_subset_NP' depends on axioms: [propext, Quot.sound]
'Complexity.InP.compl' depends on axioms: [propext]
'Complexity.InP.union' depends on axioms: [propext, Quot.sound]
'Complexity.InP.inter' depends on axioms: [propext, Quot.sound]
'Complexity.PolyBounded.add' depends on axioms: [propext, Quot.sound]
'Complexity.InP.empty' depends on axioms: [propext, Quot.sound]
'Complexity.InP.univ' depends on axioms: [propext, Quot.sound]
'Complexity.P_subset_EXP' does not depend on any axioms
'Complexity.InEXP.compl' depends on axioms: [propext]
'Complexity.P_subset_coNP' depends on axioms: [propext, Quot.sound]
```

## Model

Complexity classes are defined over an abstract machine model, which keeps the
formalization portable: a machine is a decider plus a step counter, and a polynomial
bound is `∃ k c, ∀ n, f n ≤ c * (n + 1) ^ k`.

* `Language` — a membership predicate on `List Bool`
* `Machine` — `accept : Word → Bool`, `steps : Word → Nat`
* `Verifier` — `verify : Word → Word → Bool`, `steps : Word → Word → Nat`
* `InP L` — some polynomial-time machine decides `L`
* `InNP L` — some polynomial-time verifier accepts exactly `L` with polynomially bounded certificates
* `InEXP L` — some exponential-time machine decides `L`
* `IncoNP L` — the complement of `L` is in `NP`

## Build

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
lake build
lake env lean Audit.lean
```

## Layout

```
Complexity.lean          -- library root
Complexity/Basic.lean    -- words, languages, machines, polynomial and exponential bounds
Complexity/Classes.lean  -- InP, InNP, InEXP, IncoNP, inclusions and closure properties
Audit.lean               -- #print axioms audit
paper/                   -- "P 与 NP 的形式化地基" (Markdown + PDF)
```

## Paper

`paper/pnp-formalization.md` — *P 与 NP 的形式化地基：一个 Lean 4 中可机器验证的复杂性类框架，
兼论「P = NP」为何仍然悬而未决*. It states the open status up front, walks through the
formalization, and surveys the relativization, natural-proofs and algebrization barriers.

Render it to PDF:

```bash
pandoc paper/pnp-formalization.md -o paper/pnp-formalization.pdf --pdf-engine=xelatex \
  -V mainfont="DejaVu Serif" -V monofont="DejaVu Sans Mono" -V CJKmainfont="AR PL UKai CN"
```

## Why no proof of P = NP

Because none exists. Lean checks proofs; it does not manufacture them. A complete Lean
proof of P = NP would be a historic mathematical result, not something a repository can
assert. The right test for any such claim is one command:

```bash
lake env lean Audit.lean   # look for sorryAx
```

## License

MIT
