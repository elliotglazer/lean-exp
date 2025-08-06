# lean-exp

A collection of absurdly sophisticated proofs of simple mathematical facts in Lean 4. Proof of concept for a proposed benchmark of autoformalization agents.

## Overview

This project demonstrates how simple mathematical facts can be proven using unnecessarily complex mathematical machinery. It's inspired by the MathOverflow question ["Awfully sophisticated proof for simple facts"](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts) and [Asaf Karagila's proof of the irrationality of √2 using ultrafilters](https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational/1311239#1311239). These files test the faithfulness of repositories in mathlib by applying them in contrived yet mathematically rigorous proofs outside their typical applications.

## Autoformalizer Benchmark

This is a proof of concept for a proposed benchmark of autoformalization agents. A tested autoformalizer will be provided a proof, book, or paper, as well as a Lean file initialization listing key definitions and propositions with variable names corresponding to their index in the mathematical text and metadata regarding the types of all relevant objects. The agent is to convert the paper into a Lean library, giving the key defs and props their predetermined names and metadata. To assess the output library’s accuracy to the intended results, we append to the output an auxiliary Lean file which derives several corollaries of the paper’s props. The proofs in this file refer to the key defs and props by name, so in order for the appended doc to compile, it is necessary that the agent faithfully formalizes the referred results by their established name.

## Theorems Proved

### 1. Irrationality of √2 (`irrational_sqrt_2`)
**Statement**: √2 is irrational.

**Convoluted approach**: 
- Uses Dirichlet's theorem on primes in arithmetic progressions to get infinitely many primes ≡ 3 (mod 8)
- Constructs a non-principal ultrafilter on this infinite set using the hyperfilter
- Applies quadratic reciprocity to show 2 is not a square mod p for these primes
- Derives a contradiction by showing if √2 = a/b, then 2 would be a square mod p

**Reference**: Based on [Asaf Karagila's proof](https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational) (see comments)

### 2. Existence of Discontinuous Functions (`discontinuous_function_exists`)
**Statement**: There exists a function from ℝ to ℝ that is not continuous.

**Convoluted approach**:
- Proof by contradiction assuming all functions are continuous
- Uses cardinal arithmetic: if all functions were continuous, then #(ℝ → ℝ) ≤ #(ℚ → ℝ)
- Applies density of ℚ in ℝ and that continuous functions are determined by values on dense subsets
- Shows this implies 𝔠^𝔠 ≤ 𝔠^ℵ₀ = 𝔠
- Derives contradiction using Cantor's theorem: 𝔠 < 𝔠^𝔠

**Reference**: [MathOverflow discussion](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts)

## Building the Project

1. Install Lean 4 following the [official instructions](https://leanprover.github.io/lean4/doc/setup.html)
2. Clone this repository
3. Run `lake build` in the project directory

## Mathematical Background

The project showcases how advanced mathematical concepts can be (mis)used to prove elementary results:

- **Model Theory**: Ultraproducts, Łoś's theorem, first-order structures
- **Number Theory**: Dirichlet's theorem, quadratic reciprocity
- **Set Theory**: Cardinal arithmetic, Cantor's theorem

## Contributing

Feel free to add your own convoluted proofs! The more sophisticated the machinery for proving simple facts, the better.

## Credits

Coauthored with [Alok Singh.](https://github.com/alok/)

## License

Apache 2.0
