/-
First proof of concept problem for assessing a library via convoluted proof of a simple consequence.
In this file, the basic theory of cardinality, as developed in mathlib, is applied to prove
existence of a discontinuous function from R to R. Note that no such function is computable, so
the imported libraries are necessarily supplying noncomputable content to this proof.

If an alterantive library for set theory (or at least cardinality) is developed, and had substitutes for all of the mathlib functions so that
this document compiles, then its theory of cardinal arithmetic would likely be essentially equivalent to that of mathlib.

Ultimately, the goal of this project is to produce examples of problems like this for areas of math or specific texts for which
there is no pre-existing library which allows it to compile.

-/

import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Topology.Defs.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

theorem disc_fnct : ∃ f : ℝ → ℝ, ¬ Continuous f := by
  apply byContradiction
  intro (h1: ¬ (∃ f : ℝ → ℝ, ¬ Continuous f))
  have h2 : ∀ f : ℝ → ℝ, Continuous f := by
    not_exists_not (f : ℝ → ℝ, Continuous f)
  def S := Set ℝ → ℝ
  def T := Set ℝ
  have h3 : ¬ (#S ≤ #T) := by
    have : #T = 𝔠 := mk_univ_real
    have : #S = 𝔠^𝔠 := power_def 𝔠 𝔠
    have : #S = 2^𝔠 := power_self_eq 𝔠
    have : #T < #S := cantor 𝔠
    apply lt_iff_le_not_le
  def F (f : ℝ → ℝ) (q : ℚ) : ℝ :=
    f ↑(q)
  have : Injective F := by
    intro f g (h : F f = F g)
    have : Continuous (f - g) := h2 (f - g)
    have : IsClosed ({0}: Set ℝ):=isClosed_singleton {0: ℝ}
    have h5 : IsClosed ((f-g)⁻¹' {0: ℝ}) :=
    IsClosed.preimage((f-g), {0: ℝ}(h : IsClosed {0, ℝ}))
    have h0 : ∀ q ∈ ℚ, (f-g)(↑(q)) = 0 :=
    calc (f-g)(↑(q)) = f(↑(q)) - g(↑(q))
                  _  = F(q) - F(q) := rw h0
                  _  = 0 := 0 + F(q)=F(q)
    have h9 : Rat.denseRange_cast {ℝ} ⊆ (f-g)⁻¹'{0: ℝ} := h0
    have h6 : IsDense ((f-g)⁻¹' {0: ℝ}) := by
      intro (r : ℝ)
      show : r ∈ closure ((f-g)⁻¹'{0: ℝ}) :=
      calc r ∈ closure (range (↑ : ℚ → ℝ)):= h6
           _ ⊆ ((f-g)⁻¹' {0: ℝ}) := subset_closure(range (↑ : ℚ → ℝ))
    have : ∀ x ∈ ℝ, x ∈ closure ((f-g)⁻¹'{0: ℝ}) := h6
    have : closure ((f-g)⁻¹') = (f-g)⁻¹'{0: ℝ} :=h5
    have : ∀ x ∈ ℝ, (f-g)(x) ∈ {0: ℝ} :=
    calc (f-g)(x) = f(x) - g(x)
    have : ∀ x ∈ ℝ, f(x) - g(x) = 0 := rw h5
    have h7 : ∀ x ∈ ℝ, f x = g x
    show f = g
    exact funext f g h7
  have : #S ≤ #(Set (ℚ → ℝ)) := mk_le_of_injective S (Set (ℚ → ℝ))
  have h4 : #S ≤ #T :=
  calc #S ≤ #(Set (ℚ → ℝ)) := mk_le_of_injective S (Set (ℚ → ℝ))
       _  = #(Set ℝ)^(#(Set ℚ))
       _  = 𝔠^{#(Set ℚ)} := mk_univ_real
       _  = 𝔠^{ℵ_0} := Cardinal.mkRat
       _  = 𝔠 := continuum_power_aleph0
  have h4 : #S ≤ #T := mk_le_of_injective S T
  show False
  exact h3 h4
