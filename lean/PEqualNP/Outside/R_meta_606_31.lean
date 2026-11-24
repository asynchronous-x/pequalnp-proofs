import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_606_31 :
    (∃ a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      circuitFun n C = (fun x : Fin n → Bool =>
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ (D : Circuit) (out : Fin n → ℕ), Monotone2 D ∧
        D.size + (Finset.univ.image out).card + 1 ≤ a * (C.size + 1) ∧
        ∀ (v : Fin n) (x : Fin n → Bool),
          (∀ i j, G.Adj i j → x i = true → x j = false) →
          (D.wires (List.ofFn x)).getD (out v) false =
            circuitFun n C (Function.update x v true)) →
    (∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ (D : Circuit) (out : Fin n → ℕ), Monotone2 D →
      (∀ (v : Fin n) (x : Fin n → Bool),
        (∀ i j, G.Adj i j → x i = true → x j = false) →
        ((D.wires (List.ofFn x)).getD (out v) false = true ↔
          ∃ u, G.Adj v u ∧ x u = true)) →
      G.edgeFinset.card ≤ b * (D.size + (Finset.univ.image out).card + 1)) →
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  rintro ⟨a, extract⟩ ⟨b, count⟩
  refine ⟨b * a, ?_⟩
  intro n G inst girth C hm hc
  obtain ⟨D, out, hd, size, queries⟩ := extract n G girth C hm hc
  have rows (v : Fin n) (x : Fin n → Bool)
      (independent : ∀ i j, G.Adj i j → x i = true → x j = false) :
      (D.wires (List.ofFn x)).getD (out v) false = true ↔
        ∃ u, G.Adj v u ∧ x u = true := by
    rw [queries v x independent, hc]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      by_cases iv : i = v
      · subst i
        exact ⟨j, hij, by simpa only [Function.update_of_ne hij.ne.symm] using hj⟩
      by_cases jv : j = v
      · subst j
        exact ⟨i, hij.symm, by simpa only [Function.update_of_ne iv] using hi⟩
      rw [Function.update_of_ne iv] at hi
      rw [Function.update_of_ne jv] at hj
      exact Bool.noConfusion ((independent i j hij hi).symm.trans hj)
    · rintro ⟨u, hvu, hu⟩
      exact ⟨v, u, hvu, by simp, by simpa only [Function.update_of_ne hvu.ne.symm] using hu⟩
  calc
    G.edgeFinset.card ≤ b * (D.size + (Finset.univ.image out).card + 1) := count n G girth D out hd rows
    _ ≤ b * (a * (C.size + 1)) := Nat.mul_le_mul_left b size
    _ = (b * a) * (C.size + 1) := (Nat.mul_assoc ..).symm
