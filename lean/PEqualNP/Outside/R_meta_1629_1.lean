import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1629_1
  (firstOrder : ∀ (N : ℕ) (L : Fin N → Finset (Fin N)) (C : Circuit) (A : Fin N → Finset (Fin N)),
    (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) → Monotone2 C → (∀ (z : Fin (N + N) → Bool) (Y : Finset (Fin N)),
      (∀ l, z (Fin.natAdd N l) = true → l ∈ Y) → Y.card ≤ 1 →
      (¬ ∃ p l : Fin N, p ∈ L l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) →
    (∀ l, ∀ p ∈ A l, p ∈ L l ∧ Relation.ReflTransGen (fun a b : ℕ =>
          ∃ j : Fin C.size, b = N + N + j.val ∧ a < b ∧
            a ∈ (C.gates.get j).inputs ∧
            ((C.gates.get j).op = .or ∨ ∀ w ∈ (C.gates.get j).inputs, w ≠ a →
              w < b ∧ (C.wires (List.ofFn fun u : Fin (N + N) => decide (u = Fin.castAdd N p))).getD w false = true))
          (N + l.val) C.output) →
    ∑ l, (A l).card ≤ 12 * C.size + N)
  (nonlinear : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : Circuit) (A : Fin N → Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (L l).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l) → IsMinimalMonoCircuit (N + N) C →
    (∀ p l : Fin N, p ∈ L l → circuitFun (N + N) C
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ (z : Fin (N + N) → Bool) (Y : Finset (Fin N)),
      (∀ l, z (Fin.natAdd N l) = true → l ∈ Y) → Y.card ≤ q →
      (¬ ∃ p l : Fin N, p ∈ L l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) →
    (∀ l, ∀ p ∈ A l, p ∈ L l ∧ ¬ Relation.ReflTransGen (fun a b : ℕ =>
          ∃ j : Fin C.size, b = N + N + j.val ∧ a < b ∧
            a ∈ (C.gates.get j).inputs ∧
            ((C.gates.get j).op = .or ∨ ∀ w ∈ (C.gates.get j).inputs, w ≠ a →
              w < b ∧ (C.wires (List.ofFn fun u : Fin (N + N) => decide (u = Fin.castAdd N p))).getD w false = true))
          (N + l.val) C.output) →
    ∑ l, (A l).card ≤ 88 * C.size) : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 100 * C.size := by
  intro q N I inst C hq hn hc hu hm hp hs
  classical
  let ok := fun k : ℕ => ∃ D : Circuit, Monotone2 D ∧ circuitFun (N + N) D = circuitFun (N + N) C ∧ D.size = k
  have hex : ∃ k, ok k := ⟨C.size, C, hm, rfl, rfl⟩
  obtain ⟨D, hd, hf, hsize⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, Monotone2 E → circuitFun (N + N) E = circuitFun (N + N) D → D.size ≤ E.size := by
    intro E he heq
    rw [hsize]
    exact Nat.find_min' hex ⟨E, he, heq.trans hf, rfl⟩
  have hdc : D.size ≤ C.size := hmin C hm hf.symm
  let good := fun (p l : Fin N) => Relation.ReflTransGen (fun a b : ℕ =>
          ∃ j : Fin D.size, b = N + N + j.val ∧ a < b ∧
            a ∈ (D.gates.get j).inputs ∧
            ((D.gates.get j).op = .or ∨ ∀ w ∈ (D.gates.get j).inputs, w ≠ a →
              w < b ∧ (D.wires (List.ofFn fun u : Fin (N + N) => decide (u = Fin.castAdd N p))).getD w false = true))
          (N + l.val) D.output
  let line := fun l : Fin N => Finset.univ.filter (fun p : Fin N => I p l)
  let A := fun l : Fin N => (line l).filter (fun p => good p l)
  let B := fun l : Fin N => (line l).filter (fun p => ¬ good p l)
  have hcover (z : Fin (N + N) → Bool) (Y : Finset (Fin N))
      (hy : ∀ l, z (Fin.natAdd N l) = true → l ∈ Y) :
      (Finset.univ.filter fun l : Fin N => z (Fin.natAdd N l) = true).card ≤ Y.card := by
    apply Finset.card_le_card
    intro l h
    exact hy l (Finset.mem_filter.mp h).2
  have huL : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ line l ∧ p' ∈ line l := by
    simpa [line] using hu
  have hA := firstOrder N line D A huL hd (by
    intro z Y hy hlim hneg
    rw [hf]
    exact hs z (le_trans (hcover z Y hy) (by omega)) (by simpa [line] using hneg)) (by
    intro l p hp'
    simpa [A, line, good] using hp')
  have hB := nonlinear q N line D B hq hn hc huL ⟨hd, hmin⟩ (by
    intro p l hi
    rw [hf]
    exact hp p l (by simpa [line] using hi)) (by
    intro z Y hy hlim hneg
    rw [hf]
    exact hs z (le_trans (hcover z Y hy) hlim) (by simpa [line] using hneg)) (by
    intro l p hp'
    simpa [B, line, good] using hp')
  have hsum : (∑ l, (A l).card) + (∑ l, (B l).card) = N * (q + 1) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _l : Fin N, (q + 1) := by
        apply Finset.sum_congr rfl
        intro l _
        change ((line l).filter _).card + ((line l).filter _).card = q + 1
        rw [Finset.card_filter_add_card_filter_not]
        exact hc l
      _ = _ := by simp
  rw [Nat.mul_add, Nat.mul_one] at hsum
  omega
