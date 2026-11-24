import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_1669_47
    (gate_elim : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ),
      (∃ y z : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc z b)) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ s + 1 →
        (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = f x) →
        (D.size ≤ s ∨ ∃ x : Fin (n + 1) → Bool,
          f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x) →
        HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s)
    (fullBound : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14)
    (partialBound : ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      (∀ x : Fin 9 → Bool, (x 0 && x 3) = false →
        D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → False) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  -- The first gate becomes the last input of the residual circuit.
  have extract_tail (C : Circuit) (hf : FanInTwo C)
      (hh : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) :
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧ ∀ y : Fin 9 → Bool,
        D.eval (List.ofFn (Fin.snoc y (y 0 && y 3))) = C.eval (List.ofFn y) := by
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have ext (gs : List Gate) (w : List Bool) : ∃ v, gs.foldl step w = w ++ v := by
      induction gs generalizing w with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih =>
        obtain ⟨v, hv⟩ := ih (step w g)
        exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ v, by
          simpa [step, List.append_assoc] using hv⟩
    obtain ⟨gs, out⟩ := C
    cases gs with
    | nil =>
      have h := hh (fun _ => true)
      change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = (true && true) at h
      simp [List.getD_eq_getElem?_getD] at h
    | cons g gs =>
      refine ⟨⟨gs, out⟩, ?_, rfl, ?_⟩
      · exact fun g' hm => hf g' (List.mem_cons_of_mem g hm)
      · intro y
        have hfirst := hh y
        change (gs.foldl step (step (List.ofFn y) g)).getD 9 false = (y 0 && y 3) at hfirst
        obtain ⟨v, hv⟩ := ext gs (step (List.ofFn y) g)
        rw [hv, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (show 9 < (step (List.ofFn y) g).length by simp [step])] at hfirst
        simp [step] at hfirst
        have hsnoc : List.ofFn (Fin.snoc y (y 0 && y 3)) = List.ofFn y ++ [y 0 && y 3] := by
          rw [List.ofFn_succ_last]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [hsnoc]
        change (gs.foldl step (List.ofFn y ++ [y 0 && y 3])).getD out false =
          (gs.foldl step (step (List.ofFn y) g)).getD out false
        rw [← hfirst]
        simp [step]

  intro C ok first correct
  by_contra! small
  let target := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  obtain ⟨D, hd, sizeD, tail⟩ := extract_tail C ok first
  let t := circuitFun 10 D
  have onSlice (x : Fin 9 → Bool) : t (Fin.snoc x (x 0 && x 3)) = target x :=
    (tail x).trans (congrFun correct x)
  have hpartial (x : Fin 9 → Bool) (hx : (x 0 && x 3) = false) :
      t (Fin.snoc x false) = target x := by simpa [hx] using onSlice x
  let y : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
  let z : Fin 9 → Bool := fun _ => false
  have hnc : ∃ y z : Fin 9 → Bool, t (Fin.snoc y false) ≠ t (Fin.snoc z false) := by
    refine ⟨y, z, ?_⟩
    rw [hpartial y (by decide), hpartial z (by decide)]
    decide
  -- An essential auxiliary input gives the smaller problem on its zero slice.
  by_cases sensitive : ∃ x : Fin 10 → Bool,
      t (Function.update x (Fin.last 9) (!x (Fin.last 9))) ≠ t x
  · obtain ⟨E, he, hsize, evalE⟩ := gate_elim 9 t false 13 hnc D hd (by omega) (fun _ => rfl) (Or.inr sensitive)
    exact partialBound E he hsize (fun x hx => (evalE x).trans (hpartial x hx))
  · obtain ⟨E, he, hsize, evalE⟩ := gate_elim 9 t false 14 hnc D hd (by omega) (fun _ => rfl) (Or.inl (by omega))
    apply fullBound
    refine ⟨E, he, hsize, fun x => (evalE x).trans ?_⟩
    cases hbit : x 0 && x 3 with
    | false => exact hpartial x hbit
    | true =>
      have hs : t (Fin.snoc x false) = t (Fin.snoc x true) := by
        have h := not_exists.mp sensitive (Fin.snoc x false)
        apply Eq.symm
        rw [not_not] at h
        convert h using 2
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Function.update_self, Fin.snoc_last, Fin.snoc_last]
          rfl
        · rw [Function.update_of_ne (Fin.castSucc_ne_last j), Fin.snoc_castSucc, Fin.snoc_castSucc]
      have h := onSlice x
      rw [hbit] at h
      exact hs.trans h
