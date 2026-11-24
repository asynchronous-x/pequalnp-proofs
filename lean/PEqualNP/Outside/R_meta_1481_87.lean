import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1481_87
  (synthesis :
    let P : Fin 13 → Fin 26 := Fin.castAdd 13
    let Y : Fin 13 → Fin 26 := Fin.natAdd 13
    let I := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
    ∃ C : Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ p l, I p l → circuitFun 26 C (fun k => decide (k = P p ∨ k = Y l)) = true) ∧
      (∀ X : Finset (Fin 13), circuitFun 26 C (Fin.append (fun p => decide (p ∈ X))
          (fun l => decide (∀ p ∈ X, ¬I p l))) = false) ∧
      ∃ p l, I p l ∧ ∀ side : Bool,
        let base := if side then Y l else P p
        let seed := if side then P p else Y l
        let vals := fun i => (C.wires (List.ofFn fun k : Fin 26 => decide (k = base))).getD i false
        ¬Relation.ReflTransGen (fun i k : ℕ => ∃ j : Fin C.size,
          let g := C.gates.get j
          k = 26 + j.val ∧ i ∈ g.inputs ∧
          (g.op = .or ∨ ∀ b ∈ g.inputs, b ≠ i → vals b = true)) seed.val C.output)
  (active : ∀ (n : ℕ) (C : Circuit) (val : ℕ → Bool) (seed : Fin n),
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j) → ¬ Relation.ReflTransGen (fun i k : ℕ => ∃ j : Fin C.size,
          let g := C.gates.get j
          k = n + j.val ∧ i ∈ g.inputs ∧
          (g.op = .or ∨ ∀ b ∈ g.inputs, b ≠ i → val b = true)) seed.val C.output →
    ∃ d : ℕ → Bool, (∀ k : Fin n, d k.val = decide (k = seed)) ∧
      (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (n+j) = ((val a && d b) || (d a && val b))) ∧
        (g.op = .or → d (n+j) = (d a || d b))) ∧ d C.output = false) :
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  classical
  have boundary_complete {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (f : (Fin (N + N) → Bool) → Bool) (hf : Monotone f)
      (hp : ∀ p l, I p l →
        f (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true)
      (hn : ∀ X : Finset (Fin N),
        f (Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (∀ p ∈ X, ¬ I p l))) = false) :
      ∀ x, f x = true ↔ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
    intro x
    constructor
    · intro hx
      by_contra he
      let X : Finset (Fin N) := Finset.univ.filter (fun p => x (Fin.castAdd N p) = true)
      have hle : x ≤ Fin.addCases (motive := fun _ => Bool)
          (fun p => decide (p ∈ X)) (fun l => decide (∀ p ∈ X, ¬ I p l)) := by
        intro k
        refine Fin.addCases (motive := fun k => x k ≤ _) ?_ ?_ k
        · intro p
          apply Bool.le_iff_imp.mpr
          simpa [X]
        · intro l
          apply Bool.le_iff_imp.mpr
          intro hl
          simp only [Fin.addCases_right, decide_eq_true_eq]
          intro p hpm hI
          exact he ⟨p, l, hI, (Finset.mem_filter.mp hpm).2, hl⟩
      have him := hf hle
      rw [hx, hn X] at him
      contradiction
    · rintro ⟨p, l, hI, hxP, hxL⟩
      have hle : (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) ≤ x := by
        intro k
        apply Bool.le_iff_imp.mpr
        intro hk
        rcases of_decide_eq_true hk with hp' | hl'
        · simpa [hp'] using hxP
        · simpa [hl'] using hxL
      exact Bool.le_iff_imp.mp (hf hle) (hp p l hI)
  have binary_circuit_monotone {n : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
      (hg : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
         g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) :
      Monotone (fun (x : Fin n → Bool) => C.eval (List.ofFn x)) := by
    let stp (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  
    have eval_eq (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) :
        C.eval x = (C.gates.foldl stp x).getD C.output false := rfl
  
    have getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
        (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
      rcases lt_trichotomy i W.length with h | h | h
      · rw [if_neg (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
      · subst h
        simp [List.getD_eq_getElem?_getD]
      · rw [if_neg (by omega)]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  
    have ev_and (g : PEqualNP.CircuitLowerBounds.Gate) (f : ℕ → Bool) (h : g.op = PEqualNP.CircuitLowerBounds.GateOp.and) :
        (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
      rw [h]
      change ((g.inputs.map f).all id = true) ↔ _
      simp
  
    have ev_or (g : PEqualNP.CircuitLowerBounds.Gate) (f : ℕ → Bool) (h : g.op = PEqualNP.CircuitLowerBounds.GateOp.or) :
        (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
      rw [h]
      change ((g.inputs.map f).any id = true) ↔ _
      simp
  
    have mono : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W1 W2 : List Bool), W1.length = W2.length →
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ i, W1.getD i false = true → W2.getD i false = true) →
        ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
      intro gs
      induction gs with
      | nil => intro W1 W2 _ _ H; simpa using H
      | cons g gs ih =>
        intro W1 W2 hl hop H
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
          (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
        intro i
        simp only [stp, getD_snoc, hl]
        split_ifs
        · rcases hop g List.mem_cons_self with ha | ho
          · rw [ev_and g _ ha, ev_and g _ ha]
            intro h k hk
            exact H k (h k hk)
          · rw [ev_or g _ ho, ev_or g _ ho]
            rintro ⟨k, hk, h⟩
            exact ⟨k, hk, H k h⟩
        · exact H i
  
    have ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
        (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
      rw [List.getD_eq_getElem?_getD]
      split_ifs with h
      · rw [List.getElem?_eq_getElem (by simpa using h)]
        simp
      · rw [List.getElem?_eq_none (by simpa using h)]
        rfl
  
    have eval_mono_fn {n : ℕ} (gates : List PEqualNP.CircuitLowerBounds.Gate)
        (hg : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
        (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
        (h : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
      rw [eval_eq] at h ⊢
      refine mono gates _ _ (by simp) hg ?_ o h
      intro i
      rw [ofFn_getD, ofFn_getD]
      split_ifs with hi
      · exact hxy _
      · exact id
  
    intro x y hxy
    apply Bool.le_iff_imp.mpr
    apply eval_mono_fn C.gates _ x y _ C.output
    · intro g h
      obtain ⟨j, hj⟩ := List.getElem?_of_mem h
      exact hg j g hj
    · intro v
      exact Bool.le_iff_imp.mp (hxy v)
  obtain ⟨C, hs, hw, hpos, hneg, p, l, hpl, hsep⟩ := synthesis
  let I := fun u t : Fin 13 => u=t ∨ u=t+1 ∨ u=t+3 ∨ u=t+9
  have heval := boundary_complete I (circuitFun 26 C) (binary_circuit_monotone C (fun j g hg => (hw j g hg).1)) hpos hneg
  let vals (b : Fin 26) (i : ℕ) :=
    (C.wires (List.ofFn fun k : Fin 26 => decide (k = b))).getD i false
  obtain ⟨v, hv, hvG, hvO⟩ := active 26 C (vals (Fin.castAdd 13 p)) (Fin.natAdd 13 l) hw (hsep false)
  obtain ⟨w, hwI, hwG, hwO⟩ := active 26 C (vals (Fin.natAdd 13 l)) (Fin.castAdd 13 p) hw (hsep true)
  refine ⟨C, hs, hw, heval, p, l, hpl, ⟨v, ?_, hvG, hvO⟩, ⟨w, ?_, hwG, hwO⟩⟩
  · intro k
    have hne : Fin.castAdd 13 k ≠ Fin.natAdd 13 l := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    refine ⟨?_, ?_⟩
    · simpa only [Fin.val_castAdd, hne, decide_false] using hv (Fin.castAdd 13 k)
    · exact (hv (Fin.natAdd 13 k)).trans (decide_eq_decide.mpr (Fin.natAdd_inj 13))
  · intro k
    have hne : Fin.natAdd 13 k ≠ Fin.castAdd 13 p := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    refine ⟨?_, ?_⟩
    · exact (hwI (Fin.castAdd 13 k)).trans (decide_eq_decide.mpr Fin.castAdd_inj)
    · simpa only [Fin.val_natAdd, hne, decide_false] using hwI (Fin.natAdd 13 k)
