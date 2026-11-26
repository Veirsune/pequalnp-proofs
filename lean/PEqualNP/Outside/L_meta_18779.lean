import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18779_aux

open PEqualNP.CircuitLowerBounds

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem keepInput (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl extend w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [extend]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem readInput {n : ℕ} (C : Circuit) (hi : C.output < n) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = x ⟨C.output, hi⟩ := by
  change (C.gates.foldl extend (List.ofFn x)).getD C.output false = _
  rw [keepInput _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

end PEqualNP.Outside.L_meta_18779_aux

theorem PEqualNP.Outside.L_meta_18779 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (42 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (22 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true := by
  intro C ho _ _ hcomputes
  let x : Fin 42 → Bool := fun i => decide (i.val = C.output)
  have htrue : C.eval (List.ofFn x) = true := by
    rw [PEqualNP.Outside.L_meta_18779_aux.readInput C ho x]
    simp [x]
  obtain ⟨p, l, ⟨hp, hl, _⟩, hxp, hxl⟩ := (hcomputes x).mp htrue
  simp only [x, decide_eq_true_eq] at hxp hxl
  omega
