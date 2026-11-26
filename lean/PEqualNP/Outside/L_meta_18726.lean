import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18726_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev exampleCircuit : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [3, 4]⟩], 5⟩

def keepSet : Finset (Fin 3) := {2}
def pruneSet : Finset (Fin 3) := {0, 1}

theorem copies (j : Fin 3) (hj : j ∈ keepSet) :
    ∃ w ∈ (exampleCircuit.gates.get j).inputs, w < 3 + j.val ∧
      ∀ x : Fin 3 → Bool,
      (exampleCircuit.wires (List.ofFn (Function.update x 2 false))).getD (3+j.val) false =
      (exampleCircuit.wires (List.ofFn (Function.update x 2 false))).getD w false := by
  have eqj : j = 2 := by simpa [keepSet] using hj
  subst j
  exact ⟨3, by decide, by decide, by decide⟩

theorem refutation : ¬ (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool) (K P : Finset (Fin C.gates.length)), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → Disjoint K P → (∀ j ∈ K, (∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = c) ∨ (∃ w ∈ (C.gates.get j).inputs, ∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD w false = c) ∨ ∃ w ∈ (C.gates.get j).inputs, w < n + j.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = (C.wires (List.ofFn (Function.update x v b))).getD w false) → (∀ p ∈ P, n + p.val ≠ C.output ∧ ∀ k : Fin C.gates.length, n + p.val ∈ (C.gates.get k).inputs → k ∈ P ∨ (k ∈ K ∧ ((∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = c) ∨ ∃ w ∈ (C.gates.get k).inputs, w < n + k.val ∧ w ≠ n + p.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = (C.wires (List.ofFn (Function.update x v b))).getD w false))) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + K.card + P.card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b))) := by
  intro h
  have hf : FanInTwo exampleCircuit := by
    intro g hg
    simp at hg
    rcases hg with rfl | rfl | rfl <;> simp
  have hnot : ∀ g ∈ exampleCircuit.gates, g.op = GateOp.not → g.inputs.length = 1 := by
    intro g hg
    simp at hg
    rcases hg with rfl | rfl | rfl <;> simp
  obtain ⟨⟨gs, o⟩, _, hs, hv⟩ := h 3 exampleCircuit 2 false keepSet pruneSet hf hnot
    ⟨(fun _ => false), by decide⟩ (by decide)
    (fun j hj => Or.inr (Or.inr (copies j hj))) (by
      intro p hp
      have casesP : p = (0 : Fin 3) ∨ p = (1 : Fin 3) := by simpa [pruneSet] using hp
      rcases casesP with rfl | rfl
      · refine ⟨by decide, ?_⟩
        intro k hk
        have isLast : k = (2 : Fin 3) := by
          change Fin 3 at k; fin_cases k <;> first | rfl | exfalso; revert hk; decide
        subst k
        exact Or.inr ⟨by decide, Or.inr ⟨4, by decide, by decide, by decide, by decide⟩⟩
      · refine ⟨by decide, ?_⟩
        intro k hk
        have isLast : k = (2 : Fin 3) := by
          change Fin 3 at k; fin_cases k <;> first | rfl | exfalso; revert hk; decide
        subst k
        exact Or.inr ⟨by decide, Or.inr ⟨3, by decide, by decide, by decide, by decide⟩⟩)
  have size : gs.length + 1 + 2 ≤ 3 := hs
  have nilG : gs = [] := List.length_eq_zero_iff.mp (by omega)
  subst gs
  have test0 := hv (fun i => decide (i = 0))
  have test1 := hv (fun i => decide (i = 1))
  have test2 := hv (fun i => decide (i = 2))
  have testAll := hv (fun _ => true)
  change [true, false, false].getD o false = false at test0
  change [false, true, false].getD o false = false at test1
  change [false, false, true].getD o false = false at test2
  change [true, true, true].getD o false = true at testAll
  cases o with
  | zero => contradiction
  | succ o =>
    cases o with
    | zero => contradiction
    | succ o =>
      cases o with
      | zero => contradiction
      | succ o => simp [List.getD] at testAll

end PEqualNP.Outside.L_meta_18726_aux

theorem PEqualNP.Outside.L_meta_18726 : ¬ (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool) (K P : Finset (Fin C.gates.length)), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → Disjoint K P → (∀ j ∈ K, (∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = c) ∨ (∃ w ∈ (C.gates.get j).inputs, ∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD w false = c) ∨ ∃ w ∈ (C.gates.get j).inputs, w < n + j.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = (C.wires (List.ofFn (Function.update x v b))).getD w false) → (∀ p ∈ P, n + p.val ≠ C.output ∧ ∀ k : Fin C.gates.length, n + p.val ∈ (C.gates.get k).inputs → k ∈ P ∨ (k ∈ K ∧ ((∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = c) ∨ ∃ w ∈ (C.gates.get k).inputs, w < n + k.val ∧ w ≠ n + p.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = (C.wires (List.ofFn (Function.update x v b))).getD w false))) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + K.card + P.card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b))) :=
  PEqualNP.Outside.L_meta_18726_aux.refutation
