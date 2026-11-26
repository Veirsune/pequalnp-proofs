import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_18880 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : List Bool), List.Forall₂ (fun (x5 x6 : Bool) => x5 ≤ x6) x3 x4 → x1.eval x3 ≤ x1.eval x4 := by
  have read {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) (i : ℕ) :
      a.getD i false ≤ b.getD i false := by
    induction h generalizing i with
    | nil => exact le_rfl
    | cons hab _ ih => cases i with
      | zero => exact hab
      | succ j => exact ih j

  have inputs (a b : ℕ → Bool) (h : ∀ i, a i ≤ b i) (l : List ℕ) :
      ((l.map a).all id ≤ (l.map b).all id) ∧ ((l.map a).any id ≤ (l.map b).any id) := by
    induction l with
    | nil => exact ⟨le_rfl, le_rfl⟩
    | cons i l ih =>
      simp only [List.map_cons, List.all_cons, List.any_cons, id_eq]
      have hh := h i
      rcases ih with ⟨h1,h2⟩
      constructor
      · revert hh h1; generalize a i = aa, b i = bb, (List.map a l).all id = xx, (List.map b l).all id = yy
        decide +revert
      · revert hh h2; generalize a i = aa, b i = bb, (List.map a l).any id = xx, (List.map b l).any id = yy
        decide +revert

  let step (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have extend {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) (g : Gate)
      (hop : g.op = .and ∨ g.op = .or) : List.Forall₂ (· ≤ ·) (step a g) (step b g) := by
    unfold step
    apply List.rel_append h
    apply List.Forall₂.cons _ List.Forall₂.nil
    have hh := inputs _ _ (read h) g.inputs
    rcases hop with e|e
    · simpa [e, GateOp.eval] using hh.1
    · simpa [e, GateOp.eval] using hh.2
  intro C hc a b h
  have fold (gs : List Gate) (hh : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ a b : List Bool, List.Forall₂ (· ≤ ·) a b → List.Forall₂ (· ≤ ·) (gs.foldl step a) (gs.foldl step b) := by
    induction gs with
    | nil => exact fun _ _ e => e
    | cons g gs ih =>
      intro u v e
      exact ih (fun k hk => hh k (by simp [hk])) _ _ (extend e g (hh g (by simp)))
  exact read (fold C.gates (fun g hg => (hc g hg).1) a b h) C.output
