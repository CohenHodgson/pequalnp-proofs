import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_3321_1
    (oneHot : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C →
      ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit,
        Monotone2 D ∧
        ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool,
          circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        ∀ j < D.gates.length,
          (gateAt D j).op =
            GateOp.and →
          (∀ p : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)))).getD
              (N + N + j) false = false) ∧
          ∀ l : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)))).getD
              (N + N + j) false = false)
    (rectangles : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C →
      ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      (∀ j < C.gates.length,
        (gateAt C j).op =
          GateOp.and →
        (∀ p : Fin N,
          (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)))).getD
            (N + N + j) false = false) ∧
        ∀ l : Fin N,
          (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)))).getD
            (N + N + j) false = false) →
      ∃ D : Circuit,
        Monotone2 D ∧
        ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool,
          circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length,
          (gateAt D j).op =
            GateOp.and →
          ∀ z : Fin (N + N) → Bool,
            (D.wires (List.ofFn z)).getD (N + N + j) false = true →
            (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k.val < N) && z k))).getD
                (N + N + j) false = true ∨
              (D.wires (List.ofFn (fun k : Fin (N + N) => decide (N ≤ k.val) && z k))).getD
                  (N + N + j) false = true ∨
              ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        ∀ j < D.gates.length,
          (gateAt D j).op =
            GateOp.and →
          (∀ p : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)))).getD
              (N + N + j) false = false) ∧
          ∀ l : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)))).getD
              (N + N + j) false = false) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C →
      ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit,
        Monotone2 D ∧
        ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool,
          circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length,
          (gateAt D j).op =
            GateOp.and →
          ∀ z : Fin (N + N) → Bool,
            (D.wires (List.ofFn z)).getD (N + N + j) false = true →
            (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k.val < N) && z k))).getD
                (N + N + j) false = true ∨
              (D.wires (List.ofFn (fun k : Fin (N + N) => decide (N ≤ k.val) && z k))).getD
                  (N + N + j) false = true ∨
              ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        ∀ j < D.gates.length,
          (gateAt D j).op =
            GateOp.and →
          (∀ p : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)))).getD
              (N + N + j) false = false) ∧
          ∀ l : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)))).getD
              (N + N + j) false = false := by
  intro N I _ C hno4 hmono hread hfun
  obtain ⟨D, hDm, hDr, hDs, hDf, hDhot⟩ := oneHot N I C hno4 hmono hread hfun
  obtain ⟨E, hEm, hEr, hEs, hEf, hErect, hEhot⟩ :=
    rectangles N I D hno4 hDm hDr hDf hDhot
  exact ⟨E, hEm, hEr, hEs.trans hDs, hEf, hErect, hEhot⟩
