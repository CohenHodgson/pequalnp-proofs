import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_11092 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Sym2 (Fin x1))), (∀ x4 ∈ x3, x4 ∈ x2.edgeSet) → (∀ x5 ∈ x3, ∀ x7 ∈ x3, ∀ x9 ∈ x5, x9 ∈ x7 → x5 = x7) → x3.card ≤ x2.edgeSet.ncard := by
  intro n G E hsub _
  have hsub' : (E : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
    intro e he
    exact hsub e he
  have h := Set.ncard_le_ncard hsub'
  simpa using h
