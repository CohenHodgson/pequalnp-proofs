import Mathlib
import PEqualNP.Defs

namespace CohenHodgson

def mat20 : List ℕ :=
  [589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504,
   19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921]

def pts : List (Fin 20 × Fin 20) :=
  [(⟨19, by decide⟩, ⟨17, by decide⟩),
   (⟨16, by decide⟩, ⟨14, by decide⟩),
   (⟨1, by decide⟩, ⟨12, by decide⟩),
   (⟨13, by decide⟩, ⟨7, by decide⟩),
   (⟨11, by decide⟩, ⟨0, by decide⟩),
   (⟨8, by decide⟩, ⟨15, by decide⟩)]

def pt (p : Fin 6) : Fin 20 × Fin 20 :=
  pts.get p

lemma pt_zero (p : Fin 6) :
    (mat20.getD (pt p).1.val 0).testBit (pt p).2.val = false := by
  fin_cases p <;> decide

lemma pt_cross (p q : Fin 6) (hpq : p ≠ q) :
    (mat20.getD (pt p).1.val 0).testBit (pt q).2.val = true ∨
      (mat20.getD (pt q).1.val 0).testBit (pt p).2.val = true := by
  fin_cases p <;> fin_cases q <;> simp [pt, pts, mat20] at hpq ⊢ <;> decide

end CohenHodgson

theorem PEqualNP.Outside.L_meta_11102 : ¬ (∃ L : List (Finset (Fin 20) × Finset (Fin 20)), L.length ≤ 5 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 20) (j : Fin 20), (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hlen, hzero, hcover⟩
  let rp : Fin 6 → (Finset (Fin 20) × Finset (Fin 20)) := fun p =>
    Classical.choose (hcover (CohenHodgson.pt p).1 (CohenHodgson.pt p).2
      (by simpa [CohenHodgson.mat20] using CohenHodgson.pt_zero p))
  have hrp_mem (p : Fin 6) : rp p ∈ L :=
    (Classical.choose_spec (hcover (CohenHodgson.pt p).1 (CohenHodgson.pt p).2
      (by simpa [CohenHodgson.mat20] using CohenHodgson.pt_zero p))).1
  have hrp_row (p : Fin 6) : (CohenHodgson.pt p).1 ∈ (rp p).1 :=
    (Classical.choose_spec (hcover (CohenHodgson.pt p).1 (CohenHodgson.pt p).2
      (by simpa [CohenHodgson.mat20] using CohenHodgson.pt_zero p))).2.1
  have hrp_col (p : Fin 6) : (CohenHodgson.pt p).2 ∈ (rp p).2 :=
    (Classical.choose_spec (hcover (CohenHodgson.pt p).1 (CohenHodgson.pt p).2
      (by simpa [CohenHodgson.mat20] using CohenHodgson.pt_zero p))).2.2
  let idx : Fin 6 → Fin L.length := fun p =>
    Classical.choose (List.mem_iff_get.mp (hrp_mem p))
  have hidx_get (p : Fin 6) : L.get (idx p) = rp p :=
    Classical.choose_spec (List.mem_iff_get.mp (hrp_mem p))
  have hinj : Function.Injective idx := by
    intro p q hpqidx
    by_contra hpq
    have hr_eq : rp p = rp q := by
      calc
        rp p = L.get (idx p) := (hidx_get p).symm
        _ = L.get (idx q) := by rw [hpqidx]
        _ = rp q := hidx_get q
    rcases CohenHodgson.pt_cross p q hpq with hcross | hcross
    · have hz : (CohenHodgson.mat20.getD (CohenHodgson.pt p).1.val 0).testBit
          (CohenHodgson.pt q).2.val = false := by
        simpa [CohenHodgson.mat20] using
          hzero (rp q) (hrp_mem q) (CohenHodgson.pt p).1
            (by simpa [hr_eq] using hrp_row p) (CohenHodgson.pt q).2 (hrp_col q)
      rw [hcross] at hz
      cases hz
    · have hz : (CohenHodgson.mat20.getD (CohenHodgson.pt q).1.val 0).testBit
          (CohenHodgson.pt p).2.val = false := by
        simpa [CohenHodgson.mat20] using
          hzero (rp p) (hrp_mem p) (CohenHodgson.pt q).1
            (by simpa [hr_eq] using hrp_row q) (CohenHodgson.pt p).2 (hrp_col p)
      rw [hcross] at hz
      cases hz
  have hcard : 6 ≤ L.length := by
    have h := Fintype.card_le_of_injective idx hinj
    simpa using h
  omega
