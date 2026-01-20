import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.BooleanAlgebra.Basic

open Set
open Filter

namespace AtomlessBooleanAlgebra

def Cantor := ℕ → Bool

def BitString (n : ℕ) := Fin n → Bool

def cylinder {n : ℕ} (s : BitString n) : Set Cantor :=
  { x | ∀ i : Fin n, x i = s i }

def CountableAtomlessBA : BooleanSubalgebra (Set Cantor) :=
  BooleanSubalgebra.closure
    { A | ∃ S : Finset (Σ n, BitString n), A = ⋃ p ∈ S, cylinder p.2 }

def update {n : ℕ} (s : BitString n) (k : Fin n) (b : Bool) : BitString n :=
  fun i => if i = k then b else s i

lemma cylinder_split {n : ℕ} (s : BitString n) :
  ∃ (s0 s1 : BitString (n + 1)),
    cylinder s = cylinder s0 ∪ cylinder s1 ∧
    Disjoint (cylinder s0) (cylinder s1) ∧
    (cylinder s0).Nonempty ∧
    (cylinder s1).Nonempty := by
  -- s0 extends s with bit false, s1 extends s with bit true
  let s0 : BitString (n + 1) := fun i =>
    if h : i.val < n then s ⟨i.val, h⟩ else false
  let s1 : BitString (n + 1) := fun i =>
    if h : i.val < n then s ⟨i.val, h⟩ else true
  use s0, s1
  constructor
  · -- cylinder s = cylinder s0 ∪ cylinder s1
    ext x
    simp only [mem_union, cylinder, Set.mem_setOf_eq]
    constructor
    · intro hx
      by_cases h : x n = false
      · left
        intro i
        by_cases hi : i.val < n
        · simp only [s0, hi, dite_true]
          exact hx ⟨i.val, hi⟩
        · have : i.val = n := by omega
          have : i = ⟨n, by omega⟩ := by ext; exact this
          rw [this]
          simp only [s0, lt_self_iff_false, dite_false]
          exact h
      · right
        intro i
        by_cases hi : i.val < n
        · simp only [s1, hi, dite_true]
          exact hx ⟨i.val, hi⟩
        · have : i.val = n := by omega
          have : i = ⟨n, by omega⟩ := by ext; exact this
          rw [this]
          simp only [s1, lt_self_iff_false, dite_false]
          simp only [Bool.not_eq_false] at h
          exact h
    · intro hx i
      cases hx with
      | inl h0 =>
        have := h0 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        simp only [s0] at this
        simp only [dif_pos i.isLt] at this
        exact this
      | inr h1 =>
        have := h1 ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        simp only [s1] at this
        simp only [dif_pos i.isLt] at this
        exact this
  constructor
  · -- Disjoint
    rw [Set.disjoint_iff]
    intro x
    simp only [mem_inter_iff, cylinder, Set.mem_setOf_eq, mem_empty_iff_false]
    intro ⟨h0, h1⟩
    have eq0 : x n = false := by
      have := h0 ⟨n, Nat.lt_succ_self n⟩
      simp only [s0, lt_self_iff_false, dite_false] at this
      exact this
    have eq1 : x n = true := by
      have := h1 ⟨n, Nat.lt_succ_self n⟩
      simp only [s1, lt_self_iff_false, dite_false] at this
      exact this
    rw [eq0] at eq1
    cases eq1
  constructor
  · -- s0 nonempty
    use fun i => if h : i < n then s ⟨i, h⟩ else false
    intro i
    by_cases h : i.val < n <;> simp [s0, h]
  · -- s1 nonempty
    use fun i => if h : i < n then s ⟨i, h⟩ else true
    intro i
    by_cases h : i.val < n <;> simp [s1, h]


end AtomlessBooleanAlgebra

def StoneSpace (B : Type _) [BooleanAlgebra B] := Ultrafilter B

def StoneBasicOpen {B : Type _} [BooleanAlgebra B] (b : B) :
  Set (Ultrafilter B) :=
  { F | {b} ∈ F.toFilter }
