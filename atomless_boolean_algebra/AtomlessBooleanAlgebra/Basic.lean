import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
-- import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.RelClasses

open Set
open Filter

namespace AtomlessBooleanAlgebra

def Cantor := ℕ → Bool

def BitString (n : ℕ) := Fin n → Bool deriving DecidableEq

def cylinder {n : ℕ} (s : BitString n) : Set Cantor :=
  { x | ∀ i : Fin n, x i = s i }

def compatible {n m : ℕ} (s : BitString n) (t : BitString m) : Prop :=
  ∀ (i : ℕ) (hn : i < n) (hm : i < m), s ⟨i, hn⟩ = t ⟨i, hm⟩

lemma incompatible_empty
  {n m : ℕ} {s : BitString n} {t : BitString m}
  (h : ¬ compatible s t) :
  cylinder s ∩ cylinder t = ∅ := by
  ext x
  simp only [mem_inter_iff, cylinder, Set.mem_setOf_eq, mem_empty_iff_false]
  constructor
  · intro ⟨hx_s, hx_t⟩
    simp only [compatible, not_forall] at h
    obtain ⟨i, hn, hm, hneq⟩ := h
    have eq_s : x i = s ⟨i, hn⟩ := hx_s ⟨i, hn⟩
    have eq_t : x i = t ⟨i, hm⟩ := hx_t ⟨i, hm⟩
    rw [eq_s] at eq_t
    exact hneq eq_t
  · intro hx
    exact False.elim hx

lemma compatible_inter {n m : ℕ} {s : BitString n} {t : BitString m} (h : compatible s t) :
    ∃ (p : Σ k, BitString k), cylinder s ∩ cylinder t = cylinder p.2 := by
  cases le_total n m with
  | inl hle =>
    -- Case: n ≤ m. The intersection is the longer one (t).
    use ⟨m, t⟩
    ext x
    simp only [mem_inter_iff, cylinder, mem_setOf_eq]
    constructor
    · intro ⟨_, ht⟩; exact ht
    · intro ht
      refine ⟨?_, ht⟩
      intro i
      -- Since i < n and n ≤ m, then i < m.
      have hi_m : i.val < m := Nat.lt_of_lt_of_le i.isLt hle
      -- Use the compatibility property
      rw [h i.val i.isLt hi_m]
      exact ht ⟨i.val, hi_m⟩
  | inr hle =>
    -- Case: m ≤ n. The intersection is the longer one (s).
    use ⟨n, s⟩
    ext x
    simp only [mem_inter_iff, cylinder, mem_setOf_eq]
    constructor
    · intro ⟨hs, _⟩; exact hs
    · intro hs
      refine ⟨hs, ?_⟩
      intro i
      have hi_n : i.val < n := Nat.lt_of_lt_of_le i.isLt hle
      -- Use the symmetric compatibility property
      rw [← h i.val hi_n i.isLt]
      exact hs ⟨i.val, hi_n⟩

lemma cylinder_intersection {n m : ℕ} (s : BitString n) (t : BitString m) :
  ∃ (p : Option (Σ k, BitString k)),
    cylinder s ∩ cylinder t =
      match p with
      | none => ∅
      | some ⟨_, u⟩ => cylinder u := by
  by_cases h : compatible s t
  · -- compatible case: intersection is a cylinder
    obtain ⟨p, hp⟩ := compatible_inter h
    exact ⟨some p, hp⟩
  · -- incompatible case: intersection is empty
    exact ⟨none, incompatible_empty h⟩

def CountableAtomlessBA : BooleanSubalgebra (Set Cantor) where
  carrier := { A | ∃ S : Finset (Σ n, BitString n), A = ⋃ p ∈ S, cylinder p.2 }

  bot_mem' := by
    use ∅
    simp

  supClosed' := by
    intro A hA B hB
    obtain ⟨SA, hA_eq⟩ := hA
    obtain ⟨SB, hB_eq⟩ := hB
    use SA ∪ SB
    rw [hA_eq, hB_eq]
    ext x
    change x ∈ (⋃ p ∈ SA, cylinder p.snd) ∪ (⋃ p ∈ SB, cylinder p.snd) ↔ _
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_union, Sigma.exists, exists_prop]
    aesop

  infClosed' := by
    intro A hA B hB
    obtain ⟨SA, hA_eq⟩ := hA
    obtain ⟨SB, hB_eq⟩ := hB
    -- Goal: show that the intersection is also a finite union of cylinders
    -- The intersection of two finite unions is a finite union of intersections by De Morgan's law
    -- Each intersection of two cylinders is either empty or a cylinder by the above lemma
    -- Use biUnion to construct the intersection set
    let SI : Finset (Σ n, BitString n) :=
      (SA.product SB).biUnion (fun ⟨p, q⟩ =>
        match (cylinder_intersection p.2 q.2).choose with
        | none => ∅
        | some u => {u})
    use SI
    rw [hA_eq, hB_eq]
    ext x
    change x ∈ (⋃ p ∈ SA, cylinder p.snd) ∩ (⋃ p ∈ SB, cylinder p.snd) ↔ _
    rw [Set.iUnion_inter_iUnion]
    simp only [Set.mem_iUnion, Finset.mem_product, Sigma.exists, exists_prop]
    sorry


  compl_mem' := by sorry

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

lemma cylinder_mem {n : ℕ} (s : BitString n) :
  cylinder s ∈ CountableAtomlessBA.carrier := by
  -- 1. Reveal the definition of the carrier
  change ∃ S : Finset (Σ n, BitString n), cylinder s = ⋃ p ∈ S, cylinder p.2
  -- 2. Provide the "witness": a Finset containing just this bitstring
  use {⟨n, s⟩}
  -- 3. Prove that the union over a singleton is just the set itself
  simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]

/-- Every cylinder is non-empty because we can always construct an
    infinite sequence starting with the given prefix. -/
lemma cylinder_nonempty {n : ℕ} (s : BitString n) :
    (cylinder s).Nonempty := by
  -- Construct an infinite sequence x:
  -- If index i < n, use the bit from the BitString.
  -- If index i ≥ n, just use 'false'.
  let x : Cantor := fun i =>
    if h : i < n then s ⟨i, h⟩ else false
  use x
  intro i
  -- By definition of x, when i < n, x i is exactly s i
  simp [x, i.isLt]

lemma exists_cylinder_subset {A : Set Cantor}
    (hA : A ∈ CountableAtomlessBA.carrier) (hne : A.Nonempty) :
    ∃ n, ∃ s : BitString n, cylinder s ⊆ A := by
  -- 1. Unpack the definition: A is a finite union of cylinders
  obtain ⟨S, h_eq⟩ := hA
  -- 2. If the union is nonempty, the index set S cannot be empty
  have hS_ne : S.Nonempty := by
    contrapose! hne
    rw [h_eq]
    simp [hne]
  -- 3. Pick an arbitrary bitstring p = ⟨n, s⟩ from S
  obtain ⟨p, hp⟩ := hS_ne
  use p.1, p.2
  -- 4. Prove that cylinder p.2 is a subset of the union A
  rw [h_eq]
  intro x hx
  simp only [mem_iUnion, Sigma.exists, exists_prop]
  use p.1, p.2, hp, hx

theorem CountableAtomlessBA_is_atomless :
  ∀ b ∈ CountableAtomlessBA.carrier, b.Nonempty →
  ∃ a ∈ CountableAtomlessBA.carrier, a.Nonempty ∧ a ⊂ b := by
  intro b hb hne
  -- 1. Find a cylinder inside b
  obtain ⟨n, s, hsub⟩ := exists_cylinder_subset hb hne
  -- 2. Split that cylinder into two disjoint cylinders
  obtain ⟨s0, s1, split_eq, disj, nonempty_s0, nonempty_s1⟩ := cylinder_split s
  -- 3. Let a be one of the halves
  let a := cylinder s0
  -- 4. a is in the algebra and nonempty
  have ha : a ∈ CountableAtomlessBA.carrier := cylinder_mem s0
  have ha_nonempty : a.Nonempty := nonempty_s0
  -- 6. a ⊆ b
  have ha_subset_b : a ⊆ b := by
    have h_a_sub_s : a ⊆ cylinder s := by
      rw [split_eq]
      exact Set.subset_union_left
    exact Set.Subset.trans h_a_sub_s hsub
  -- 7. a ⊂ b (Proper Subset)
  have ha_ssubset_b : a ⊂ b := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨ha_subset_b, ?_⟩
    intro heq
    -- cylinder s1 is inside b
    have s1_sub_b : cylinder s1 ⊆ b := by
      have h_s1_sub_s : cylinder s1 ⊆ cylinder s := by
        rw [split_eq]
        exact Set.subset_union_right
      exact Set.Subset.trans h_s1_sub_s hsub
    -- Since a = b, cylinder s1 ⊆ a
    -- We use 'heq' to change 'b' to 'a' in the type of 's1_sub_b'
    have s1_sub_a : cylinder s1 ⊆ a := heq ▸ s1_sub_b
    -- Contradiction: s1 is non-empty and contained in a, but s1 and a are disjoint
    obtain ⟨x, hx⟩ := nonempty_s1
    have x_in_a : x ∈ a := s1_sub_a hx
    -- 'disj' is Disjoint a (cylinder s1)
    exact Set.disjoint_iff.mp disj ⟨x_in_a, hx⟩
  -- 8. Final assembly
  exact ⟨a, ha, ha_nonempty, ha_ssubset_b⟩

end AtomlessBooleanAlgebra

def StoneSpace (B : Type _) [BooleanAlgebra B] := Ultrafilter B

def StoneBasicOpen {B : Type _} [BooleanAlgebra B] (b : B) :
  Set (Ultrafilter B) :=
  { F | {b} ∈ F.toFilter }
