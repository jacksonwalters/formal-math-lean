import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice  -- This provides the ⋃ notation
import Mathlib.Order.Filter.Ultrafilter.Defs

open Set
open Filter

namespace AtomlessBooleanAlgebra

def Cantor := ℕ → Bool

def BitString (n : ℕ) := Fin n → Bool

def cylinder {n : ℕ} (s : BitString n) : Set Cantor :=
  { x | ∀ i : Fin n, x i = s i }

def CountableAtomlessBA : Set (Set Cantor) :=
  { A | ∃ (S : Finset (Σ n : ℕ, BitString n)),
    A = ⋃ p ∈ S, cylinder p.2 }

def StoneSpace (B : Type _) [BooleanAlgebra B] := Ultrafilter B

def StoneBasicOpen {B : Type _} [BooleanAlgebra B] (b : B) :
  Set (Ultrafilter B) :=
  { F | {b} ∈ F.toFilter }

end AtomlessBooleanAlgebra
