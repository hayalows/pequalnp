import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

def bowtie : Circuit := ⟨[
  ⟨.or, [1,2]⟩, ⟨.or, [3,4]⟩, ⟨.or, [5,6]⟩,
  ⟨.and, [0,7]⟩, ⟨.and, [1,2]⟩, ⟨.and, [3,4]⟩,
  ⟨.or, [9,10]⟩, ⟨.or, [8,11]⟩], 12⟩

def edgeBool (a b c d e : Bool) : Bool :=
  (a && b) || (a && c) || (b && c) || (a && d) || (a && e) || (d && e)

theorem witness_table : ∀ a b c d e : Bool,
    bowtie.eval [a,b,c,d,e] = edgeBool a b c d e := by decide

theorem witness_fanin : PEqualNP.MetaComplexity.Monotone2 bowtie := by
  simp [PEqualNP.MetaComplexity.Monotone2, bowtie]

def singletonSupport (j : Nat) : Nat :=
  (Finset.univ.filter fun u : Fin 5 =>
    (bowtie.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5+j) false = true).card

theorem supports : (List.range 8).map singletonSupport = [2,2,4,0,0,0,0,0] := by decide

theorem witness_weight : 3 + 3 + 2 * 2 = (10 : Nat) := by decide
