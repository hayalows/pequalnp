import Mathlib

def netCircuit (x0 x1 x2 x3 x4 x5 : Bool) : Bool :=
  let w6 := x1 || x2
  let w7 := x0 || x2
  let w8 := x1 || x3
  let w9 := w7 && w8
  let w10 := w6 && w9
  let w11 := w6 || x5
  let w12 := x4 && w11
  w10 || w12

def netEdges (x0 x1 x2 x3 x4 x5 : Bool) : Bool :=
  (x0 && x1) || (x1 && x2) || (x2 && x3) ||
  (x1 && x4) || (x2 && x4) || (x4 && x5)

theorem netCircuit_matches : ∀ a b c d e f : Bool,
    netCircuit a b c d e f = netEdges a b c d e f := by decide

theorem proposed_counts : ¬ ((6 : Nat) + 2 * 3 ≤ 3 + 4 + 2 * 1 + 2) := by decide
