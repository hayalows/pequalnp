import PEqualNP.Defs.CircuitLowerBounds

open PEqualNP.CircuitLowerBounds

namespace CircuitPatch

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def constantGate (b : Bool) : Gate :=
  if b then ⟨.and, []⟩ else ⟨.or, []⟩

theorem constantGate_step (w : List Bool) (b : Bool) :
    step w (constantGate b) = w ++ [b] := by
  cases b <;> rfl

theorem patch_wires (pre post : List Gate) (g : Gate) (out : Nat)
    (x : List Bool) (b : Bool)
    (h : g.op.eval (g.inputs.map fun i => (pre.foldl step x).getD i false) = b) :
    (Circuit.mk (pre ++ g :: post) out).wires x =
      (Circuit.mk (pre ++ constantGate b :: post) out).wires x := by
  change (pre ++ g :: post).foldl step x = (pre ++ constantGate b :: post).foldl step x
  simp only [List.foldl_append, List.foldl_cons, constantGate_step]
  have hs : step (pre.foldl step x) g = pre.foldl step x ++ [b] := by
    dsimp only [step] at h ⊢
    rw [h]
  rw [hs]

end CircuitPatch
