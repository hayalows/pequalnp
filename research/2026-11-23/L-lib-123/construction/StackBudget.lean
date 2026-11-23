import Mathlib
import PEqualNP.Defs

namespace FP3Audit

open Turing Turing.TM2

universe u v w z

variable {K : Type u} [DecidableEq K] {Γ : K → Type v} {Λ : Type w} {σ : Type z}

def pushBudget (q : Stmt Γ Λ σ) : ℕ :=
  match q with
  | .push _ _ b => pushBudget b + 1
  | .pop _ _ b | .peek _ _ b | .load _ b => pushBudget b
  | .branch _ b c => max (pushBudget b) (pushBudget c)
  | .goto _ | .halt => 0

theorem stepAux_length (q : Stmt Γ Λ σ) (s : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((stepAux q s S).stk k).length ≤ (S k).length + pushBudget q := by
  induction q generalizing s S with
  | push j f b ih =>
    simp only [stepAux, pushBudget]
    apply (ih s (Function.update S j (f s :: S j))).trans
    by_cases hkj : k = j
    · subst k
      rw [Function.update_self, List.length_cons]
      omega
    · rw [Function.update_of_ne hkj]
      omega
  | pop j f b ih =>
    simp only [stepAux, pushBudget]
    apply (ih _ (Function.update S j (S j).tail)).trans
    by_cases hkj : k = j
    · subst k
      rw [Function.update_self]
      simp
    · rw [Function.update_of_ne hkj]
  | peek j f b ih | load f b ih =>
    simp only [stepAux, pushBudget]
    exact ih _ S
  | branch f b c ihb ihc =>
    cases hf : f s
    · simp only [stepAux, pushBudget, hf, Bool.cond_false]
      exact (ihc s S).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · simp only [stepAux, pushBudget, hf, Bool.cond_true]
      exact (ihb s S).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f | halt => simp [stepAux, pushBudget]

theorem finTM2_step_length (M : FinTM2) : ∃ B : ℕ,
    ∀ c c' : M.Cfg, M.step c = some c' → ∀ k,
      (c'.stk k).length ≤ (c.stk k).length + B := by
  let _ : DecidableEq M.K := M.kDecidableEq
  let _ : Fintype M.Λ := M.ΛFin
  refine ⟨Finset.univ.sup (fun l : M.Λ => pushBudget (M.m l)), ?_⟩
  intro c c' hstep k
  rcases c with ⟨l, s, S⟩
  cases l with
  | none => simp [FinTM2.step, TM2.step] at hstep
  | some l =>
    simp only [FinTM2.step, TM2.step] at hstep
    have hc : stepAux (M.m l) s S = c' := Option.some.inj hstep
    subst c'
    have hb : pushBudget (M.m l) ≤ Finset.univ.sup (fun z : M.Λ => pushBudget (M.m z)) :=
      Finset.le_sup (f := fun z : M.Λ => pushBudget (M.m z)) (Finset.mem_univ l)
    exact (stepAux_length (M.m l) s S k).trans (Nat.add_le_add_left hb _)

end FP3Audit
