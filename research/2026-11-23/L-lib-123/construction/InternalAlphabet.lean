import Mathlib
import PEqualNP.Defs

namespace FP3Audit

open Turing Turing.TM2

universe u v w z

variable {K : Type u} [DecidableEq K] {Γ : K → Type v} {Λ : Type w} {σ : Type z}

def generated (q : Stmt Γ Λ σ) (k : K) : Set (Γ k) :=
  match q with
  | .push j f b =>
    if h : k = j then Set.range (fun s => cast (congrArg Γ h.symm) (f s)) ∪ generated b k
    else generated b k
  | .pop _ _ b | .peek _ _ b | .load _ b => generated b k
  | .branch _ b c => generated b k ∪ generated c k
  | .goto _ | .halt => ∅

theorem finite_generated [Finite σ] (q : Stmt Γ Λ σ) (k : K) :
    (generated q k).Finite := by
  induction q with
  | push j f b ih =>
    simp only [generated]
    split_ifs
    · exact (Set.finite_range _).union ih
    · exact ih
  | pop j f b ih | peek j f b ih | load f b ih => exact ih
  | branch f b c ihb ihc => exact ihb.union ihc
  | goto f | halt => exact Set.finite_empty

theorem stepAux_preserves (q : Stmt Γ Λ σ) (F : ∀ k, Set (Γ k))
    (hF : ∀ k, generated q k ⊆ F k)
    (s : σ) (S : ∀ k, List (Γ k))
    (hS : ∀ k a, a ∈ S k → a ∈ F k) :
    ∀ k a, a ∈ (stepAux q s S).stk k → a ∈ F k := by
  induction q generalizing s S with
  | push j f b ih =>
    have hb : ∀ k, generated b k ⊆ F k := by
      intro k a ha
      apply hF k
      simp only [generated]
      split_ifs
      · exact Or.inr ha
      · exact ha
    simp only [stepAux]
    apply ih hb
    intro k a ha
    by_cases hkj : k = j
    · subst k
      rw [Function.update_self] at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · apply hF j
        simp only [generated, cast_eq]
        exact Or.inl ⟨s, rfl⟩
      · exact hS j a ha
    · rw [Function.update_of_ne hkj] at ha
      exact hS k a ha
  | pop j f b ih =>
    simp only [stepAux]
    apply ih hF
    intro k a ha
    by_cases hkj : k = j
    · subst k
      rw [Function.update_self] at ha
      exact hS j a (List.tail_subset _ ha)
    · rw [Function.update_of_ne hkj] at ha
      exact hS k a ha
  | peek j f b ih | load f b ih =>
    simp only [stepAux]
    exact ih hF _ S hS
  | branch f b c ihb ihc =>
    cases hf : f s
    · simpa [stepAux, hf] using
        ihc (fun k a ha => hF k (Or.inr ha)) s S hS
    · simpa [stepAux, hf] using
        ihb (fun k a ha => hF k (Or.inl ha)) s S hS
  | goto f | halt => exact hS

noncomputable def machineAlphabet (M : FinTM2) (k : M.K) : Set (M.Γ k) :=
  letI : DecidableEq M.K := M.kDecidableEq
  (⋃ l : M.Λ, generated (M.m l) k) ∪ if k = M.k₀ then Set.univ else ∅

theorem machineAlphabet_finite (M : FinTM2) (k : M.K) : (machineAlphabet M k).Finite := by
  let _ : DecidableEq M.K := M.kDecidableEq
  let _ : Fintype M.Λ := M.ΛFin
  let _ : Fintype M.σ := M.σFin
  refine (Set.finite_iUnion fun l => finite_generated (M.m l) k).union ?_
  split_ifs with h
  · subst k
    let _ : Fintype (M.Γ M.k₀) := M.Γk₀Fin
    exact Set.finite_univ
  · exact Set.finite_empty

theorem initial_in_alphabet (M : FinTM2) (input : List (M.Γ M.k₀)) :
    ∀ k a, a ∈ (initList M input).stk k → a ∈ machineAlphabet M k := by
  let _ : DecidableEq M.K := M.kDecidableEq
  intro k a ha
  by_cases h : k = M.k₀
  · simp [machineAlphabet, h]
  · simp [initList, h] at ha

theorem step_closed (M : FinTM2) (c c' : M.Cfg) (hstep : M.step c = some c')
    (hc : ∀ k a, a ∈ c.stk k → a ∈ machineAlphabet M k) :
    ∀ k a, a ∈ c'.stk k → a ∈ machineAlphabet M k := by
  let _ : DecidableEq M.K := M.kDecidableEq
  rcases c with ⟨l, s, S⟩
  cases l with
  | none => simp [FinTM2.step, TM2.step] at hstep
  | some l =>
    simp only [FinTM2.step, TM2.step] at hstep
    have he : stepAux (M.m l) s S = c' := Option.some.inj hstep
    subst c'
    refine stepAux_preserves (M.m l) (machineAlphabet M) (fun k a ha => ?_) s S hc
    apply Set.mem_union_left
    exact Set.mem_iUnion.mpr ⟨l, ha⟩

theorem reachable_in_alphabet (M : FinTM2) (input : List (M.Γ M.k₀)) (c : M.Cfg)
    (h : Relation.ReflTransGen (fun a b => M.step a = some b) (initList M input) c) :
    ∀ k a, a ∈ c.stk k → a ∈ machineAlphabet M k := by
  induction h with
  | refl => exact initial_in_alphabet M input
  | tail h1 hs ih => exact step_closed M _ _ hs ih

end FP3Audit
