import Mathlib

-- Candidate proof for L-meta-452 (A redundant vector raises the rank above the number of essential vectors).
-- Source: pequalnp.com lemma L-meta-452 (Conjecture, 0 attempts as of 23 Nov 2026).
-- Status: Uncompiled Lean 4.36.0 + Mathlib draft; fast-path lint checked locally; ready for Codex compilation and checklemma.

theorem L_meta_452 :
    ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
      (∀ i, r i ≠ 0) →
      (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
      Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  intro k m r h_ne h_red
  classical
  rcases h_red with ⟨j, hj_red⟩
  let E : Set (Fin k) := {i : Fin k | r i ∉ Submodule.span ℚ (r '' {l | l ≠ i})}
  have hj_not_E : j ∉ E := fun h => h hj_red
  have hrj_not_span : r j ∉ Submodule.span ℚ (r '' E) := by
    intro hrj
    have h_img : r '' E = Set.range (fun i : ↥E => r i.1) := by
      ext y
      simp [E]
    rw [h_img, Submodule.mem_span_range_iff_exists_fun] at hrj
    rcases hrj with ⟨c, hc⟩
    have h_ex : ∃ i₀ : ↥E, c i₀ ≠ 0 := by
      by_contra h_all
      have h_zero : ∑ i : ↥E, c i • r i.1 = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hci : c i = 0 := by
          by_contra hne
          exact h_all ⟨i, hne⟩
        rw [hci, zero_smul]
      exact h_ne j (hc.symm.trans h_zero)
    rcases h_ex with ⟨i₀, hci₀⟩
    have h_split : c i₀ • r i₀.1 + ∑ i ∈ Finset.univ.erase i₀, c i • r i.1 = r j := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      exact hc
    have h_eq : r i₀.1 = (c i₀)⁻¹ • (r j - ∑ i ∈ Finset.univ.erase i₀, c i • r i.1) := by
      have h_sub : c i₀ • r i₀.1 = r j - ∑ i ∈ Finset.univ.erase i₀, c i • r i.1 :=
        eq_sub_of_add_eq h_split
      rw [← h_sub, inv_smul_smul₀ hci₀]
    have hj_ne : j ≠ i₀.1 := fun h => hj_not_E (h ▸ i₀.2)
    have hrj_mem : r j ∈ Submodule.span ℚ (r '' {l | l ≠ i₀.1}) :=
      Submodule.subset_span ⟨j, hj_ne, rfl⟩
    have hsum_mem :
        ∑ i ∈ Finset.univ.erase i₀, c i • r i.1 ∈ Submodule.span ℚ (r '' {l | l ≠ i₀.1}) := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨i.1, ?_, rfl⟩
      intro h_eq_val
      exact (Finset.ne_of_mem_erase hi) (Subtype.ext h_eq_val)
    have h_in : r i₀.1 ∈ Submodule.span ℚ (r '' {l | l ≠ i₀.1}) := by
      rw [h_eq]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hrj_mem hsum_mem)
    exact i₀.2 h_in
  have h_lin_E : LinearIndependent ℚ (fun i : ↥E => r i.1) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i₀
    by_contra hci₀
    have h_split : c i₀ • r i₀.1 + ∑ i ∈ Finset.univ.erase i₀, c i • r i.1 = 0 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      exact hc
    have h_eq : r i₀.1 = (c i₀)⁻¹ • (-(∑ i ∈ Finset.univ.erase i₀, c i • r i.1)) := by
      have h_neg : c i₀ • r i₀.1 = -(∑ i ∈ Finset.univ.erase i₀, c i • r i.1) :=
        eq_neg_of_add_eq_zero_left h_split
      rw [← h_neg, inv_smul_smul₀ hci₀]
    have hsum_mem :
        ∑ i ∈ Finset.univ.erase i₀, c i • r i.1 ∈ Submodule.span ℚ (r '' {l | l ≠ i₀.1}) := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨i.1, ?_, rfl⟩
      intro h_eq_val
      exact (Finset.ne_of_mem_erase hi) (Subtype.ext h_eq_val)
    have h_in : r i₀.1 ∈ Submodule.span ℚ (r '' {l | l ≠ i₀.1}) := by
      rw [h_eq]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hsum_mem)
    exact i₀.2 h_in
  let v : Option ↥E → (Fin m → ℚ) := fun x => Option.elim x (r j) (fun i => r i.1)
  have h_lin_v : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_option] at hc
    have hc_none : c none = 0 := by
      by_contra hcn
      have h_eq : r j = (c none)⁻¹ • (-(∑ i : ↥E, c (some i) • r i.1)) := by
        have h_neg : c none • r j = -(∑ i : ↥E, c (some i) • r i.1) :=
          eq_neg_of_add_eq_zero_left hc
        rw [← h_neg, inv_smul_smul₀ hcn]
      have hsum_mem : ∑ i : ↥E, c (some i) • r i.1 ∈ Submodule.span ℚ (r '' E) := by
        apply Submodule.sum_mem
        intro i _
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨i.1, i.2, rfl⟩
      have h_in : r j ∈ Submodule.span ℚ (r '' E) := by
        rw [h_eq]
        exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hsum_mem)
      exact hrj_not_span h_in
    have hc_some : ∀ i : ↥E, c (some i) = 0 := by
      rw [hc_none, zero_smul, zero_add] at hc
      exact (Fintype.linearIndependent_iff.mp h_lin_E) (fun i => c (some i)) hc
    intro x
    cases x with
    | none => exact hc_none
    | some i => exact hc_some i
  let W : Submodule ℚ (Fin m → ℚ) := Submodule.span ℚ (Set.range r)
  have hv_mem : ∀ x : Option ↥E, v x ∈ W := by
    intro x
    cases x with
    | none => exact Submodule.subset_span ⟨j, rfl⟩
    | some i => exact Submodule.subset_span ⟨i.1, rfl⟩
  let vW : Option ↥E → W := fun x => ⟨v x, hv_mem x⟩
  have h_lin_vW : LinearIndependent ℚ vW := h_lin_v.of_comp W.subtype
  have h_card : Fintype.card (Option ↥E) ≤ Module.finrank ℚ W :=
    h_lin_vW.fintype_card_le_finrank
  rw [Fintype.card_option] at h_card
  rw [Nat.card_eq_fintype_card]
  exact h_card
