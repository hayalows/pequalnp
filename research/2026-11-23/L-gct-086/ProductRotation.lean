import Mathlib

open Finset

namespace ProductRotation

theorem kill_products {n : ℕ} (roots : List ℂ) :
    ∀ (V : Submodule ℂ (Fin n → ℂ)) (v : Fin n → ℂ),
      (∀ r ∈ roots, r ≠ 0) → roots.length ≤ Module.finrank ℂ V →
      ∃ w ∈ V, ∀ r ∈ roots, ∃ j : Fin n, 1 + r * (v + w) j = 0 := by
  induction roots with
  | nil =>
    intro V v _ _
    exact ⟨0, V.zero_mem, by simp⟩
  | cons r roots ih =>
    intro V v hr hdim
    have hr0 := hr r List.mem_cons_self
    have hne : V ≠ ⊥ := by
      intro h
      rw [h, finrank_bot, List.length_cons] at hdim
      omega
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra! h
      exact hx0 (funext h)
    let ev : Module.Dual ℂ V := (LinearMap.proj j).comp V.subtype
    have hev : ev ≠ 0 := by
      intro h
      exact hj (congrArg (fun f : Module.Dual ℂ V => f ⟨x,hx⟩) h)
    let K := LinearMap.ker ev
    let W := K.map V.subtype
    have hW : Module.finrank ℂ W + 1 = Module.finrank ℂ V := by
      rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective V.subtype
        V.injective_subtype K)]
      exact Module.Dual.finrank_ker_add_one_of_ne_zero hev
    let c := (-1 - r * v j) / (r * x j)
    let u := c • x
    have hu : u ∈ V := V.smul_mem c hx
    have hkill : 1 + r * (v + u) j = 0 := by
      simp only [Pi.add_apply, u, Pi.smul_apply, smul_eq_mul, c]
      field_simp
      ring
    obtain ⟨y, hy, hrest⟩ := ih W (v+u) (fun s hs => hr s (List.mem_cons_of_mem _ hs)) (by
      simp only [List.length_cons] at hdim
      omega)
    have hyV : y ∈ V := by
      obtain ⟨x, _, rfl⟩ := hy
      exact x.property
    have hyj : y j = 0 := by
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx
    refine ⟨u+y, V.add_mem hu hyV, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · refine ⟨j, ?_⟩
      simpa [Pi.add_apply, hyj] using hkill
    · obtain ⟨k,hk⟩ := hrest s hs
      exact ⟨k, by simpa [add_assoc] using hk⟩

theorem dimension_lt_number_of_products {n m : ℕ} (r a : Fin m → ℂ)
    (hr : ∀ i, r i ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ v ∈ V, (∑ i, a i * ∏ j, (1 + r i * v j)) = c) :
    Module.finrank ℂ V < m := by
  by_contra! h
  let roots := List.ofFn r
  have hr' : ∀ s ∈ roots, s ≠ 0 := by
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    exact hr i
  obtain ⟨w, hw, hwzero⟩ := kill_products roots V 0 hr' (by simpa [roots] using h)
  apply hc
  rw [← hV w hw]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨j,hj⟩ := hwzero (r i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simpa using hj), mul_zero]

end ProductRotation
