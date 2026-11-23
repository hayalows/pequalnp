import Mathlib
import PEqualNP.Defs

open Finset Polynomial

namespace LevelCoefficients

abbrev Mat := Fin 5 × Fin 5 → ℂ

noncomputable def levelPolynomial (t : Mat) : ℂ[X] :=
  ∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + C (t (i, f i)) * X)

theorem levelPolynomial_eq {L : Submodule ℂ Mat}
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    {t : Mat} (ht : t ∈ L) :
    levelPolynomial t = C 120 := by
  apply Polynomial.funext
  intro z
  rw [levelPolynomial, eval_finsetSum, eval_C]
  simp only [eval_prod, eval_add, eval_one, eval_mul_X, eval_C]
  have hz := hL (z • t) (L.smul_mem z ht)
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  simp_rw [mul_comm _ z]
  exact hz

theorem coefficient_formula (t : Mat) (k : ℕ) :
    (levelPolynomial t).coeff k =
      ∑ f : Fin 5 ↪ Fin 5, ∑ s : Finset (Fin 5),
        if s.card = k then ∏ i ∈ s, t (i, f i) else 0 := by
  classical
  unfold levelPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.prod_one_add, Polynomial.finsetSum_coeff]
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  by_cases h : s.card = k
  · subst k
    simp
  · simp [h, Ne.symm h]

theorem positive_coefficient_zero {L : Submodule ℂ Mat}
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    {t : Mat} (ht : t ∈ L) {k : ℕ} (hk : 0 < k) :
    (∑ f : Fin 5 ↪ Fin 5, ∑ s : Finset (Fin 5),
        if s.card = k then ∏ i ∈ s, t (i, f i) else 0) = 0 := by
  rw [← coefficient_formula, levelPolynomial_eq hL ht]
  exact Polynomial.coeff_C_of_ne_zero hk.ne'

noncomputable def row (t : Mat) (i : Fin 5) : ℂ := ∑ j, t (i, j)
noncomputable def col (t : Mat) (j : Fin 5) : ℂ := ∑ i, t (i, j)
noncomputable def total (t : Mat) : ℂ := ∑ i, row t i

theorem total_col (t : Mat) : total t = ∑ j, col t j := by
  exact Finset.sum_comm

noncomputable def form (t u : Mat) : ℂ :=
  total t * total u - (∑ i, row t i * row u i) - (∑ j, col t j * col u j)
    + ∑ i : Fin 5, ∑ j : Fin 5, t (i, j) * u (i, j)

noncomputable def hessian : LinearMap.BilinForm ℂ Mat :=
  LinearMap.mk₂ ℂ form
    (by
      intro t u v
      simp only [form, total, row, col, Pi.add_apply, Finset.sum_add_distrib, add_mul]
      ring)
    (by
      intro c t u
      simp only [form, total, row, col, Pi.smul_apply, smul_eq_mul, mul_assoc,
        ← Finset.mul_sum]
      ring)
    (by
      intro t u v
      simp only [form, total, row, col, Pi.add_apply, Finset.sum_add_distrib, mul_add]
      ring)
    (by
      intro c t u
      simp only [form, total, row, col, Pi.smul_apply, smul_eq_mul,
        mul_left_comm _ c, ← Finset.mul_sum]
      ring)

theorem form_symm (t u : Mat) : form t u = form u t := by
  unfold form
  simp_rw [mul_comm]

def testEntry (i j : Fin 5) : Mat := fun ab =>
  if ab.1 = i then if ab.2 = j then 1 else 0 else 0

theorem form_testEntry (t : Mat) (i j : Fin 5) :
    form t (testEntry i j) = total t - row t i - col t j + t (i,j) := by
  classical
  have hr (a : Fin 5) : row (testEntry i j) a = if a = i then 1 else 0 := by
    by_cases h : a = i <;> simp [row, testEntry, h]
  have hc (b : Fin 5) : col (testEntry i j) b = if b = j then 1 else 0 := by
    by_cases h : b = j <;> simp [col, testEntry, h]
  unfold form total
  simp only [hr, hc, testEntry, mul_ite, mul_one, mul_zero, sum_ite_eq',
    mem_univ, ite_true]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro a _ hai
    simp [hai]
  · simp

theorem form_separates (t : Mat) (h : ∀ u : Mat, form t u = 0) : t = 0 := by
  have hp (i j : Fin 5) : t (i,j) = row t i + col t j - total t := by
    have hj := h (testEntry i j)
    rw [form_testEntry] at hj
    linear_combination hj
  have hr (i : Fin 5) : row t i = total t := by
    have hs : row t i = 5 * row t i + (∑ j, col t j) - 5 * total t := by
      conv_lhs => unfold row
      simp_rw [hp, sum_sub_distrib, sum_add_distrib, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [← total_col] at hs
    linear_combination -hs/4
  have ht : total t = 0 := by
    have hsum : total t = 5 * total t := by
      conv_lhs => unfold total
      simp [hr, Finset.sum_const, nsmul_eq_mul]
    linear_combination -hsum/4
  have hc (j : Fin 5) : col t j = 0 := by
    have he : col t j = 5 * col t j := by
      conv_lhs => unfold col
      simp_rw [hp, hr, ht, zero_add, sub_zero, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    linear_combination -he/4
  funext ⟨i,j⟩
  simp [hp, hr, ht, hc]

theorem hessian_nondegenerate : hessian.Nondegenerate := by
  constructor
  · exact form_separates
  · intro u hu
    apply form_separates u
    intro t
    rw [form_symm]
    exact hu t

set_option maxHeartbeats 1000000 in
theorem finrank_of_isotropic (L : Submodule ℂ Mat) (hL : ∀ t ∈ L, form t t = 0) :
    Module.finrank ℂ L ≤ 12 := by
  have hh : L ≤ hessian.orthogonal L := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro t ht
    have he := hL (t + u) (L.add_mem ht hu)
    change hessian (t + u) (t + u) = 0 at he
    simp only [map_add, LinearMap.add_apply] at he
    change form t t + form u t + (form t u + form u u) = 0 at he
    rw [hL t ht, hL u hu, form_symm u t] at he
    change form t u = 0
    linear_combination he/2
  have hdim := Submodule.finrank_mono hh
  rw [LinearMap.BilinForm.finrank_orthogonal hessian_nondegenerate,
    Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    ] at hdim
  omega


theorem zero_rectangle_impossible {L : Submodule ℂ Mat}
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120)
    {t : Mat} (ht : t ∈ L) (R S : Finset (Fin 5)) (hRS : 5 < R.card + S.card) :
    ¬ ∀ i ∈ R, ∀ j ∈ S, t (i,j) = -1 := by
  classical
  intro hz
  have hp : (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 0 := by
    apply Finset.sum_eq_zero
    intro f _
    have hhit : ¬ Disjoint (R.map f) S := by
      intro hd
      have hc := Finset.card_le_univ ((R.map f) ∪ S)
      rw [Finset.card_union_of_disjoint hd, Finset.card_map, Fintype.card_fin] at hc
      omega
    rcases Finset.not_disjoint_iff.mp hhit with ⟨j,hjR,hjS⟩
    rcases Finset.mem_map.mp hjR with ⟨i,hi,rfl⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz i hi _ hjS]; ring)
  have h := (hL t ht).symm.trans hp
  norm_num at h

end LevelCoefficients
