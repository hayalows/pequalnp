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

def pairExpansion (a b c d e : ℂ) : ℂ :=
  a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e

theorem coeff_two_mul (p q : ℂ[X]) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map]
  simp [Finset.sum_range_succ]
  rfl

theorem coeff_two_five (a b c d e : ℂ) :
    ((1 + C a * X) * ((1 + C b * X) * ((1 + C c * X) *
      ((1 + C d * X) * (1 + C e * X))))).coeff 2 = pairExpansion a b c d e := by
  simp only [coeff_two_mul, mul_coeff_one, mul_coeff_zero, coeff_add, coeff_C_mul]
  norm_num [coeff_one, coeff_X, pairExpansion]
  ring

abbrev Tuple5 := Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5

def tuple5 : Tuple5 ≃ (Fin 5 → Fin 5) where
  toFun z := ![z.1,z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2]
  invFun f := (f 0,f 1,f 2,f 3,f 4)
  left_inv _ := rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

abbrev distinct5 (a b c d e : Fin 5) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
  c ≠ d ∧ c ≠ e ∧ d ≠ e

theorem tuple5_injective (a b c d e : Fin 5) :
    Function.Injective (tuple5 (a,b,c,d,e)) ↔ distinct5 a b c d e := by
  constructor
  · intro h
    exact ⟨fun he => (by decide : (0 : Fin 5) ≠ 1) (h he),
      fun he => (by decide : (0 : Fin 5) ≠ 2) (h he),
      fun he => (by decide : (0 : Fin 5) ≠ 3) (h he),
      fun he => (by decide : (0 : Fin 5) ≠ 4) (h he),
      fun he => (by decide : (1 : Fin 5) ≠ 2) (h he),
      fun he => (by decide : (1 : Fin 5) ≠ 3) (h he),
      fun he => (by decide : (1 : Fin 5) ≠ 4) (h he),
      fun he => (by decide : (2 : Fin 5) ≠ 3) (h he),
      fun he => (by decide : (2 : Fin 5) ≠ 4) (h he),
      fun he => (by decide : (3 : Fin 5) ≠ 4) (h he)⟩
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      simp [tuple5] at hij
      tauto

theorem sum_embeddings5 (g : (Fin 5 → Fin 5) → ℂ) :
    (∑ f : Fin 5 ↪ Fin 5, g f) =
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, if distinct5 a b c d e then g (tuple5 (a,b,c,d,e)) else 0 := by
  classical
  let E := Equiv.subtypeInjectiveEquivEmbedding (Fin 5) (Fin 5)
  calc
    _ = ∑ f : {f : Fin 5 → Fin 5 // Function.Injective f}, g f := (E.sum_comp (fun x => g x)).symm
    _ = ∑ f : Fin 5 → Fin 5, if Function.Injective f then g f else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype _ (by simp) g).symm
    _ = ∑ p : Tuple5, if Function.Injective (tuple5 p) then g (tuple5 p) else 0 :=
      (tuple5.sum_comp (fun x => if Function.Injective x then g x else 0)).symm
    _ = _ := by simp only [Fintype.sum_prod_type, tuple5_injective]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 30000 in
theorem secondCoefficient (t : Mat) : (levelPolynomial t).coeff 2 = 3 * form t t := by
  classical
  rw [levelPolynomial, Polynomial.finsetSum_coeff]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, coeff_two_five]
  change (∑ f : Fin 5 ↪ Fin 5, (fun g : Fin 5 → Fin 5 =>
    pairExpansion (t (0,g 0)) (t (1,g 1)) (t (2,g 2)) (t (3,g 3)) (t (4,g 4))) f) = _
  rw [sum_embeddings5 (fun g : Fin 5 → Fin 5 =>
    pairExpansion (t (0,g 0)) (t (1,g 1)) (t (2,g 2)) (t (3,g 3)) (t (4,g 4)))]
  simp (config := { maxSteps := 300000 }) +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, distinct5, tuple5,
    Equiv.coe_fn_mk, form, total, row, col]
  simp [pairExpansion]
  ring

theorem weakerOfficialBound (L : Submodule ℂ Mat)
    (hL : ∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) :
    Module.finrank ℂ L ≤ 12 := by
  apply finrank_of_isotropic L
  intro t ht
  have h := congrArg (fun p : ℂ[X] => p.coeff 2) (levelPolynomial_eq hL ht)
  rw [secondCoefficient, Polynomial.coeff_C_of_ne_zero (by decide : (2 : ℕ) ≠ 0)] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end LevelCoefficients
