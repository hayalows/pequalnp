import Mathlib
import PEqualNP.Defs

open Finset Polynomial

namespace LevelHall

abbrev Mat (n : ℕ) := Fin n × Fin n → ℂ

theorem evalPermanent {n : ℕ} (z : Mat n) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ n) =
      ∑ σ : Equiv.Perm (Fin n), ∏ j, z (σ j, j) := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

noncomputable def linePolynomial {n : ℕ} (t : Mat n) : ℂ[X] :=
  ∑ σ : Equiv.Perm (Fin n), ∏ j, (1 + C (t (σ j, j)) * X)

theorem constant_linePolynomial {n : ℕ} {L : Submodule ℂ (Mat n)}
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p)
      (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ))
    {t : Mat n} (ht : t ∈ L) :
    linePolynomial t = C (Nat.factorial n : ℂ) := by
  apply Polynomial.funext
  intro z
  rw [linePolynomial, eval_finsetSum, eval_C]
  simp only [eval_prod, eval_add, eval_one, eval_mul_X, eval_C]
  have hz := hL (z • t) (L.smul_mem z ht)
  rw [evalPermanent] at hz
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  simp_rw [mul_comm _ z]
  exact hz

theorem coefficient_formula {n : ℕ} (t : Mat n) (k : ℕ) :
    (linePolynomial t).coeff k =
      ∑ σ : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
        if S.card = k then ∏ j ∈ S, t (σ j, j) else 0 := by
  classical
  rw [linePolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_one_add, Polynomial.finsetSum_coeff, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : S.card = k
  · subst k
    simp
  · simp [h, Ne.symm h]

theorem zero_rectangle_impossible {n : ℕ} {L : Submodule ℂ (Mat n)}
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p)
      (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ))
    {t : Mat n} (ht : t ∈ L) (R S : Finset (Fin n)) (hRS : n < R.card + S.card) :
    ¬ ∀ i ∈ R, ∀ j ∈ S, t (i,j) = -1 := by
  classical
  intro hz
  have hp : (∑ σ : Equiv.Perm (Fin n), ∏ j, (1 + t (σ j, j))) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    have hhit : ¬ Disjoint (S.map σ.toEmbedding) R := by
      intro hd
      have hc := Finset.card_le_univ ((S.map σ.toEmbedding) ∪ R)
      rw [Finset.card_union_of_disjoint hd, Finset.card_map, Fintype.card_fin] at hc
      omega
    rcases Finset.not_disjoint_iff.mp hhit with ⟨i,hiS,hiR⟩
    rcases Finset.mem_map.mp hiS with ⟨j,hj,rfl⟩
    change σ j ∈ R at hiR
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz _ hiR _ hj]; ring)
  have h := hL t ht
  rw [evalPermanent, hp] at h
  exact (Nat.cast_ne_zero.mpr n.factorial_ne_zero) h.symm

theorem row_invariance {n : ℕ} (ρ : Equiv.Perm (Fin n)) (t : Mat n) :
    linePolynomial (fun p => t (ρ p.1,p.2)) = linePolynomial t := by
  unfold linePolynomial
  exact Equiv.sum_comp (Equiv.mulLeft ρ) (fun σ => ∏ j, (1 + C (t (σ j,j)) * X))

theorem coefficient_smul {n : ℕ} (z : ℂ) (t : Mat n) (k : ℕ) :
    (linePolynomial (z • t)).coeff k = z^k * (linePolynomial t).coeff k := by
  rw [coefficient_formula, coefficient_formula, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : S.card = k
  · simp [h, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  · simp [h]

theorem coefficient_zero_of_row_eigenvector {n : ℕ} (ρ : Equiv.Perm (Fin n))
    (z : ℂ) (t : Mat n) (hz : z^k ≠ 1) (heig : ∀ i j, t (ρ i,j) = z * t (i,j)) :
    (linePolynomial t).coeff k = 0 := by
  have h : (fun p : Fin n × Fin n => t (ρ p.1,p.2)) = z • t := by
    funext ⟨i,j⟩
    exact heig i j
  have hi := row_invariance ρ t
  rw [h] at hi
  have hc := congrArg (fun p : ℂ[X] => p.coeff k) hi
  rw [coefficient_smul] at hc
  have hz' : z^k - 1 ≠ 0 := sub_ne_zero.mpr hz
  apply (mul_eq_zero.mp (show (z^k - 1) * (linePolynomial t).coeff k = 0 by
    linear_combination hc)).resolve_left hz'

noncomputable def sumCoordinates (n : ℕ) : Module.Dual ℂ (Fin n → ℂ) :=
  ∑ j, LinearMap.proj j

noncomputable abbrev Centered (n : ℕ) := LinearMap.ker (sumCoordinates n)

theorem centered_dim {n : ℕ} (hn : 0 < n) :
    Module.finrank ℂ (Centered n) = n - 1 := by
  classical
  have hne : sumCoordinates n ≠ 0 := by
    intro h
    let j : Fin n := ⟨0,hn⟩
    have hz := LinearMap.congr_fun h (Pi.single j 1)
    simp [sumCoordinates, LinearMap.sum_apply, Pi.single_apply] at hz
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  exact Nat.eq_sub_of_add_eq hdim

def rotateBlocks (r m : ℕ) : Equiv.Perm (Fin (r*m)) :=
  finProdFinEquiv.symm.trans (((Equiv.refl (Fin r)).prodCongr (finRotate m)).trans finProdFinEquiv)

noncomputable def lowMap (r m : ℕ) (z : ℂ) :
    (Fin r → Centered (r*m)) →ₗ[ℂ] Mat (r*m) where
  toFun p ij := z ^ (finProdFinEquiv.symm ij.1 : Fin r × Fin m).2.val *
    (p (finProdFinEquiv.symm ij.1 : Fin r × Fin m).1).val ij.2
  map_add' p q := by
    funext ⟨i,j⟩
    simp [mul_add]
  map_smul' c p := by
    funext ⟨i,j⟩
    simp [mul_left_comm]

theorem lowMap_injective (r m : ℕ) (hm : 0 < m) (z : ℂ) :
    Function.Injective (lowMap r m z) := by
  intro p q h
  funext i
  apply Subtype.ext
  funext j
  have hp := congrFun h (finProdFinEquiv (i, (⟨0,hm⟩ : Fin m)),j)
  change z ^ (finProdFinEquiv.symm (finProdFinEquiv (i, (⟨0,hm⟩ : Fin m)))).2.val *
    (p (finProdFinEquiv.symm (finProdFinEquiv (i, (⟨0,hm⟩ : Fin m)))).1).val j =
      z ^ (finProdFinEquiv.symm (finProdFinEquiv (i, (⟨0,hm⟩ : Fin m)))).2.val *
      (q (finProdFinEquiv.symm (finProdFinEquiv (i, (⟨0,hm⟩ : Fin m)))).1).val j at hp
  rw [Equiv.symm_apply_apply] at hp
  simpa using hp

theorem lowMap_eigenvector (r m : ℕ) (z : ℂ) (hm : 0 < m) (hz : z^m = 1)
    (p : Fin r → Centered (r*m)) (i j : Fin (r*m)) :
    lowMap r m z p (rotateBlocks r m i,j) = z * lowMap r m z p (i,j) := by
  let a : Fin r × Fin m := finProdFinEquiv.symm i
  have hrot : finProdFinEquiv.symm (rotateBlocks r m i) = (a.1, finRotate m a.2) := by
    simp [rotateBlocks, a]
  change z ^ (finProdFinEquiv.symm (rotateBlocks r m i) : Fin r × Fin m).2.val *
    (p (finProdFinEquiv.symm (rotateBlocks r m i) : Fin r × Fin m).1).val j =
      z * (z ^ a.2.val * (p a.1).val j)
  rw [hrot]
  have hp (b : Fin m) : z ^ (finRotate m b).val = z * z ^ b.val := by
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [coe_finRotate]
    split_ifs with h
    · subst b
      simpa [pow_succ', Nat.succ_eq_add_one] using (hz.symm : (1 : ℂ) = z ^ (l+1))
    · rw [pow_succ']
  rw [hp, mul_assoc]

theorem low_order_large_centered (r m : ℕ) (hr : 0 < r) (hm : 1 < m) :
    ∃ L : Submodule ℂ (Mat (r*m)),
      Module.finrank ℂ L = r * (r*m - 1) ∧
      (∀ t ∈ L, (∀ i, ∑ j, t (i,j) = 0) ∧ (∀ j, ∑ i, t (i,j) = 0)) ∧
      (∀ t ∈ L, ∀ k, 0 < k → k < m → (linePolynomial t).coeff k = 0) := by
  classical
  have hmpos : 0 < m := by omega
  let : NeZero m := ⟨hmpos.ne'⟩
  obtain ⟨z,hz⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ m
  let L := LinearMap.range (lowMap r m z)
  have hzne : z ≠ 1 := by
    intro h
    have hd := (hz.pow_eq_one_iff_dvd 1).mp (by simp [h])
    exact (by omega : ¬ m ≤ 1) (Nat.le_of_dvd (by decide) hd)
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (lowMap_injective r m hmpos z),
      Module.finrank_pi_fintype, centered_dim (Nat.mul_pos hr hmpos)]
    simp
  · rintro _ ⟨p,rfl⟩
    constructor
    · intro i
      unfold lowMap
      change (∑ j, z ^ (finProdFinEquiv.symm i : Fin r × Fin m).2.val *
        (p (finProdFinEquiv.symm i : Fin r × Fin m).1).val j) = 0
      rw [← Finset.mul_sum]
      have hc := (p (finProdFinEquiv.symm i : Fin r × Fin m).1).property
      change sumCoordinates (r*m) _ = 0 at hc
      simp only [sumCoordinates, LinearMap.sum_apply, LinearMap.proj_apply] at hc
      rw [hc, mul_zero]
    · intro j
      have he := Equiv.sum_comp (rotateBlocks r m) (fun i => lowMap r m z p (i,j))
      simp only [lowMap_eigenvector r m z hmpos hz.pow_eq_one, ← Finset.mul_sum] at he
      have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hzne
      exact (mul_eq_zero.mp (show (z - 1) * (∑ i, lowMap r m z p (i,j)) = 0 by
        linear_combination he)).resolve_left hz'
  · rintro _ ⟨p,rfl⟩ k hk hkm
    refine coefficient_zero_of_row_eigenvector (rotateBlocks r m) z _ ?_
      (lowMap_eigenvector r m z hmpos hz.pow_eq_one p)
    intro he
    exact (Nat.not_le.mpr hkm) (Nat.le_of_dvd hk ((hz.pow_eq_one_iff_dvd k).mp he))

theorem no_fixed_order_linear_bound (c k : ℕ) :
    ∃ (n : ℕ) (L : Submodule ℂ (Mat n)), c * n < Module.finrank ℂ L ∧
      (∀ t ∈ L, (∀ i, ∑ j, t (i,j) = 0) ∧ (∀ j, ∑ i, t (i,j) = 0)) ∧
      (∀ t ∈ L, ∀ j, 0 < j → j ≤ k → (linePolynomial t).coeff j = 0) := by
  let r := c + 2
  let m := k + 2
  obtain ⟨L,hd,hcent,hvanish⟩ := low_order_large_centered r m (by dsimp [r]; omega)
    (by dsimp [m]; omega)
  refine ⟨r*m,L,?_,hcent,fun t ht j hj hjk => hvanish t ht j hj (by dsimp [m]; omega)⟩
  rw [hd, Nat.mul_sub_left_distrib, Nat.mul_one]
  have hrn : r ≤ r*m := by
    calc
      r = r * 1 := (Nat.mul_one _).symm
      _ ≤ r*m := Nat.mul_le_mul_left _ (by dsimp [m]; omega)
  have hpos : 0 < r := by dsimp [r]; omega
  have he : r * (r*m) = c * (r*m) + (r*m) + (r*m) := by
    conv_lhs => rw [show r = c + 2 from rfl]
    ring
  rw [he]
  omega

end LevelHall
