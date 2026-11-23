import PEqualNP.Defs

namespace FP3Audit

open PEqualNP.Library

theorem alt_three_exact (s : ℕ) (P : List Bool → Prop) :
    Alt 3 s P ↔
      ∃ a : List Bool, a.length = s ∧
        ∀ b : List Bool, b.length = s →
          ∃ c : List Bool, c.length = s ∧ P (a ++ b ++ c) := by
  classical
  simp [Alt, List.append_assoc]

theorem alt_two_exact (s : ℕ) (P : List Bool → Prop) :
    Alt 2 s P ↔
      ∃ a : List Bool, a.length = s ∧
        ∀ b : List Bool, b.length = s → P (a ++ b) := by
  classical
  simp [Alt]

theorem alt_three_constant (s : ℕ) (P : Prop) :
    Alt 3 s (fun _ => P) ↔ P := by
  rw [alt_three_exact]
  constructor
  · rintro ⟨a, ha, hab⟩
    obtain ⟨c, hc, hp⟩ := hab (List.replicate s false) (by simp)
    exact hp
  · intro hp
    exact ⟨List.replicate s false, by simp, fun _ _ => ⟨List.replicate s false, by simp, hp⟩⟩

theorem three_blocks_length (s : ℕ) (a b c : List Bool)
    (ha : a.length = s) (hb : b.length = s) (hc : c.length = s) :
    (a ++ b ++ c).length = 3 * s := by
  simp [ha, hb, hc]
  omega

theorem pair_length (x a b c : List Bool) (s : ℕ)
    (ha : a.length = s) (hb : b.length = s) (hc : c.length = s) :
    (encodePair (x, a ++ b ++ c)).length = x.length + 3 * s := by
  simp [encodePair, ha, hb, hc]
  omega

theorem exponent_gap (p q K : ℕ) (hpq : p < q) :
    ∃ n : ℕ, K * 2 ^ (p * n) + K < 2 ^ (q * n) := by
  let n := 2 * K + 1
  refine ⟨n, ?_⟩
  have hpow : 2 * K < 2 ^ n := by
    have : n < 2 ^ n := n.lt_two_pow_self
    omega
  have hp₁ : 1 ≤ 2 ^ (p * n) := Nat.one_le_two_pow
  have hmul := Nat.mul_le_mul_left K hp₁
  have hpow' := Nat.mul_lt_mul_of_pos_right hpow (by positivity : 0 < 2 ^ (p * n))
  calc
    K * 2 ^ (p * n) + K ≤ 2 * K * 2 ^ (p * n) := by nlinarith
    _ < 2 ^ n * 2 ^ (p * n) := hpow'
    _ = 2 ^ ((p + 1) * n) := by rw [← pow_add]; congr 1; ring
    _ ≤ 2 ^ (q * n) := Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right n (by omega))

theorem positive_rung (p q : ℕ) (hpq : p < q) :
    ∃ u v : ℕ, 1 ≤ v ∧ v < u ∧ p * u ^ 3 < q * v ^ 3 := by
  let v := 7 * p + 1
  have hv : 1 ≤ v := by omega
  refine ⟨v + 1, v, hv, by omega, ?_⟩
  have hv2 : v ≤ v ^ 2 := by nlinarith
  have hv2' : 1 ≤ v ^ 2 := hv.trans hv2
  have h₀ : 3 * v ^ 2 + 3 * v + 1 ≤ 7 * v ^ 2 := by omega
  have hvp : 7 * p < v := by omega
  have hpos : 0 < v ^ 2 := by positivity
  calc
    p * (v + 1) ^ 3 = p * v ^ 3 + p * (3 * v ^ 2 + 3 * v + 1) := by ring
    _ ≤ p * v ^ 3 + p * (7 * v ^ 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left p h₀) _
    _ = p * v ^ 3 + (7 * p) * v ^ 2 := by ring
    _ < p * v ^ 3 + v * v ^ 2 :=
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hvp hpos) _
    _ = (p + 1) * v ^ 3 := by ring
    _ ≤ q * v ^ 3 := Nat.mul_le_mul_right _ (by omega)

theorem long_query_growth (p K A past : ℕ) (hp : 1 ≤ p) :
    ∃ n : ℕ, n % 2 = 0 ∧ past < 2 ^ (p * n + n / 2) ∧
      A * (n + 3 * (K * 2 ^ (p * n) + K)) + A < 2 ^ (p * n + n / 2) := by
  let C := A * (6 * K + 2)
  let m := past + C + 1
  let n := 2 * m
  let X : ℕ := 2 ^ (p * n)
  have hX : 1 ≤ X := Nat.one_le_two_pow
  have hnm : n / 2 = m := by simp [n]
  have hXn : n ≤ X :=
    n.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  have hscope : A * (n + 3 * (K * X + K)) + A ≤ C * X := by
    have h : n + 3 * (K * X + K) + 1 ≤ (6 * K + 2) * X := by
      have hk := Nat.mul_le_mul_left K hX
      nlinarith
    have hA := Nat.mul_le_mul_left A h
    dsimp [C]
    nlinarith only [hA]
  have hm : m < 2 ^ m := m.lt_two_pow_self
  have hC : C < 2 ^ m := by omega
  have hpast : past < 2 ^ m := by omega
  have ht : 2 ^ (p * n + n / 2) = X * 2 ^ m := by rw [hnm, pow_add]
  refine ⟨n, by simp [n], ?_, ?_⟩
  · rw [ht]
    exact hpast.trans_le (by simpa using Nat.mul_le_mul_right (2 ^ m) hX)
  · change A * (n + 3 * (K * X + K)) + A < _
    rw [ht, mul_comm X]
    exact hscope.trans_lt (Nat.mul_lt_mul_of_pos_right hC (by omega))

end FP3Audit
