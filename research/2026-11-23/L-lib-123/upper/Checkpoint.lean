import Mathlib
import PEqualNP.Defs

namespace EvasionCheckpoint

open Function

theorem iteratedBlocks {Cfg Witness : Type*} (step : Cfg → Cfg) (r b : ℕ)
    (verify : Cfg → Cfg → Witness → Prop)
    (hverify : ∀ x y, (∃ w, verify x y w) ↔ step^[b] x = y)
    (x y : Cfg) :
    (∃ checkpoints : ℕ → Cfg, checkpoints 0 = x ∧ checkpoints r = y ∧
      ∀ i < r, ∃ w, verify (checkpoints i) (checkpoints (i + 1)) w) ↔
    step^[r * b] x = y := by
  constructor
  · rintro ⟨c, h₀, hᵣ, hc⟩
    have agree (i : ℕ) (hi : i ≤ r) : step^[i * b] x = c i := by
      induction i with
      | zero => simpa using h₀.symm
      | succ i ih =>
        have hi' : i < r := hi
        rw [Nat.succ_mul, Nat.add_comm, iterate_add_apply, ih (Nat.le_of_lt hi')]
        exact (hverify (c i) (c (i + 1))).mp (hc i hi')
    exact (agree r le_rfl).trans hᵣ
  · intro h
    refine ⟨fun i => step^[i * b] x, by simp, h, ?_⟩
    intro i _
    apply (hverify _ _).mpr
    change step^[b] (step^[i * b] x) = step^[(i + 1) * b] x
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, iterate_add_apply]

theorem balancedExponents (m p q s : ℕ) (hpq : p ≤ q) (hbudget : q + s ≤ 2 * p) :
    let r := 2 ^ ((q - p) * m)
    let b := 2 ^ (p * m)
    r * b = 2 ^ (q * m) ∧
      (r + 1) * 2 ^ (s * m) + b ≤ 3 * 2 ^ (p * m) := by
  have h₁ : q - p + p = q := Nat.sub_add_cancel hpq
  have h₂ : (q - p) + s ≤ p := by omega
  have h₃ : s ≤ p := by omega
  simp only
  constructor
  · rw [← pow_add, ← Nat.add_mul, h₁]
  · have hprod : 2 ^ ((q - p) * m) * 2 ^ (s * m) ≤ 2 ^ (p * m) := by
      rw [← pow_add, ← Nat.add_mul]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right m h₂)
    have hs : 2 ^ (s * m) ≤ 2 ^ (p * m) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right m h₃)
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem noCheckpointPowerSaving (a p q : ℕ) (h : a + q ≤ p) : q ≤ p := by
  omega

theorem fixedEndpointPadding {Cfg : Type*} (step : Cfg → Cfg) (x y : Cfg)
    (t extra : ℕ) (run : step^[t] x = y) (fixed : step y = y) :
    step^[extra + t] x = y := by
  rw [iterate_add_apply, run]
  induction extra with
  | zero => rfl
  | succ extra ih => rw [iterate_succ_apply, fixed, ih]

end EvasionCheckpoint
