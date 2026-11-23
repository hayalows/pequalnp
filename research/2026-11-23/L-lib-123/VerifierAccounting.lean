import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Evasion.MBudget
import PEqualNP.Library.Evasion.MTrans

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Evasion

namespace VerifierAccounting

theorem alt_three_iff (s : ℕ) (P : List Bool → Prop) :
    Alt 3 s P ↔ ∃ a : List Bool, a.length = s ∧
      ∀ b : List Bool, b.length = s →
        ∃ c : List Bool, c.length = s ∧ P (a ++ b ++ c) := by
  simp [Alt, List.append_assoc]

theorem alt_three_constant (s : ℕ) (P : Prop) :
    Alt 3 s (fun _ => P) ↔ P := by
  rw [alt_three_iff]
  constructor
  · rintro ⟨_, _, h⟩
    obtain ⟨_, _, hp⟩ := h (List.replicate s false) (by simp)
    exact hp
  · intro hp
    exact ⟨List.replicate s false, by simp, fun _ _ => ⟨List.replicate s false, by simp, hp⟩⟩

theorem source_exponent_mono {p q q' : ℕ} (h : q' ≤ q) (hf : FP3 p q) : FP3 p q' := by
  intro L hL
  apply hf L
  obtain ⟨K,f,hfL,B,hB⟩ := hL
  refine ⟨K,f,hfL,B,fun n => (hB n).trans ?_⟩
  change K * 2^(q'*n) + K ≤ K * 2^(q*n) + K
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right n h))) _

abbrev Pair := List Bool × List Bool
abbrev Tag := Bool ⊕ Bool

def swapPair (p : Pair) : Pair := (p.2,p.1)

theorem swap_time : ComputableInTime encodePair encodePair swapPair (fun n => 4*n + 4) := by
  refine tp_time _ _ _ (fun s : Tag => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
    (fun s : Tag => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s)
    (Sum.inl true) ?_
  rintro ⟨x,w⟩
  simp [swapPair, encodePair, List.filterMap_append, List.filterMap_map, Function.comp_def]

def afterSwap (p : Pair) : Pair := (List.replicate p.1.length true ++ false :: p.2,[])

def tagStep : Bool → Tag → Bool × Option Tag × Option Tag
  | true, Sum.inl _ => (true, some (Sum.inl true), none)
  | true, Sum.inr b => (false, some (Sum.inl false), some (Sum.inl b))
  | false, Sum.inl b => (false, some (Sum.inl b), none)
  | false, Sum.inr b => (false, some (Sum.inl b), none)

def tagFin : Bool → Option Tag
  | true => some (Sum.inl false)
  | false => none

theorem tag_right (x : List Bool) :
    fstRun2 tagStep tagFin false (x.map Sum.inr) = x.map Sum.inl := by
  induction x with
  | nil => rfl
  | cons b l ih => simp [fstRun2,tagStep,ih]

theorem tag_padding (w x : List Bool) :
    fstRun2 tagStep tagFin true (encodePair (w,x)) = encodePair (afterSwap (w,x)) := by
  induction w with
  | nil =>
    cases x <;> simp [encodePair, afterSwap, fstRun2, tagFin, tagStep, tag_right]
  | cons b l ih =>
    simp only [encodePair, List.map_cons, List.cons_append, fstRun2, tagStep,
      Option.toList_some, Option.toList_none, List.append_nil]
    have h := ih
    simp only [encodePair,afterSwap,List.map_nil,List.append_nil] at h
    rw [h]
    simp [afterSwap, List.replicate_succ]

theorem afterSwap_time : ComputableInTime encodePair encodePair afterSwap (fun n => 3*n+3) :=
  time_mono (fst2_time _ _ _ tagStep tagFin true (Sum.inl true) (fun p => (tag_padding p.1 p.2).symm))
    (fun _ => by omega)

def budgetInput (p : Pair) : Pair := afterSwap (swapPair p)

theorem budgetInput_time :
    ∃ C : ℕ, ComputableInTime encodePair encodePair budgetInput (fun n => C*n+C) := by
  apply lin_comp (C₁ := 4) (C₂ := 3) (D := 1) swap_time afterSwap_time
  intro p
  simp [encodePair, swapPair, Nat.add_comm]

theorem first_time : ComputableInTime encodePair (fun x : List Bool => x)
    (fun p : Pair => p.1) (fun n => 4*n + 4) := by
  refine tp_time _ _ _ (fun s : Tag => Sum.elim some (fun _ => none) s)
    (fun _ : Tag => none) true ?_
  rintro ⟨x,w⟩
  simp [encodePair, List.filterMap_append, List.filterMap_map, Function.comp_def]

theorem time_no_saving (p q : ℕ) (hp : 1 ≤ p) (hpq : q ≤ p) : FP3 p q := by
  intro L hL
  obtain ⟨M,f,hf,hM⟩ := hL
  let S : Set Pair := {r | r.1 ∈ L}
  let timeS (n : ℕ) := 4*n+4 + (2*n+2) + (M*2^(q*n)+M)
  have ht : DecidableInTime encodePair S timeS := by
    refine ⟨fun r => f r.1, fun r => hf r.1, ?_⟩
    refine comp_time encodePair (fun x : List Bool => x) Computability.encodeBool
      (fun r : Pair => r.1) f _ _ id first_time hM ?_ ?_
    · intro a b hab
      change M * 2^(q*a) + M ≤ M * 2^(q*b) + M
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul_left _ hab))) _
    · intro r
      simp [encodePair]
  obtain ⟨B,D,hB,hSound,hComplete⟩ := budget S timeS ht
  obtain ⟨C,hC⟩ := budgetInput_time
  let R : Set Pair := {r | budgetInput r ∈ B}
  obtain ⟨fB,hfB,hfBTime⟩ := hB
  have hl (r : Pair) : (encodePair (budgetInput r)).length ≤ 2*(encodePair r).length+2 := by
    simp [budgetInput, afterSwap, swapPair, encodePair]
    omega
  obtain ⟨C', hC'⟩ := lin_comp (C₁ := C) (C₂ := D) (D := 2) hC hfBTime hl
  have hR : DecidableInTime encodePair R (fun n => C'*n+C') :=
    ⟨fun r => fB (budgetInput r), fun r => hfB (budgetInput r), hC'⟩
  let K := M+6
  refine ⟨K, by dsimp [K]; omega, R, C', hR, ?_⟩
  intro x
  let s := K*2^(p*x.length)+K
  change x ∈ L ↔ Alt 3 s (fun w => (x,w) ∈ R)
  have hbound : timeS x.length ≤ s := by
    have hn : x.length ≤ 2^(p*x.length) := by
      exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by decide)
        (by nlinarith))
    have hexp : 2^(q*x.length) ≤ 2^(p*x.length) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hpq)
    dsimp [timeS,s,K]
    rw [Nat.add_mul]
    have h1 := Nat.mul_le_mul_left M hexp
    omega
  have hcorrect (w : List Bool) (hw : s ≤ w.length) : ((x,w) ∈ R ↔ x ∈ L) := by
    change (List.replicate w.length true ++ false :: x, []) ∈ B ↔ x ∈ L
    constructor
    · intro h
      exact hSound w.length x [] h
    · intro h
      exact hComplete w.length x [] (by simpa using hbound.trans hw) h
  rw [alt_three_iff]
  constructor
  · intro hx
    refine ⟨List.replicate s false, by simp, fun b hb => ⟨List.replicate s false, by simp, ?_⟩⟩
    apply (hcorrect _ ?_).2 hx
    simp [hb]
  · rintro ⟨a,ha,h⟩
    obtain ⟨c,hc,hR'⟩ := h (List.replicate s false) (by simp)
    apply (hcorrect _ ?_).1 hR'
    simp [ha,hc]

open Filter Topology

theorem polynomial_factor_gap (p q d K : ℕ) (hpq : p < q) :
    ∃ N : ℕ, ∀ n ≥ N, K * (n+1)^d * 2^(p*n) < 2^(q*n) := by
  let D : ℕ := K * 2^d
  let ε : ℝ := 1 / ((D : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1 : ℝ) < 2)
  have he := h₀.eventually (Iio_mem_nhds hε)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have ha := hN n (le_trans (le_max_left _ _) hn)
  change ((n : ℝ)^d / 2^n) < 1 / ((D : ℝ) + 1) at ha
  have hd : (D : ℝ) * (n : ℝ)^d < (2 : ℝ)^n := by
    have h2 : (0 : ℝ) < 2^n := by positivity
    have hD : (0 : ℝ) < D + 1 := by positivity
    rw [div_lt_div_iff₀ h2 hD, one_mul] at ha
    nlinarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) d]
  have hd' : D * n^d < 2^n := by exact_mod_cast hd
  have hfirst : K * (n+1)^d < 2^n := by
    calc
      K * (n+1)^d ≤ K * (2*n)^d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = D * n^d := by rw [mul_pow, ← Nat.mul_assoc]
      _ < 2^n := hd'
  have hexp : p*n+n ≤ q*n := by
    have h := Nat.mul_le_mul_right n (show p+1 ≤ q by omega)
    simpa [Nat.add_mul] using h
  calc
    K * (n+1)^d * 2^(p*n) < 2^n * 2^(p*n) :=
      Nat.mul_lt_mul_of_pos_right hfirst (by positivity)
    _ = 2^(p*n+n) := by rw [pow_add, mul_comm]
    _ ≤ 2^(q*n) := Nat.pow_le_pow_right (by decide) hexp

end VerifierAccounting
