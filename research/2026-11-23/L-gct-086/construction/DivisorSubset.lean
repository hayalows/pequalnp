import Mathlib

namespace DivisorSubset

def step (N a : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s ∪ ((s.image (· + a)).filter (· ≤ N))

def sums (N : ℕ) : List ℕ → Finset ℕ
  | [] => {0}
  | a :: as => step N a (sums N as)

def IsSubsetSum : List ℕ → ℕ → Prop
  | [], k => k = 0
  | a :: as, k => IsSubsetSum as k ∨ ∃ b, IsSubsetSum as b ∧ b + a = k

lemma mem_sums_iff (N : ℕ) (as : List ℕ) (k : ℕ) :
    k ∈ sums N as ↔ IsSubsetSum as k ∧ k ≤ N := by
  induction as generalizing k with
  | nil =>
    simp [sums, IsSubsetSum]
    omega
  | cons a as ih =>
    simp only [sums, step, IsSubsetSum, Finset.mem_union, Finset.mem_filter, Finset.mem_image, ih]
    constructor
    · rintro (⟨h, hN⟩ | ⟨⟨b, ⟨hb, hbN⟩, rfl⟩, hN⟩)
      · exact ⟨Or.inl h, hN⟩
      · exact ⟨Or.inr ⟨b, hb, rfl⟩, hN⟩
    · rintro ⟨h | ⟨b, hb, rfl⟩, hN⟩
      · exact Or.inl ⟨h, hN⟩
      · exact Or.inr ⟨⟨b, ⟨hb, by omega⟩, rfl⟩, hN⟩

lemma zero_mem_sums (N : ℕ) (as : List ℕ) : 0 ∈ sums N as := by
  induction as with
  | nil => simp [sums]
  | cons a as ih => exact Finset.mem_union_left _ ih

lemma grow (N a : ℕ) (s : Finset ℕ) (hzero : 0 ∈ s) (hdiv : a ∣ N)
    (hN : N ∉ step N a s) : s.card < (step N a s).card := by
  by_contra! h
  have he : s = step N a s := Finset.eq_of_subset_of_card_le Finset.subset_union_left h
  obtain ⟨m, rfl⟩ := hdiv
  have closure (k : ℕ) (hk : k ≤ m) : a * k ∈ s := by
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have hk' : k ≤ m := by omega
      have hmem : a * (k + 1) ∈ step (a*m) a s := by
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_image.mpr ⟨a*k, ih hk', by ring⟩, ?_⟩
        exact Nat.mul_le_mul_left a hk
      exact he ▸ hmem
  exact hN (Finset.mem_union_left _ (closure m le_rfl))

lemma size (N : ℕ) (as : List ℕ) (hdiv : ∀ a ∈ as, a ∣ N)
    (hN : N ∉ sums N as) : as.length + 1 ≤ (sums N as).card := by
  induction as with
  | nil => simp [sums]
  | cons a as ih =>
    have htail : N ∉ sums N as := fun hn => hN (Finset.mem_union_left _ hn)
    have hs := ih (fun b hb => hdiv b (List.mem_cons_of_mem _ hb)) htail
    have hg := grow N a (sums N as) (zero_mem_sums N as) (hdiv a (by simp)) hN
    change as.length + 1 + 1 ≤ (step N a (sums N as)).card
    omega

theorem exists_subset_sum (N : ℕ) (as : List ℕ) (hdiv : ∀ a ∈ as, a ∣ N)
    (hlen : N ≤ as.length) : IsSubsetSum as N := by
  by_contra h
  have hN : N ∉ sums N as := fun hmem => h ((mem_sums_iff N as N).mp hmem).1
  have hz := size N as hdiv hN
  have hs : sums N as ⊆ Finset.range N := by
    intro k hk
    rw [Finset.mem_range]
    have hkN := ((mem_sums_iff N as k).mp hk).2
    have hne : k ≠ N := fun he => hN (he ▸ hk)
    omega
  have hc := Finset.card_le_card hs
  rw [Finset.card_range] at hc
  omega

end DivisorSubset
