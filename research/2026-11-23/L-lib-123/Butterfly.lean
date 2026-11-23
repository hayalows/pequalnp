import Mathlib

open Finset

namespace Butterfly

abbrev Word (k : ℕ) := Fin k → Bool
abbrev Vertex (k : ℕ) := Fin (k+1) × Word k
abbrev Endpoints (k : ℕ) := Word k × Word k

def atLayer {k : ℕ} (i : ℕ) (a b : Word k) : Word k :=
  fun j => if j.val < i then b j else a j

theorem first_layer {k : ℕ} (a b : Word k) : atLayer 0 a b = a := by
  funext j
  simp [atLayer]

theorem last_layer {k : ℕ} (a b : Word k) : atLayer k a b = b := by
  funext j
  simp [atLayer,j.isLt]

theorem change_only_current_bit {k : ℕ} (i : ℕ) (a b : Word k) (j : Fin k)
    (h : j.val ≠ i) : atLayer (i+1) a b j = atLayer i a b j := by
  have : j.val < i + 1 ↔ j.val < i := by omega
  simp [atLayer,this]

def fiberEquiv {k : ℕ} (i : ℕ) (z : Word k) :
    {p : Endpoints k // atLayer i p.1 p.2 = z} ≃ Word k where
  toFun p j := if j.val < i then p.val.1 j else p.val.2 j
  invFun w := ⟨(fun j => if j.val < i then w j else z j,
      fun j => if j.val < i then z j else w j), by
    funext j
    by_cases h : j.val < i <;> simp [atLayer,h]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> funext j
    · have hp := congrFun p.property j
      by_cases h : j.val < i <;> simp_all [atLayer]
    · have hp := congrFun p.property j
      by_cases h : j.val < i <;> simp_all [atLayer]
  right_inv w := by
    funext j
    by_cases h : j.val < i <;> simp [h]

noncomputable def hits {k : ℕ} (v : Vertex k) : Finset (Endpoints k) := by
  classical
  exact univ.filter fun p => atLayer v.1.val p.1 p.2 = v.2

theorem hits_card {k : ℕ} (v : Vertex k) : (hits v).card = 2^k := by
  classical
  have h := Fintype.card_congr (fiberEquiv v.1.val v.2)
  rw [Fintype.card_subtype] at h
  simpa [hits, Word] using h

def avoids {k : ℕ} (cut : Finset (Vertex k)) (a b : Word k) : Prop :=
  ∀ i : Fin (k+1), (i,atLayer i.val a b) ∉ cut

noncomputable def survivingSources {k : ℕ} (cut : Finset (Vertex k)) (b : Word k) :
    Finset (Word k) := by
  classical
  exact univ.filter fun a => avoids cut a b

theorem many_surviving_sources {k : ℕ} (cut : Finset (Vertex k)) :
    ∃ b : Word k, 2^k ≤ cut.card + (survivingSources cut b).card := by
  classical
  let bad := cut.biUnion hits
  let good := (univ : Finset (Endpoints k)) \ bad
  let m := 2^k
  have hm : Fintype.card (Word k) = m := by simp [m,Word]
  have hbad : bad.card ≤ cut.card*m := by
    apply card_biUnion_le.trans
    simp [hits_card,m]
  have hgood (a b : Word k) : (a,b) ∈ good ↔ avoids cut a b := by
    simp only [good, mem_sdiff, mem_univ, true_and, bad, mem_biUnion, hits, mem_filter]
    constructor
    · intro h i hi
      exact h ⟨(i,atLayer i.val a b),hi,rfl⟩
    · intro h hex
      rcases hex with ⟨v,hi,hz⟩
      rcases v with ⟨i,z⟩
      change atLayer i.val a b = z at hz
      exact h i (by rw [hz]; exact hi)
  have htotal : good.card + bad.card = m*m := by
    have h := card_sdiff_add_card_eq_card (subset_univ bad)
    simpa only [good, card_univ, Fintype.card_prod, hm] using h
  have hcount : good.card = ∑ b : Word k, (survivingSources cut b).card := by
    rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := (univ : Finset (Word k)))
      (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro b _
    refine card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro ⟨a,b'⟩ h
      rcases mem_filter.mp h with ⟨hg,hb⟩
      change b' = b at hb
      subst b'
      simp [survivingSources, (hgood a b).mp hg]
    · rintro ⟨a,b'⟩ hx ⟨a',b''⟩ hy he
      have h1 : b' = b := (mem_filter.mp hx).2
      have h2 : b'' = b := (mem_filter.mp hy).2
      exact Prod.ext he (h1.trans h2.symm)
    · intro a ha
      have hz : avoids cut a b := (mem_filter.mp ha).2
      exact ⟨(a,b),mem_filter.mpr ⟨(hgood a b).mpr hz,rfl⟩,rfl⟩
  by_contra! hf
  have hsmall : (∑ b : Word k, (survivingSources cut b).card) + cut.card*m < m*m := by
    calc
      _ = ∑ b : Word k, (cut.card + (survivingSources cut b).card) := by
        rw [sum_add_distrib]
        simp [hm, Nat.mul_comm, Nat.add_comm]
      _ < ∑ _ : Word k, m := by
        apply sum_lt_sum
        · intro b _
          exact (hf b).le
        · exact ⟨fun _ => false, mem_univ _, hf _⟩
      _ = m*m := by simp [hm]
  omega

theorem half_sources_survive {k : ℕ} (hk : 0 < k) (cut : Finset (Vertex k))
    (hc : cut.card ≤ 2^(k-1)) :
    ∃ b : Word k, 2^(k-1) ≤ (survivingSources cut b).card := by
  obtain ⟨b,hb⟩ := many_surviving_sources cut
  refine ⟨b,?_⟩
  have hp : 2^k = 2 * 2^(k-1) := by
    calc
      2^k = 2^((k-1)+1) := by rw [Nat.sub_add_cancel hk]
      _ = 2 * 2^(k-1) := by rw [pow_succ']
  omega

end Butterfly
