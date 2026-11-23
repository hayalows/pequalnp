import Mathlib

open Finset

namespace LineAndDag

theorem branching_count {ι : Type} [DecidableEq ι] (V : Finset ι) (root : ι)
    (hr : root ∈ V) (next : ι → Finset ι)
    (hdeg : ∀ v ∈ V, (next v).card ≤ 2)
    (hcover : ∀ v ∈ V, v ≠ root → ∃ u ∈ V, v ∈ next u) :
    (V.filter fun v => (next v).card = 0).card ≤
      (V.filter fun v => (next v).card = 2).card + 1 := by
  have hcov : V.erase root ⊆ V.biUnion next := by
    intro v hv
    rcases mem_erase.mp hv with ⟨hne,hm⟩
    exact mem_biUnion.mpr (hcover v hm hne)
  have ha : V.card - 1 ≤ ∑ v ∈ V, (next v).card := by
    rw [← card_erase_of_mem hr]
    exact (card_le_card hcov).trans card_biUnion_le
  have hd : (∑ v ∈ V, (next v).card) =
      (V.filter fun v => (next v).card ≠ 0).card +
      (V.filter fun v => (next v).card = 2).card := by
    rw [card_eq_sum_ones (V.filter _), card_eq_sum_ones (V.filter _)]
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun v hv => ?_
    have := hdeg v hv
    split_ifs <;> omega
  have hp : (V.filter fun v => (next v).card = 0).card +
      (V.filter fun v => (next v).card ≠ 0).card = V.card :=
    card_filter_add_card_filter_not (s := V) (fun v => (next v).card = 0)
  have hh := ha.trans_eq hd
  omega

def diffSet : Finset (Fin 57) := {0, 1, 3, 13, 32, 36, 43, 52}
def line (w : Fin 57) : Finset (Fin 57) := diffSet.image fun v => v + w

set_option maxRecDepth 6000 in
set_option maxHeartbeats 6000000 in
theorem each_point_eight_lines : ∀ v : Fin 57, (univ.filter fun w => v ∈ line w).card = 8 := by
  decide

theorem sum_line_counts (W : Finset (Fin 57)) :
    (∑ w : Fin 57, (line w ∩ W).card) = 8 * W.card := by
  calc
    _ = ∑ w : Fin 57, ∑ v ∈ W, if v ∈ line w then 1 else 0 := by
      apply sum_congr rfl
      intro w _
      rw [← sum_filter, ← card_eq_sum_ones]
      congr 1
      ext v
      simp [and_comm]
    _ = ∑ v ∈ W, ∑ w : Fin 57, if v ∈ line w then 1 else 0 := sum_comm
    _ = _ := by
      simp_rw [← sum_filter, ← card_eq_sum_ones, each_point_eight_lines]
      simp [Nat.mul_comm]

theorem large_restriction_excess (W : Finset (Fin 57)) (h : 16 ≤ W.card) :
    14 ≤ ∑ w : Fin 57, ((line w ∩ W).card - 2) := by
  have hbound : (∑ w : Fin 57, (line w ∩ W).card) ≤
      (∑ w : Fin 57, ((line w ∩ W).card - 2)) + 114 := by
    calc
      _ ≤ ∑ w : Fin 57, (((line w ∩ W).card - 2) + 2) :=
        sum_le_sum (fun w _ => by omega)
      _ = _ := by rw [sum_add_distrib]; simp
  rw [sum_line_counts] at hbound
  omega

theorem line_zero : line 0 = diffSet := by simp [line]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 7000000 in
theorem shifted_intersection_count :
    ∀ d : Fin 57, d ≠ 0 → (diffSet ∩ line d).card = 1 := by decide

theorem translate_line (u w : Fin 57) :
    (line w).map ⟨fun x => x-u, fun x y h => by simpa using congrArg (fun z => z + u) h⟩ = line (w-u) := by
  ext x
  simp only [line, mem_map, mem_image]
  constructor
  · rintro ⟨y,⟨a,ha,rfl⟩,rfl⟩
    refine ⟨a,ha,?_⟩
    change a + (w-u) = (a+w)-u
    abel
  · rintro ⟨a,ha,rfl⟩
    refine ⟨a+w,⟨a,ha,rfl⟩,?_⟩
    change (a+w)-u = a + (w-u)
    abel

theorem pair_intersection_count (u v : Fin 57) (h : u ≠ v) :
    (line u ∩ line v).card = 1 := by
  let emb : Fin 57 ↪ Fin 57 := ⟨fun x => x-u, fun x y h => by simpa using congrArg (fun z => z + u) h⟩
  rw [← card_map emb, map_inter, translate_line, translate_line, sub_self, line_zero]
  exact shifted_intersection_count _ (sub_ne_zero.mpr h.symm)

theorem line_count (w : Fin 57) : (line w).card = 8 := by
  rw [line, card_image_of_injective _ (fun _ _ => add_right_cancel)]
  decide

def sixteenOutside : Finset (Fin 57) := {6, 7, 8, 9, 10, 11, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24}
theorem sixteenOutside_card : sixteenOutside.card = 16 := by decide
theorem sixteenOutside_avoids :
    Disjoint sixteenOutside (line 0 ∪ line 1 ∪ line 2) := by decide

theorem support_branching_count {α : Type} [DecidableEq α]
    (V : Finset ℕ) (root : ℕ) (hr : root ∈ V) (next : ℕ → Finset ℕ)
    (support : ℕ → Finset α)
    (hdeg : ∀ v ∈ V, (next v).card ≤ 2)
    (hcover : ∀ v ∈ V, v ≠ root → ∃ u ∈ V, v ∈ next u)
    (hnext : ∀ v ∈ V, ∀ u ∈ next v, u ∈ V ∧ u < v)
    (hprop : ∀ v ∈ V, (next v).card ≠ 0 → support v ⊆ (next v).biUnion support)
    (hleaf : ∀ v ∈ V, (next v).card = 0 → (support v).card ≤ 1) :
    (support root).card ≤ (V.filter fun v => (next v).card = 2).card + 1 := by
  let leaves := V.filter fun v => (next v).card = 0
  have hs (v : ℕ) : v ∈ V → support v ⊆ leaves.biUnion support := by
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro hv x hx
      by_cases hz : (next v).card = 0
      · exact mem_biUnion.mpr ⟨v,mem_filter.mpr ⟨hv,hz⟩,hx⟩
      · rcases mem_biUnion.mp (hprop v hv hz hx) with ⟨u,hu,hxu⟩
        obtain ⟨huV,hlt⟩ := hnext v hv u hu
        exact ih u hlt huV hxu
  calc
    _ ≤ (leaves.biUnion support).card := card_le_card (hs root hr)
    _ ≤ ∑ v ∈ leaves, (support v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ leaves, 1 := sum_le_sum fun v hv =>
      let ⟨hm,hz⟩ := mem_filter.mp hv
      hleaf v hm hz
    _ = leaves.card := by simp
    _ ≤ _ := branching_count V root hr next hdeg hcover

theorem pack_extra_gates {ι : Type} [DecidableEq ι]
    (all outs : Finset ι) (ho : outs ⊆ all)
    (branch : Fin 57 → Finset ι)
    (hsub : ∀ w, branch w ⊆ all \ outs)
    (hd : (Set.univ : Set (Fin 57)).PairwiseDisjoint branch)
    (W : Finset (Fin 57)) (hW : 16 ≤ W.card)
    (hlocal : ∀ w, (line w ∩ W).card - 2 ≤ (branch w).card) :
    outs.card + 14 ≤ all.card := by
  classical
  have hUnion : (univ : Finset (Fin 57)).biUnion branch ⊆ all \ outs := by
    rintro x hx
    obtain ⟨w,_,hw⟩ := mem_biUnion.mp hx
    exact hsub w hw
  have hcard := card_le_card hUnion
  rw [card_biUnion (by simpa using hd)] at hcard
  have hl : (∑ w : Fin 57, ((line w ∩ W).card - 2)) ≤ ∑ w : Fin 57, (branch w).card :=
    sum_le_sum (fun w _ => hlocal w)
  have hh := card_sdiff_add_card_eq_card ho
  have := large_restriction_excess W hW
  omega

end LineAndDag
