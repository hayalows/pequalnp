import Mathlib
import PEqualNP.Defs

namespace EvasionDAG

variable {Value : Type*}

def Certificate
    (pred : ℕ → Set ℕ) (rule : ℕ → (ℕ → Value) → Value)
    (anchors : Set ℕ) (claim : ℕ → Value)
    (v : ℕ) (cone : Set ℕ) (labels : ℕ → Value) : Prop :=
  v ∈ cone ∧
    (∀ i ∈ cone, rule i labels = labels i) ∧
    (∀ i ∈ cone, ∀ j ∈ pred i, j ∈ cone ∨ j ∈ anchors) ∧
    ∀ i ∈ anchors, labels i = claim i

theorem certificateSoundWithEarlierAnchors
    (pred : ℕ → Set ℕ) (rule : ℕ → (ℕ → Value) → Value)
    (hpred : ∀ i j, j ∈ pred i → j < i)
    (hrule : ∀ i x y, (∀ j ∈ pred i, x j = y j) → rule i x = rule i y)
    (truth : ℕ → Value) (htruth : ∀ i, rule i truth = truth i)
    (anchors : Set ℕ) (claim : ℕ → Value)
    (v : ℕ) (cone : Set ℕ) (labels : ℕ → Value)
    (hcert : Certificate pred rule anchors claim v cone labels)
    (hknown : ∀ j < v, j ∈ anchors → claim j = truth j) :
    labels v = truth v := by
  have localAgree (i : ℕ) (hiv : i ≤ v) (hi : i ∈ cone) : labels i = truth i := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      rw [← hcert.2.1 i hi, ← htruth i]
      apply hrule
      intro j hj
      have hji := hpred i j hj
      rcases hcert.2.2.1 i hi j hj with hcone | hanchor
      · exact ih j hji (hji.le.trans hiv) hcone
      · exact (hcert.2.2.2 j hanchor).trans (hknown j (hji.trans_le hiv) hanchor)
  exact localAgree v le_rfl hcert.1

theorem committedAnchorsSound
    (pred : ℕ → Set ℕ) (rule : ℕ → (ℕ → Value) → Value)
    (hpred : ∀ i j, j ∈ pred i → j < i)
    (hrule : ∀ i x y, (∀ j ∈ pred i, x j = y j) → rule i x = rule i y)
    (truth : ℕ → Value) (htruth : ∀ i, rule i truth = truth i)
    (anchors : Set ℕ) (claim : ℕ → Value)
    (hcert : ∀ v ∈ anchors, ∃ cone labels, Certificate pred rule anchors claim v cone labels) :
    ∀ v ∈ anchors, claim v = truth v := by
  intro v hv
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    obtain ⟨cone, labels, h⟩ := hcert v hv
    exact (h.2.2.2 v hv).symm.trans
      (certificateSoundWithEarlierAnchors pred rule hpred hrule truth htruth anchors claim v cone labels h ih)

theorem checkedTargetSound
    (pred : ℕ → Set ℕ) (rule : ℕ → (ℕ → Value) → Value)
    (hpred : ∀ i j, j ∈ pred i → j < i)
    (hrule : ∀ i x y, (∀ j ∈ pred i, x j = y j) → rule i x = rule i y)
    (truth : ℕ → Value) (htruth : ∀ i, rule i truth = truth i)
    (anchors : Set ℕ) (claim : ℕ → Value)
    (hcert : ∀ v ∈ anchors, ∃ cone labels, Certificate pred rule anchors claim v cone labels)
    (v : ℕ) (cone : Set ℕ) (labels : ℕ → Value)
    (hv : Certificate pred rule anchors claim v cone labels) :
    labels v = truth v :=
  certificateSoundWithEarlierAnchors pred rule hpred hrule truth htruth anchors claim v cone labels hv
    (fun j _ => committedAnchorsSound pred rule hpred hrule truth htruth anchors claim hcert j)

theorem closedConeCompleteness
    (pred : ℕ → Set ℕ) (rule : ℕ → (ℕ → Value) → Value)
    (truth : ℕ → Value) (htruth : ∀ i, rule i truth = truth i)
    (anchors : Set ℕ) (claim : ℕ → Value)
    (hclaim : ∀ i ∈ anchors, claim i = truth i)
    (v : ℕ) (cone : Set ℕ) (hv : v ∈ cone)
    (hclosed : ∀ i ∈ cone, ∀ j ∈ pred i, j ∈ cone ∨ j ∈ anchors) :
    Certificate pred rule anchors claim v cone truth :=
  ⟨hv, fun i _ => htruth i, hclosed, fun i hi => (hclaim i hi).symm⟩

end EvasionDAG
