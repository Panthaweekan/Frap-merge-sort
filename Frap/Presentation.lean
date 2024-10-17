import Frap.Sort
open List


def merge : List Nat → List Nat → List Nat
| [], ys => ys
| xs, [] => xs
| (x::xs) , (y::ys) =>
  if x ≤ y then x :: merge xs (y::ys)
  else y :: merge (x::xs) ys


-- Merge Sort function with fuel
def mergeSortFuel (l : List Nat) (n : Nat) : List Nat :=
  match l, n with
  | [] , _=> []
  | [x] , _ => [x]  -- Base case: A single element list is already sorted
  | _, 0 => l      -- Ran out of fuel, return the list as it is
  | xs, n' + 1 =>
    let mid := xs.length / 2
    let left := xs.take mid
    let right := xs.drop mid
    let sortedLeft := mergeSortFuel left n'
    let sortedRight := mergeSortFuel right n'
    merge sortedLeft sortedRight

-- Wrapper function to automatically provide fuel
def mergeSort (l : List Nat) : List Nat :=
  mergeSortFuel l l.length

#eval mergeSortFuel [1, 6, 0, 1, 8, 4, 5, 0] 3
/- nested recursion appear! -/
-- [1, 6, 0, 1,// 8, 4, 5, 0]
-- [0, 1,// 1, 5, 0, 6,// 8, 4]
-- [0, 0, 1, 1, 4, 5, 6, 8]
#eval mergeSort [1, 6, 0, 1, 8, 4, 5,0 ]

/-
Proof of correctness of Merge Sort
-/

open Permutation
open Sorted

theorem merge_ :  ∀ (x y : Nat) (l₁ l₂ : List Nat),
  x ≤ y → merge (x :: l₁) (y :: l₂) = x :: merge l₁ (y :: l₂) := by
  intro x y l₁ l₂
  intro xy
  simp [merge]
  intro yx
  apply And.intro --- note 
  . omega
  . omega

theorem merge_nil : ∀ (l : List  Nat), merge [] l = l := by
  intro n
  simp [merge]

theorem Sorted_merge1 : ∀ (x x1 x2: Nat) (l₁ l₂ : List Nat),
  x ≤ x1 → x ≤ x2 →
  Sorted (merge (x1 :: l₁) (x2 :: l₂)) →
  Sorted (x :: merge (x1 :: l₁) (x2 :: l₂)) := by
  intro x x1 x2
  intro l₁ l₂
  intro hx1 hx2
  intro ih
  simp [merge]
  split
  . apply sorted_cons
    . assumption
    . simp [merge] at ih
      split at ih
      . assumption
      . assumption
  . apply sorted_cons
    . assumption
    . simp [merge] at ih
      split at ih
      . contradiction
      . assumption

theorem Sorted_mergetry : ∀ (l₁ l₂ : List Nat),
  Sorted l₁ → Sorted l₂ → Sorted (merge l₁ l₂) := by
  intro l₁ l₂ sl₁ sl₂
  induction sl₁ with
  | sorted_nil =>
    simp [merge]
    assumption
  | sorted_1 n =>
    induction sl₂
    . simp [merge]
      apply sorted_1
    . simp [merge]
      split
      . apply sorted_cons
        . assumption
        . apply sorted_1
      . apply sorted_cons
        . omega
        . apply sorted_1
    . simp [merge]
      split
      . apply sorted_cons
        . assumption
        . apply sorted_cons
          . assumption
          . assumption
      . split
        . apply sorted_cons
          . omega
          . apply sorted_cons
            . assumption
            . assumption
        . apply sorted_cons
          . assumption
          . sorry
  | sorted_cons =>
    induction sl₂
    . simp [merge] at *
      apply sorted_cons
      . assumption
      . assumption
    . simp [merge]
      split
      . split
        . apply sorted_cons
          . assumption
          . sorry
        . apply sorted_cons
          . assumption
          . apply sorted_cons
            . omega
            . assumption
      . apply sorted_cons
        . omega
        . apply sorted_cons
          . omega
          . assumption
    . simp [merge]
      . split
        . split
          . apply sorted_cons
            . assumption
            . sorry
          . split
            . apply sorted_cons
              . assumption
              . apply sorted_cons
                . omega
                . sorry
            . apply sorted_cons
              . assumption
              . apply sorted_cons
                . assumption
                . sorry
        . split
          . split
            . apply sorted_cons
              . omega
              . apply sorted_cons
                . assumption
                . sorry
            . apply sorted_cons
              . omega
              . apply sorted_cons
                . assumption
                . sorry
          . apply sorted_cons
            . assumption
            . simp [*] at *
              sorry


theorem Sorted_merge : ∀ (l₁ l₂ : List Nat),
  Sorted l₁ → Sorted l₂ → Sorted (merge l₁ l₂) := by
  intro l₁ l₂ sl₁ sl₂
  induction l₁ with simp [merge] at *
  | nil =>
    assumption
  | cons =>
    induction l₂ with simp [merge] at *
    | nil =>
      assumption
    | cons =>
      split
      . cases sl₁
        . simp [merge]
          apply sorted_cons
          . assumption
          . assumption
        . simp [merge] at *
          split
          . apply sorted_cons
            . assumption
            . rename_i ih as
              split at ih
              . apply ih
                assumption
              . apply ih
                assumption
          . apply sorted_cons
            . assumption
            . rename_i ih as
              split at ih
              . contradiction
              . apply ih
                assumption
      . cases sl₂
        . simp [merge]
          apply sorted_cons
          . omega
          . assumption
        . simp [merge] at *
          split
          . apply sorted_cons
            . omega
            . rename_i ih as
              split at ih
              . apply ih
                . assumption
                . intro t
                  sorry
              . apply ih
                . assumption
                . intro t'
                  sorry
          . apply sorted_cons
            . assumption
            . rename_i ih as
              split at ih
              . contradiction
              . apply ih
                . assumption
                . intro t''
                  sorry


theorem merge_perm : ∀ (l₁ l₂ : List Nat),
  Permutation (l₁ ++ l₂) (merge l₁ l₂) := by
  intro l₁ l₂
  induction l₁ with
  | nil =>
    simp [merge]
    apply permutation_refl
  | cons a l₁' ih₁ =>
    induction l₂ with
    | nil =>
      simp [merge]
      apply permutation_refl
    | cons b l₂ ih₂ =>
      by_cases h : a ≤ b
      . simp [merge, h]
        apply perm_skip
        assumption
      . simp [merge, h]
        sorry


theorem mergeSort_perm (l : List Nat) : Permutation l (mergeSort l)  := by
  induction l with
  | nil =>
    apply permutation_refl
  | cons n l' ih =>
    apply perm_trans
    . apply perm_skip
      assumption
    . sorry


theorem mergeSort_sorted (l : List Nat) : Sorted (mergeSort l) := by
  induction l with
  | nil =>
    sorry
  | cons =>
    sorry

theorem mergeSort_correct (l : List Nat) : Sorted (mergeSort l) ∧ Permutation (mergeSort l) l := by
  sorry

theorem merge_associative (l₁ l₂ l₃ : List Nat) : merge (merge l₁ l₂) l₃ = merge l₁ (merge l₂ l₃) := by
  sorry





--ref https://softwarefoundations.cis.upenn.edu/vfa-current/Merge.html
