import Frap.Sort

def split {X : Type} : List X → (List X × List X)
| [] => ([], [])
| [x] => ([x], [])
| x1 :: x2 :: l' =>
  let (l1, l2) := split l'
  (x1 :: l1, x2 :: l2)


--(* We're stuck! The IH talks about split (x::l') but we
--        only know aobut split (a::x::l'). *
theorem split_len_first_try {X : Type} (l : List X) (l1 l2 : List X)
  (h : split l = (l1, l2)) : l1.length  ≤  l.length  ∧  l2.length ≤  l.length := by
  induction l with simp [split] at *
  | nil =>
    constructor
    . cases h.left
      rfl
    . cases h.right
      rfl
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [split] at h
      constructor
      . cases h.left
        apply Nat.le_refl
      . cases h.right
        exact Nat.zero_le 1
    | cons y ys =>
      simp [split] at h
      obtain ⟨l1', l2'⟩ := h
      constructor
      . rw [← l1']
        apply Nat.succ_le_succ
        sorry
      . rw [← l2']
        apply Nat.succ_le_succ
        sorry


def list_ind2_principle (A : Type) (P : List A → Prop) : Prop :=
  P [] →
  (∀ (a : A), P [a]) →
  (∀ (a b : A) (l : List A), P l → P (a :: b :: l)) →
  ∀ l : List A, P l

example (A : Type) (P : List A → Prop) (h1 : P []) (h2 : ∀ (a : A), P [a])
  (h3 : ∀ (a b : A) (l : List A), P l → P (a :: b :: l)) :
  list_ind2_principle A P := by
  intro he h1 hc la
  induction la with
  | nil =>
    assumption
  | cons a l=>
    cases l
    . apply h1
    . apply hc
      sorry

theorem split_len' (list_ind2_principle : ∀ (A : Type) (P : List A → Prop),
    P [] →
    (∀ (a : A), P [a]) →
    (∀ (a b : A) (l : List A), P l → P (a :: b :: l)) →
    ∀ l : List A, P l) :
    ∀ {X} (l : List X) (l1 l2 : List X),
    split l = (l1, l2) →
    l1.length  ≤  l.length  ∧  l2.length ≤  l.length := by
    sorry

-- wtf is this
def list_ind2 : ∀ (A : Type) (P : List A → Prop),
  P [] →
  (∀ (a : A), P [a]) →
  (∀ (a b : A) (l : List A), P l → P (a :: b :: l)) →
  ∀ l : List A, P l :=
  λ A P hnil hsingle hpair l =>
    match l with
    | [] => hnil
    | [x] => hsingle x
    | x :: y :: l' => hpair x y l' (list_ind2 A P hnil hsingle hpair l')

theorem split_len {X : Type} (l : List X) (l1 l2 : List X) :
  split l = (l1, l2) →
  l1.length  ≤  l.length  ∧  l2.length ≤  l.length := by
  sorry

theorem split_perm {X : Type} (l l1 l2 : List X) :
  split l = (l1, l2) → Permutation l (l1 ++ l2) := by
  sorry




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
    let left := xs.take mid     /- Returns the first n (mid) elements of xs -/
    let right := xs.drop mid    /- Removes the first n (mid) elements of xs -/
    let sortedLeft := mergeSortFuel left n'
    let sortedRight := mergeSortFuel right n'
    merge sortedLeft sortedRight

-- Wrapper function to automatically provide fuel
def mergeSort (l : List Nat) : List Nat :=
  mergeSortFuel l l.length

#eval mergeSort [69 , 23 , 12 , 34, 15, 12, 3, 1, 2, 1]

/-
Proof of correctness of Merge Sort
-/

open Permutation
open Sorted

theorem merge2 :  ∀ (x y : Nat) (l₁ l₂ : List Nat),
  x ≤ y → merge (x :: l₁) (y :: l₂) = x :: merge l₁ (y :: l₂) := by
  intro x y l₁ l₂
  intro xy
  simp [merge]
  intro yx
  apply And.intro
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
  sorry

theorem mergeSort_correct (l : List Nat) : Sorted (mergeSort l) ∧ Permutation (mergeSort l) l := by
  sorry

theorem merge_associative (l₁ l₂ l₃ : List Nat) : merge (merge l₁ l₂) l₃ = merge l₁ (merge l₂ l₃) := by
  sorry


--ref https://softwarefoundations.cis.upenn.edu/vfa-current/Merge.html
