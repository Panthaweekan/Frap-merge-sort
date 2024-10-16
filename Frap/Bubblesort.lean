import Mathlib.Tactic.Linarith
import Frap.Sort

def swap : List Nat → List Nat
| [] => []
| [x] => [x]
| x :: y :: xs =>
  if x > y then
    y :: swap (x :: xs)
  else
    x :: swap (y :: xs)

-- Simplified `bubbleSortFuel` using the natural recursion pattern
def bubbleSortFuel : List Nat → Nat → List Nat
| [], _ => []
| [x], _ => [x]
| xs, 0 => xs
| xs, n + 1 => bubbleSortFuel (swap xs) n

-- Main bubble sort function, computes the sorted list
def bubbleSort (l : List Nat) : List Nat :=
  bubbleSortFuel l (l.length)
-- Example evaluation of the sorting function
#eval bubbleSort [2 , 3 , 1 , 5 , 4]

--- Correctness proof of the bubble sort algorithm
open Sorted
open Permutation

lemma swap_length : ∀ (l : List Nat),
  (swap l).length = l.length := by
  sorry

lemma swap_perm : ∀ (l : List Nat),
  Permutation l (swap l) := by
  sorry

lemma Sorted_bubbleSort : ∀ (l : List Nat),
  Sorted (bubbleSort l) := by
  sorry

lemma bubblesort_perm : ∀ (l : List Nat),
  Permutation l (bubbleSort l) := by
  sorry

lemma bubblesort_length : ∀ (l : List Nat),
  (bubbleSort l).length = l.length := by
  sorry

