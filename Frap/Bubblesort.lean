import Mathlib.Tactic.Linarith

def bubbleSortAux : List Nat → List Nat
| [] => []
| [x] => [x]
| x :: y :: xs =>
  if x >= y then
    y :: bubbleSortAux (x :: xs)
  else
    x :: bubbleSortAux (y :: xs)

-- Simplified `bubbleSortFuel` using the natural recursion pattern
def bubbleSortFuel : List Nat → Nat → List Nat
| [], _ => []
| [x], _ => [x]
| xs, 0 => xs
| xs, n + 1 => bubbleSortFuel (bubbleSortAux xs) n

-- Main bubble sort function, computes the sorted list
def bubbleSortF (l : List Nat) : List Nat :=
  bubbleSortFuel l (l.length)
-- Example evaluation of the sorting function
#eval bubbleSortF [2 , 3 , 1 , 5 , 4]

-- Helper function to count the number of comparisons made in bubbleSortAux
def bubbleSortAuxCount : List Nat → Nat
| [] => 0
| [_] => 0
| x :: y :: xs =>
  if x > y then
    1 + bubbleSortAuxCount (x :: xs)
  else
    1 + bubbleSortAuxCount (y :: xs)

-- Function to count the number of comparisons made by bubbleSortFuel
def bubbleSortFuelCount : List Nat → Nat → Nat
| [], _ => 0
| [_], _ => 0
| _, 0 => 0
| xs, n + 1 => bubbleSortAuxCount xs + bubbleSortFuelCount (bubbleSortAux xs) n

-- Main bubble sort function to compute the complexity
def bubbleSortCount (l : List Nat) : Nat :=
  bubbleSortFuelCount l l.length

#eval bubbleSortCount [1 , 2 , 3 , 4 , 5]
