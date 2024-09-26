import Frap.Sort
import Frap.Mergesort
open List


def isSorted : List Nat → Bool
| [] => true
| [_] => true
| x1 :: x2 :: xs => (x1 ≤ x2) && isSorted (x2 :: xs)

def mergeSortFuelWithCheck (l : List Nat) (n : Nat) : Nat × List Nat :=
  match l, n with
  | [], _ => (0, [])           -- No fuel used, return empty list
  | [x], _ => (0, [x])         -- No fuel used, single element is sorted
  | _, 0 => (0, l)             -- Ran out of fuel, return the list as it is
  | xs, n' + 1 =>
    if isSorted xs then        -- Check if the list is already sorted
      (0, xs)                  -- No fuel used if already sorted
    else
      let mid := xs.length / 2
      let left := xs.take mid
      let right := xs.drop mid
      let (fuelLeft, sortedLeft) := mergeSortFuelWithCheck left n'
      let (fuelRight, sortedRight) := mergeSortFuelWithCheck right n'
      let mergeFuel := if fuelLeft ≥ fuelRight then fuelLeft.succ else fuelRight.succ
      (mergeFuel, merge sortedLeft sortedRight)



def mergeSortWithFuel (l : List Nat) : Nat × List Nat :=
  mergeSortFuelWithCheck l l.length



#eval mergeSortFuelWithCheck [1,8,4,7,6,3,1,0,4,6] 2
#eval mergeSortWithFuel [1,8,4,7,6,3,1,0,4,6]
#eval mergeSortFuel [1,8,4,7,6,3,1,0,4,6] 4
--[1, 6, 0, 1,// 8, 4, 5, 0]
--[0, 1,// 1, 5, 0, 6,// 8, 4]
--[0, 0, 1, 1, 4, 5, 6, 8]
