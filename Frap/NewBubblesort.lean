def bubble [LT T] [DecidableRel (LT.lt (α := T))] : List T -> List T
  | [] => []
  | [x] => [x]
  | x :: y :: xs => if x < y then x :: bubble (y :: xs) else y :: bubble (x :: xs)

def bubblesortFuel [LT T] [DecidableRel (LT.lt (α := T))] [BEq T] (l : List T) (n : Nat) : List T × Nat :=
  let rec iter (l : List T) (fuel : Nat) : List T × Nat :=
    if fuel = 0 then (l, fuel)  -- Return the list and remaining fuel as is when out of fuel
    else
      let l' := bubble l
      if l' == l then (l, fuel)  -- List is sorted, so return it and remaining fuel
      else iter l' (fuel - 1)  -- Continue sorting with one less fuel
  iter l n

def bubblesort [LT T] [DecidableRel (LT.lt (α := T))] [BEq T] (l : List T) : List T :=
  let rec iter (l : List T) (fuel : Nat) : List T :=
    if fuel = 0 then l  -- Return the list as is when out of fuel
    else
      let l' := bubble l
      if l' == l then l  -- List is sorted, so return it
      else iter l' (fuel - 1)  -- Continue sorting with one less fuel
  iter l l.length


#eval bubblesortFuel [4, 3, 1, 2, 5] 3
#eval bubblesort [4, 3, 1, 2, 5]

def bubbleWithCount [LT T] [DecidableRel (LT.lt (α := T))] : List T -> Nat -> (List T × Nat)
  | [], count => ([], count)
  | [x], count => ([x], count)
  | x :: y :: xs, count =>
    if x < y then
      let (bubbledRest, newCount) := bubbleWithCount (y :: xs) (count + 1)
      (x :: bubbledRest, newCount)
    else
      let (bubbledRest, newCount) := bubbleWithCount (x :: xs) (count + 1)
      (y :: bubbledRest, newCount)

def bubblesortWithCountAndFuel [LT T] [DecidableRel (LT.lt (α := T))] [BEq T] (l : List T) (n : Nat) : (List T × Nat × Nat) :=
  let rec iter (l : List T) (fuel : Nat) (count : Nat) : (List T × Nat × Nat) :=
    if fuel = 0 then (l, count, fuel)  -- Return the list, count, and remaining fuel as is when out of fuel
    else
      let (l', newCount) := bubbleWithCount l count
      if l' == l then (l, newCount, fuel)  -- List is sorted, so return it and remaining fuel
      else iter l' (fuel - 1) newCount  -- Continue sorting with one less fuel
  iter l n 0

def bubblesortWithCount [LT T] [DecidableRel (LT.lt (α := T))] [BEq T] (l : List T) : (List T × Nat) :=
  let rec iter (l : List T) (fuel : Nat) (count : Nat) : (List T × Nat) :=
    if fuel = 0 then (l, count)  -- Return the list, count, and remaining fuel as is when out of fuel
    else
      let (l', newCount) := bubbleWithCount l count
      if l' == l then (l, newCount)  -- List is sorted, so return it and remaining fuel
      else iter l' (fuel - 1) newCount  -- Continue sorting with one less fuel
  iter l l.length 0

#eval bubblesortWithCountAndFuel [4, 3, 1, 2, 5, 3, 4, 2] 5
#eval bubblesortWithCount [4, 3, 1, 2, 5, 3, 4, 2]

