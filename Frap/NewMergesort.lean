import Mathlib.Tactic.Linarith

--
-- Define correctness for sorting algorithms
--

-- list is sorted, i.e. no element is smaller than its predecessor
inductive Sorted [LT T] : List T -> Prop
  | nil : Sorted []
  | singleton : forall {x}, Sorted [x]
  | cons : forall {a b xs}, Sorted (b :: xs) -> Not (b < a) -> Sorted (a :: b :: xs)

-- counts the elements equal to t in l
def count [DecidableEq T] (l : List T) (t : T) : Nat :=
  match l with
  | [] => 0
  | x :: xs => (if x = t then 1 else 0) + count xs t

-- l and m are permutations of each other, i.e. they contain the same amount of each value
def Permut [DecidableEq T] (l m : List T) : Prop := forall t, count l t = count m t

-- a sorting algorithm is correct iff it each output is a sorted permutation of the input
def SortCorrect [Preorder T] [DecidableEq T] [DecidableRel (LT.lt (α := T))] (sort : List T -> List T) : Prop :=
  forall l, And (Sorted (sort l)) (Permut (sort l) l)

--
-- Lemmas for correctness propositions
--

lemma Sorted.nlt [LT T] {a b : T} {l : List T} (s : Sorted (a :: b :: l)) : Not (b < a) := by
  cases s with
  | cons _ a => exact a

lemma Sorted.sub [LT T] {x : T} {xs : List T} (s : Sorted (x :: xs)) : Sorted xs := by
  cases s with
  | singleton => exact Sorted.nil
  | cons p => exact p

lemma Permut.refl [DecidableEq T] {l : List T} : Permut l l :=
  by unfold Permut; intros; rfl
lemma Permut.symm [DecidableEq T] {l m : List T} (p : Permut l m) : Permut m l :=
  by unfold Permut at *; intros; symm; apply p
lemma Permut.trans [DecidableEq T] {a b c : List T} (ab : Permut a b) (bc : Permut b c) : Permut a c :=
  by unfold Permut at *; intros; rw [ab]; apply bc;

lemma count_app [DecidableEq T] {a b : List T} {t : T} : count (a ++ b) t = count a t + count b t := by
  induction a with
  | nil => simp; rfl;
  | cons _ _ IH => simp; rw [count, count, IH, Nat.add_assoc]

lemma Permut.app [DecidableEq T] {a b c d : List T} (ac : Permut a c) (bd : Permut b d) : Permut (a ++ b) (c ++ d) := by
  unfold Permut
  intros t
  rw [count_app, count_app]
  rw [ac t, bd t]

--
-- Implement mergesort
--

def left (l : List T) : List T := List.take (l.length / 2) l
def right (l : List T) : List T := List.drop (l.length / 2) l

def merge [LT T] [DecidableRel (LT.lt (α := T))] : List T -> List T -> List T
  | [], l => l
  | l, [] => l
  | x :: xs, y :: ys => if x < y
      then x :: merge xs (y :: ys)
      else y :: merge (x :: xs) ys

lemma left_less (l : List T) (p : l.length > 0) : (left l).length < l.length := by
  unfold left
  simp
  exact Nat.div_lt_self p Nat.one_lt_two
lemma right_less (l : List T) (p : l.length > 1) : (right l).length < l.length := by
  unfold right
  simp
  apply And.intro
  . omega
  . omega

def mergesort [LT T] [DecidableRel (LT.lt (α := T))] (l : List T) : List T :=
  if l.length < 2 then l
  else
    have := left_less l
    have := right_less l
    merge (mergesort (left l)) (mergesort (right l))
termination_by l.length

def mergeWithCount [LT T] [DecidableRel (LT.lt (α := T))] : List T → List T → Nat → (List T × Nat)
  | [], l, count => (l, count)
  | l, [], count => (l, count)
  | x :: xs, y :: ys, count =>
    if x < y then
      let (mergedRest, newCount) := mergeWithCount xs (y :: ys) (count + 1)
      (x :: mergedRest, newCount)
    else
      let (mergedRest, newCount) := mergeWithCount (x :: xs) ys (count + 1)
      (y :: mergedRest, newCount)

def mergesortWithCount [LT T] [DecidableRel (LT.lt (α := T))] (l : List T) : (List T × Nat) :=
  if l.length < 2 then (l, 0)
  else
    have := left_less l
    have := right_less l
    let (leftSorted, leftCount) := mergesortWithCount (left l)
    let (rightSorted, rightCount) := mergesortWithCount (right l)
    let (mergedList, mergeCount) := mergeWithCount leftSorted rightSorted (leftCount + rightCount)
    (mergedList, mergeCount)
termination_by l.length

def mergesortWithCountWithFuel [LT T] [DecidableRel (LT.lt (α := T))] (l : List T) (fuel : Nat) : (List T × Nat × Nat) :=
  if l.length < 2 then (l, 0, fuel)
  else if fuel = 0 then (l, 0, fuel)
  else
    have := left_less l
    have := right_less l
    let (leftSorted, leftCount, leftFuel) := mergesortWithCountWithFuel (left l) (fuel / 2)
    let (rightSorted, rightCount, rightFuel) := mergesortWithCountWithFuel (right l) (fuel / 2)
    let (mergedList, mergeCount) := mergeWithCount leftSorted rightSorted (leftCount + rightCount)
    (mergedList, mergeCount, leftFuel + rightFuel)

#eval mergesortWithCount [1 , 5 , 2 , 3 , 2]
#eval mergesortWithCountWithFuel [1 , 5 , 2 , 3 , 2 , 5  , 6 , 1] 8

--
-- Verify mergesort
--

lemma merge_sorted [Preorder T] [DecidableRel (LT.lt (α := T))] {xs ys : List T} (sxs : Sorted xs) (sys : Sorted ys)
    : Sorted (merge xs ys) := by
  induction xs generalizing ys with
  | nil => unfold merge; simp; exact sys
  | cons x xs IHx =>
    induction ys with
    | nil => unfold merge; exact sxs
    | cons y ys IHy =>
      unfold merge
      by_cases p : (x < y)
      all_goals simp [p]
      cases xs with
      | nil => unfold merge; exact Sorted.cons sys (lt_asymm p)
      | cons xx xxs =>
        have ss := IHx (Sorted.sub sxs) sys
        unfold merge; unfold merge at ss
        by_cases pp : (xx < y)
        all_goals (simp [pp]; simp [pp] at ss)
        exact Sorted.cons ss (Sorted.nlt sxs)
        exact Sorted.cons ss (lt_asymm p)
      cases ys with
      | nil => unfold merge; exact Sorted.cons sxs p
      | cons yy yys =>
        have ss := IHy (Sorted.sub sys)
        unfold merge; unfold merge at ss;
        by_cases pp : (x < yy)
        all_goals (simp [pp]; simp [pp] at ss)
        exact Sorted.cons ss p
        exact Sorted.cons ss (Sorted.nlt sys)

lemma mergesort_sorted [Preorder T] [DecidableRel (LT.lt (α := T))] (l : List T)
    : Sorted (mergesort l) :=
  if p : l.length < 2
  then by
    unfold mergesort
    simp [p]
    cases l with
    | nil => exact Sorted.nil
    | cons x xs => cases xs with
      | nil => exact Sorted.singleton
      | cons => contradiction
  else
    have := left_less l
    have := right_less l
    have := merge_sorted (mergesort_sorted (left l)) (mergesort_sorted (right l))
    by unfold mergesort; simp [p]; exact this
termination_by l.length

lemma merge_permut [LT T] [DecidableEq T] [DecidableRel (LT.lt (α := T))] (xs ys : List T)
    : Permut (merge xs ys) (xs ++ ys) := by
  induction xs generalizing ys with
  | nil => unfold merge; simp; exact Permut.refl
  | cons x xs IHx => induction ys with
    | nil => unfold merge; simp; exact Permut.refl
    | cons y ys IHy =>
      unfold merge
      by_cases p : x < y
      all_goals (simp [p]); unfold Permut; intros t
      rw [count, count, IHx (y :: ys) t]
      nth_rw 1 [count]
      rw [IHy t, <-List.cons_append, count_app, count_app]
      nth_rw 3 [count]
      linarith

lemma mergesort_permut [LT T] [DecidableEq T] [DecidableRel (LT.lt (α := T))] (l : List T)
    : Permut (mergesort l) l :=
  if p : l.length < 2
  then by
    unfold mergesort
    simp [p]
    exact Permut.refl
  else
    have := left_less l
    have := right_less l
    have pl := mergesort_permut (left l)
    have pr := mergesort_permut (right l)
    by
      unfold mergesort
      simp [p]
      apply Permut.trans (merge_permut _ _)
      apply Permut.trans (Permut.app pl pr)
      unfold left right
      rewrite [List.take_append_drop]
      exact Permut.refl
termination_by l.length

theorem mergesort_correct (T : Type) [Preorder T] [DecidableEq T] [DecidableRel (LT.lt (α := T))]
    : SortCorrect (mergesort : List T -> List T) := by
  intros l
  constructor
  exact mergesort_sorted l
  exact mergesort_permut l


  --
  -- Implement bubblesort
  --

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

#eval bubblesortWithCountAndFuel [4, 3, 1, 2, 5 , 3 , 4 , 2] 6
#eval bubblesortWithCount [4, 3, 1, 2, 5 , 3 , 4 , 2]
