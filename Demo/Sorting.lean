def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x ≤ y
      then x :: merge xs (y :: ys)
      else y :: merge (x :: xs) ys

def split : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
      let (left, right) := split rest
      (x :: left, y :: right)

partial def mergeSort (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | [x] => [x]
  | _ =>
      let (left, right) := split xs
      merge (mergeSort left) (mergeSort right)
termination_by xs.length

def partition (pivot : Nat) (xs : List Nat) : List Nat × List Nat :=
  xs.foldl (fun (less, greater) x =>
    if x < pivot then (x :: less, greater) else (less, x :: greater))
    ([], [])

partial def quickSort : List Nat → List Nat
  | [] => []
  | pivot :: rest =>
      let (less, greater) := partition pivot rest

      quickSort less ++ [pivot] ++ quickSort greater
termination_by xs => xs.length

def bubblePass : List Nat → List Nat × Bool
  | [] => ([], false)
  | [x] => ([x], false)
  | x :: y :: rest =>
      if x > y then
        let (sorted, _) := bubblePass (x :: rest)
        (y :: sorted, true)
      else
        let (sorted, swapped) := bubblePass (y :: rest)
        (x :: sorted, swapped)

partial def bubbleSort (xs : List Nat) : List Nat :=
  let (result, swapped) := bubblePass xs
  if swapped then bubbleSort result else result

def isSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && isSorted (y :: rest)

def testList : List Nat := [64, 34, 25, 12, 22, 11, 90, 5, 77, 30]

#eval insertionSort testList
#eval mergeSort testList
#eval quickSort testList
#eval bubbleSort testList

#eval isSorted (insertionSort testList)
#eval isSorted (mergeSort testList)
#eval isSorted (quickSort testList)
#eval isSorted (bubbleSort testList)

structure SortResult where
  name : String
  input : List Nat
  output : List Nat
  sorted : Bool
  deriving Repr

def runSort (name : String) (sortFn : List Nat → List Nat) (xs : List Nat) : SortResult :=
  let result := sortFn xs
  { name := name, input := xs, output := result, sorted := isSorted result }

def allSorts (xs : List Nat) : List SortResult :=
  [ runSort "Insertion Sort" insertionSort xs
  , runSort "Merge Sort" mergeSort xs
  , runSort "Quick Sort" quickSort xs
  , runSort "Bubble Sort" bubbleSort xs
  ]

#eval allSorts testList

def main : IO Unit := do
  IO.println "Sorting Algorithm Comparison"
  IO.println "============================"
  IO.println s!"Input: {testList}"
  IO.println ""

  let results := allSorts testList
  for r in results do
    IO.println s!"{r.name}:"
    IO.println s!"  Output: {r.output}"
    IO.println s!"  Sorted: {r.sorted}"
    IO.println ""
