import LeanDag

/-! ## StateM Examples - State Read/Write Effects -/

structure Counter where
  value : Nat
  operations : Nat
  deriving Repr

def increment : StateM Counter Nat := do
  let s ← get
  let newValue := s.value + 1
  set { value := newValue, operations := s.operations + 1 : Counter }
  pure newValue

def double : StateM Counter Nat := do
  let s ← get
  let newValue := s.value * 2
  set { value := newValue, operations := s.operations + 1 : Counter }
  pure newValue

def counterSequence : StateM Counter Nat := do

  let v1 ← increment

  let v2 ← double
  let v3 ← increment
  pure (v1 + v2 + v3)

/-! ## ExceptT + StateM - Error Handling with State -/

structure Account where
  balance : Int
  deriving Repr

abbrev BankM := ExceptT String (StateM Account)

def deposit (amount : Nat) : BankM Nat := do
  let s ← get
  let newBalance := s.balance + amount
  set { balance := newBalance : Account }
  pure amount

def withdraw (amount : Nat) : BankM Nat := do
  let s ← get
  if s.balance < amount then
    throw s!"Insufficient funds: {s.balance}"
  else
    let newBalance := s.balance - amount
    set { balance := newBalance : Account }
    pure amount

def bankingScenario : BankM Int := do
  let _ ← deposit 100
  let _ ← withdraw 30
  let _ ← deposit 50
  let s ← get
  pure s.balance

/-! ## Option as a simple effect -/

def safeDivide (x y : Nat) : Option Nat :=
  if y == 0 then none else some (x / y)

def optionChain (a b c : Nat) : Option Nat := do
  let quotient ← safeDivide a b
  let root ← safeDivide quotient 2
  let final ← safeDivide (root + c) 2
  pure (final * 3)
