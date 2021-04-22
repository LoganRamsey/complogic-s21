import .arith_expr

/-
A little PL in which we have mutable
state and an update (assignment) operation.
-/

/-
We don't have mutable state in a pure functional language
-/
def x := 1
-- def x := 2


-- structure avar : Type := (idx : nat)

def X := avar.mk 0
def Y := avar.mk 1
def Z := avar.mk 2

def init : a_state := λ (v : avar), 0

/-
{ (X,0), (Y,0), (Z,0), ... }  st
X = 7;
{ (X,7), (Y,0), (Z,0), ... } st'
Y = 8
{ (X,7), (Y,8), (Z,0), ... } st'' 
Z = 9
{ (X,7), (Y,8), (Z,9), ... } st'''
X = 10
{ (X,10), (Y,8), (Z,9), ... } st'''


Π (v : avar), if v = X then st' v = 7 else st' v = st v
-/

def var_eq : avar → avar → bool 
| (avar.mk n1) (avar.mk n2) := n1 = n2 


def override : a_state → avar → aexp → a_state 
| st v exp := 
    λ (v' : avar), 
      if (var_eq v v') 
      then (aeval exp st) 
      else (st v')


def st' := override init X [7]

#eval st' X
#eval st' Y
#eval st' Z

def st'' := override st' Y [8]

#eval st'' X
#eval st'' Y
#eval st'' Z

def st''' := override st'' Z [9]

#eval st''' X
#eval st''' Y
#eval st''' Z
 

 def st'''' := override st''' X [10]

#eval st'''' X
#eval st'''' Y
#eval st'''' Z


inductive cmd : Type
| assn (v : avar) (e : aexp) 
| seq (c1 c2 : cmd) : cmd

open cmd

notation v = a := assn v a 
notation c1 ; c2  := seq c1 c2 


def a1 := X = [7]
def a2 := Y = [8]
def a3 := Z = [9]
def a4 := X = [10]

def c_eval : a_state → cmd → a_state
| st (assn v e) := override st v e
| st (seq c1 c2) := c_eval (c_eval st c1) c2 
/-
We implement assignment using function override,
converting a given (initial) state into a new state
by binding a given variable to the value of a given
arithmetic expression.

We implement sequential composition of c1 and c2 by 
evaluating c2 in the state obtained by evaluating
c1 in the given (initial) state.
-/


def program :=
  X = [7];
  Y = [8];
  Z = [9];
  X = [10]

def res := c_eval init program

#reduce res X
#reduce res Y
#reduce res Z

-- Yay!



 