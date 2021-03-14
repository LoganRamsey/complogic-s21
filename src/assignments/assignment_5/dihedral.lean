inductive Action : Type
| R0
| R90
| R180
| R270
| H
| V
| D
| D'

open Action

def comp : Action → Action → Action
| R0 a := a
| a R0 := a
| R90 R90 := R180
| R90 R180 := R270
| R90 R270 := R0
| R90 H := D'
| R90 V := D
| R90 D := H
| R90 D' := V
| R180 R90 := R270
| R180 R180 := R0
| R180 R270 := R90
| R180 H := V
| R180 V := H
| R180 D := D'
| R180 D' := D
| R270 R90 := R0
| R270 R180 := R90
| R270 R270 := R180 
| R270 H := D
| R270 V := D'
| R270 D := V
| R270 D' := H
| H R90 := D
| H R180 := V
| H R270 := D'
| H H := R0
| H V := R180
| H D := R90
| H D' := R270
| V R90 := D'
| V R180 := H
| V R270 := D
| V H := R180
| V V := R0
| V D := R270
| V D' := R90
| D R90 := V
| D R180 := D'
| D R270 := H
| D H := R270
| D V := R90
| D D := R0
| D D' := R180
| D' R90 := H
| D' R180 := D
| D' R270 := V
| D' H := R90
| D' V := R270
| D' D := R180
| D' D' := R0

def comp_list : list Action → Action
| [] := R0
| l := list.foldr comp R0 l

#reduce comp_list [R90, R90, H]
#reduce comp_list [V, D', R270]