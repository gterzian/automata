--------------------------- MODULE Rule_110_Step ---------------------------
EXTENDS FiniteSets, Integers
CONSTANT N
VARIABLES steps
-----------------------------------------------------------------------------
\* TLA+ spec for the original description of https://mathworld.wolfram.com/Rule110.html
\* which only allows for cells to be updated in parallel for the current step.

Steps == 1..N
Cells == 1..N
None == 2

State == {None, 1, 0}

CurrentStepBar == LET F[step \in Steps \cup {0}]
                        == IF \A cell \in Cells: steps[step][cell] # None
                                THEN step + 1
                                ELSE F[step-1]
                                           
                  IN  F[N]

TypeOk == /\ steps \in [Steps \cup {0} -> [Cells -> State]]
                     
NewState[cell \in Cells] == LET 
                              current_step == CurrentStepBar
                              last_row == steps[current_step -1]
                              old_state == last_row[cell]
                              left_neighbor == IF cell -1 > 0 THEN last_row[cell-1] ELSE last_row[N]
                              right_neighbor == IF cell +1 =< N THEN last_row[cell+1] ELSE last_row[1]
                            IN
                            CASE old_state = 1 /\ left_neighbor = 1 /\ right_neighbor = 1 -> 0
                                 []  old_state = 0 /\ right_neighbor = 1 -> 1
                                 [] OTHER -> last_row[cell]                                                        
-----------------------------------------------------------------------------
\* Starting with a single rightmost black cell.
Init == /\ steps = [step \in Steps \cup {0} |-> 
            IF step > 0 THEN [cell \in Cells |-> None] 
            ELSE [cell \in Cells |-> IF cell < N THEN 0 ELSE 1 ]]

\* Note: cells can be updated only for the current step.
Update == LET
            current_step == CurrentStepBar
          IN
          /\ steps' = [steps EXCEPT ![current_step] = [cell \in Cells |-> NewState[cell]]]
          /\ current_step' = current_step + 1 
        
Done == /\ \A step \in Steps: \A cell \in Cells: steps[step][cell] # None
        /\ UNCHANGED<<steps>>

Next == \/ \E step \in Steps: \E cell \in Cells: Update
        \/ Done
-----------------------------------------------------------------------------
PerStepSpec  ==  Init  /\  [][Next]_<<steps>>

THEOREM  PerStepSpec  =>  [](TypeOk)
=============================================================================