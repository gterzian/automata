------------------------------ MODULE Rule_110 ------------------------------
EXTENDS FiniteSets, Integers
CONSTANT N
VARIABLES steps
-----------------------------------------------------------------------------
\* TLA+ spec for https://mathworld.wolfram.com/Rule110.html

Steps == 1..N
Cells == 1..N
None == 2

State == {None, 1, 0}

TypeOk == /\ steps \in [Steps \cup {0} -> [Cells -> State]]

\* Inductive invariant:
\* For a cell to be in the 1 state, it must either:
\* - Have a right neighbor in that state, 
\*    and be in the 0 state,
\*    at steps[step-1]
\* - Be in that state at steps[step-1]
\* - Have been initialized as such
Inv == \A step \in Steps: 
       \A cell \in Cells: 
            steps[step][cell] = 1 
            => LET
                  right_neighbor == IF cell +1 =< N THEN steps[step-1][cell+1] ELSE 0
               IN
               \/ step = 0
               \/ /\ step > 0 
                  /\ \/ /\ right_neighbor = 1  
                        /\ steps[step-1][cell] = 0
                     \/ /\ steps[step-1][cell] = 1                                                         
-----------------------------------------------------------------------------

\* Starting with a single rightmost black cell.
Init == /\ steps = [step \in Steps \cup {0} |-> 
            IF step > 0 THEN [cell \in Cells |-> None] 
            ELSE [cell \in Cells |-> IF cell < N THEN 0 ELSE 1 ]]

\* Note: cells can be updated for any step
\* in kind of parallel columns, so long as their neighbors and the cell itself
\* have been updated in all previous steps.
UpdateCell(step, cell) == LET
                              last_row == steps[step -1]
                              left_neighbor == IF cell -1 > 0 THEN last_row[cell-1] ELSE 0
                              right_neighbor == IF cell +1 =< N THEN last_row[cell+1] ELSE 0
                              old_state == last_row[cell]
                              new_state == CASE old_state = 1 /\ left_neighbor = 1 /\ right_neighbor = 1 -> 0
                                            []  old_state = 0 /\ right_neighbor = 1 -> 1
                                            [] OTHER -> last_row[cell]
                          IN 
                          /\ steps[step][cell] = None
                          /\ left_neighbor # None
                          /\ right_neighbor # None
                          /\ steps' = [steps EXCEPT ![step][cell] = new_state]
                                                 
        
Done == /\ \A step \in Steps: \A cell \in Cells: steps[step][cell] # None
        /\ UNCHANGED<<steps>>

Next == \/ \E step \in Steps: \E cell \in Cells: UpdateCell(step, cell)
        \/ Done
-----------------------------------------------------------------------------
Spec  ==  Init  /\  [][Next]_<<steps>>

THEOREM  Spec  =>  [](TypeOk /\ Inv)
=============================================================================