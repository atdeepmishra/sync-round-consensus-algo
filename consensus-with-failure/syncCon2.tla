------------------------------ MODULE syncCon2 ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT N, FAILNUM
ASSUME N <= 5  /\ 0 <= FAILNUM /\ FAILNUM <= 2
Nodes == 1..N

(*
--algorithm syncCon2
{
      variable FailNum = FAILNUM, 
              up = [n \in Nodes |-> TRUE],
              pt = [n \in Nodes |-> 0],
              t = [n \in Nodes |-> FALSE],
              d = [n \in Nodes |-> -1],
              mb = [n \in Nodes |-> {}],
              Fail = FailNum;
              
              
    define {
    SetMin(S) == CHOOSE i \in S: \A j \in S : i <= j
    UpNodes == { n \in Nodes : up[n]=TRUE }
    CheckNodesRound(n) ==  {\A i \in UpNodes : pt[i]=pt[n]}
    
    }
    
    macro MaybeFail( ){
        if( FailNum > 0 /\ up[self] )
            { either 
                { up[self] := FALSE; FailNum := FailNum - 1; } 
                  or skip; } ;
        
    }
    
    fair process ( n \in Nodes )
    variable v = 0, pv = 0, Q = {}, pmb_count=0, r=1;           \*\*"pmb_count" is used to keep the info of how many nodes sent me the mail in previous step
    {                                                           \*\* "pv" holds the previous minimum value decided by node
                                                                \*\* "r" is the round counter needed for the node. the round stops when it becomes 0
P:  while (up[self] /\ r>0) {         \*\* next round is executed when node is up and round counter is set to 0                         
        
        if(pt[self]=0) {v:=self;};      \*\* set the v to self for first round else the previous decision
        else {v:=d[self]};
        Q := Nodes;                     \*\* set the Q to all nodes for sending the message
PS: while(up[self] /\ Q # {}) {
        with(p \in Q) {
            mb[p]:= mb[p] \union {v}; \*\* Append the value of self nede to message bus of p node
            Q := Q \{p};              \*\* Remove the p from Q to send message to other nodes
            MaybeFail();              \*\* Call fail macro to fail the node if FailNum has not reached the maximum limit
        };
    };
    
    if(up[self]) pt[self] := pt[self]+1; \*\* Move to next round
    

PR: await (up[self] /\ (\A k \in UpNodes: pt[self]<=pt[k]));                 \*\* Execute receive step only if the node is up
    {   
        pv:=d[self];                    \*\* stor the value of previous decision in pv
        d[self]:=SetMin(mb[self]);  \*\* Set the decision to the minimum value received by all the nodes
        
        
        \*\* the below condition checks for message count in previous round and current round. Also, the if the decision varies from last round.
        \*\* if any of the condition differs I need another round to make sure I get the minimum value
        if(pmb_count # Cardinality(mb[self]) \/ pv # d[self]) r:=1;
        else r:=r-1;
        
        pmb_count:=Cardinality(mb[self]);  \*\* set the message count of current step to pmb_count
        mb[self]:={};                   \*\* clear the mailbox for next round
        
        if(r=0) t[self]:=TRUE;          \*\* when no more rounds are needed for the current node terminate the node
        
    } \*await
  
    }  \* while 

    }    \* process
    
} \* algorithm
  
*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, pt, t, d, mb, Fail, pc

(* define statement *)
SetMin(S) == CHOOSE i \in S: \A j \in S : i <= j
UpNodes == { n \in Nodes : up[n]=TRUE }
CheckNodesRound(n) ==  {\A i \in UpNodes : pt[i]=pt[n]}

VARIABLES v, pv, Q, pmb_count, r

vars == << FailNum, up, pt, t, d, mb, Fail, pc, v, pv, Q, pmb_count, r >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ pt = [n \in Nodes |-> 0]
        /\ t = [n \in Nodes |-> FALSE]
        /\ d = [n \in Nodes |-> -1]
        /\ mb = [n \in Nodes |-> {}]
        /\ Fail = FailNum
        (* Process n *)
        /\ v = [self \in Nodes |-> 0]
        /\ pv = [self \in Nodes |-> 0]
        /\ Q = [self \in Nodes |-> {}]
        /\ pmb_count = [self \in Nodes |-> 0]
        /\ r = [self \in Nodes |-> 1]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF up[self] /\ r[self]>0
                 THEN /\ IF pt[self]=0
                            THEN /\ v' = [v EXCEPT ![self] = self]
                            ELSE /\ v' = [v EXCEPT ![self] = d[self]]
                      /\ Q' = [Q EXCEPT ![self] = Nodes]
                      /\ pc' = [pc EXCEPT ![self] = "PS"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << v, Q >>
           /\ UNCHANGED << FailNum, up, pt, t, d, mb, Fail, pv, pmb_count, r >>

PS(self) == /\ pc[self] = "PS"
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ mb' = [mb EXCEPT ![p] = mb[p] \union {v[self]}]
                            /\ Q' = [Q EXCEPT ![self] = Q[self] \{p}]
                            /\ IF FailNum > 0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ FailNum' = FailNum - 1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<FailNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << FailNum, up >>
                       /\ pc' = [pc EXCEPT ![self] = "PS"]
                       /\ pt' = pt
                  ELSE /\ IF up[self]
                             THEN /\ pt' = [pt EXCEPT ![self] = pt[self]+1]
                             ELSE /\ TRUE
                                  /\ pt' = pt
                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ UNCHANGED << FailNum, up, mb, Q >>
            /\ UNCHANGED << t, d, Fail, v, pv, pmb_count, r >>

PR(self) == /\ pc[self] = "PR"
            /\ (up[self] /\ (\A k \in UpNodes: pt[self]<=pt[k]))
            /\ pv' = [pv EXCEPT ![self] = d[self]]
            /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
            /\ IF pmb_count[self] # Cardinality(mb[self]) \/ pv'[self] # d'[self]
                  THEN /\ r' = [r EXCEPT ![self] = 1]
                  ELSE /\ r' = [r EXCEPT ![self] = r[self]-1]
            /\ pmb_count' = [pmb_count EXCEPT ![self] = Cardinality(mb[self])]
            /\ mb' = [mb EXCEPT ![self] = {}]
            /\ IF r'[self]=0
                  THEN /\ t' = [t EXCEPT ![self] = TRUE]
                  ELSE /\ TRUE
                       /\ t' = t
            /\ pc' = [pc EXCEPT ![self] = "P"]
            /\ UNCHANGED << FailNum, up, pt, Fail, v, Q >>

n(self) == P(self) \/ PS(self) \/ PR(self)

Next == (\E self \in Nodes: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
\*\* Below property is for termination
FinalState == TRUE ~> (\A i \in Nodes: up[i]=TRUE => t[i]=TRUE)
-----------------------------------------------------------------------------
\*\* Below are the invariants
Agg == \A i,j \in Nodes : (t[i]/\t[j]) => (d[i]=d[j])
Validity == (\E k \in Nodes: (\A i \in Nodes : v[i]=k)) => (\A j \in Nodes: t[j]=TRUE => d[j]=v[j])

Inv == Agg /\ Validity



=============================================================================
\* Modification History
\* Last modified Tue Oct 24 23:43:54 EDT 2017 by Deep
\* Created Tue Oct 24 20:54:28 EDT 2017 by Deep

\* DEEP NARAYAN MISHRA - PERSON NO 50245878

\* As we know the Aggrement property and validitiy will fail if there is any node failure while sending
\* the message to other nodes. Single round will not help to reach the consensue by all the parties.
\* 
\*
\*
\* In brief - we need to run for multiple rounds to establish the consences. However, every nodes need 
\* to identify when to go for the next round and when to stop.
\*
\* This problem can be solved by observing the behaviour of nodes' mail box and the decision in any two
\* consecutive rounds of the node. If we closly monitor both these properties. If there is any failure the message count received 
\* by a node will be lesser than the previous round. Or the decision made in previous round would be different from 
\* current round decision of a node.
\* In general, either of the parameters will differ is there is any failure. By looking at the difference in both the
\* property (mail box size, and decisions) of the node we can identify whether to go for next round or not.
\*
\*
\*
\* Based on the above analogy, I have two extra varibles (pmb_count : previous mail box count) and  (pv : previous
\* decisions). If there is difference in any of these parameters I am setting the round marker (r: round count) to 1.
\* If none of the prameters changes we are assure of no failure and no further rounds need. Hence setting r to 0.
