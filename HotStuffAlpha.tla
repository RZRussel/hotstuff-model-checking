--------------------------- MODULE HotStuffAlpha ---------------------------
(*
Here we omit type part in QC
*)

EXTENDS Integers, FiniteSets

(********************* PROTOCOL PARAMETERS **********************************)
CONSTANT
   Corr,          \* the set of correct processes
   Byzantine,     \* the set of byzantine processes, may be empty
   N,             \* the total number of processes: correct, defective, and Byzantine
   T,             \* an upper bound on the number of Byzantine processes
   MaxView,       \* the maximal view number
   Leader         \* the leader function from 0..NViews to 1..N

F == Cardinality(Byzantine)

ASSUME(N = Cardinality(Corr \union Byzantine))

(********************* TYPE ANNOTATIONS FOR APALACHE *************************)
\* the operator for type annotations
a <: b == a

\* the type of quorum sertificate
QCT == [viewNumber |-> Int, node |-> STRING] \* qc.sig - ommited

\* type annotations

SetOfQCs(S) == S <: {QCT}

EmptyQCsSet == {} <: {QCT}

(*************************** DEFINITIONS ************************************)
AllProcs == Corr \union Byzantine      \* the set of all processes

Views == 0..MaxView                 \* the set of potential rounds
NilView == 0   \* a special value to denote a nil round, outside of Views
ViewsOrNil == Views \union {NilView} \* this is dumb

(* nodes logic *)

MaxNode == 2^(MaxView + 1) - 1
Nodes == 2..MaxNode \* the set of all nodes
NilNode == 1  \* a special value (_|_ in paper)
NodesOrNil == Nodes \union {NilNode}

BranchFrom == [n \in NodesOrNil |-> [pn \in NodesOrNil |-> (n = pn * 2 \/ n = (pn * 2) + 1)]]

\*logic for tree structure
\* IsPowerOfTwo == [n \in NodesOrNil |-> \A d \in NodesOrNil : (n % d = 0) => (d % 2 = 0)]
LowerPowTwo == [n \in NodesOrNil |-> CHOOSE d \in 0..n :
                                        /\ n >= 2 ^ d
                                        /\ \A ad \in 1..n : (n >= 2 ^ ad) => (d >= ad)]
\* childrens in tree structure
NextNodes == [n \in NodesOrNil |-> {2 * n, 2 * n + 1}]

\* The validity predicate
ExtendsFrom == [n \in NodesOrNil |-> [pn \in NodesOrNil |-> 
                                          \E k \in ViewsOrNil :
                                          \E r \in 1..MaxNode : 
                                             r < 2 ^ k /\ n = pn * (2 ^ k) + r]]

(* nodes logic *)

Phases == {"PREPARE", "PRECOMMIT", "COMMIT", "DECIDE", "NEW-VIEW"}
PhasesExtended == Phases \union {"PREPARE'", "STOP"}

QCs == [viewNumber : ViewsOrNil, node : NodesOrNil] <: {QCT} 
NilQC == [viewNumber |-> NilView, node |-> NilNode] <: QCT \* _|_
QCsOrNil == QCs \union SetOfQCs({NilQC})

\* the two thresholds that are used in the algorithm
WEAK_THRESHOLD == T + 1     \* at least one process is not faulty
STRONG_THRESHOLD == N - T \* a quorum when having N > 3 * T

(********************* PROTOCOL STATE VARIABLES ******************************)
VARIABLES
  curView,    \* a process round number: Corr -> Views
  phase,     \* a process phase: Corr -> { "PREPARE", "PRECOMMIT", "COMMIT", "DECIDE" }
  decision, \* process decision: Corr -> QCsOrNilQC
  lockedQC,  \* a locked value: Corr -> QCsOrNil
  prepareQC   \* a valid value: Corr -> QCsOrNil

\* book-keeping variables
VARIABLES
  msgsNewViewJustify,      \* msgs : src -> view -> set_of_QCs
  msgsPrepareJustify,      \* msgs : src -> view -> node -> set_of_QCs
  \* because we really need only them as msgs + QCs
  QCsMsgsCount,            \* Count : view -> node -> Int how many msgs were sent that can form that QC
  QCsFormed,                \* for byzantine
  lastDecision
 
\* a handy definition used in UNCHANGED
vars == <<curView, phase, decision, lockedQC, QCsFormed, lastDecision,
          prepareQC, msgsNewViewJustify, msgsPrepareJustify, QCsMsgsCount>>
                                         
(************************ TYPE INVARIANT ************************************)

(* the standard type invariant *)
TypeOK ==
    /\ curView \in [Corr -> Views]
    /\ phase \in [Corr -> PhasesExtended]
    /\ decision \in [Views -> [Corr -> NodesOrNil]]
    /\ lockedQC \in [Corr -> QCsOrNil]
    /\ prepareQC \in [Corr -> QCsOrNil]
    /\ msgsNewViewJustify \in [AllProcs -> [Views -> SUBSET QCsOrNil]]
    /\ msgsPrepareJustify \in [AllProcs -> [Views -> [NodesOrNil -> SUBSET QCsOrNil]]]
    /\ QCsMsgsCount \in [Phases -> [Views -> [NodesOrNil -> Int]]]
    /\ QCsFormed \in [Views -> [NodesOrNil -> BOOLEAN]]
    /\ lastDecision \in [Corr -> NodesOrNil]

(************************ PROTOCOL INITIALIZATION ******************************)

InitFuncForNewViewJustify(s, v) ==
   IF s \in Corr
   THEN IF v = 0
        THEN SetOfQCs({NilQC})
        ELSE EmptyQCsSet
   ELSE SetOfQCs({NilQC})

InitFuncForPrepareJustify(s, v, n) ==
   IF s \in Byzantine \* /\ ExtendsFrom[n][NilNode]
   THEN SetOfQCs({NilQC})
   ELSE EmptyQCsSet

Init ==
    /\ curView = [p \in Corr |-> 1]
    /\ phase = [p \in Corr |-> "PREPARE"]
    /\ decision = [v \in Views |-> [p \in Corr |-> NilNode]]
    /\ lockedQC = [p \in Corr |-> NilQC]
    /\ prepareQC = [p \in Corr |-> NilQC]
    /\ msgsNewViewJustify = [s \in AllProcs |-> [v \in Views |-> InitFuncForNewViewJustify(s, v)]]
    /\ msgsPrepareJustify = [s \in AllProcs |-> [v \in Views |-> [n \in NodesOrNil |-> 
                                                       InitFuncForPrepareJustify(s, v, n)]]]
    /\ QCsMsgsCount = [t \in Phases |-> [v \in ViewsOrNil |-> [n \in NodesOrNil |-> F]]]
    /\ QCsFormed = [[v \in Views |-> [n \in NodesOrNil |-> FALSE]] EXCEPT ![NilView][NilNode] = TRUE]
    /\ lastDecision = [p \in Corr |-> NilNode]
        
(************************ PROTOCOL TRANSLATION ******************************)

\* PREPARE phase

\* line 2 - 6
PreparePhaseAsLeader(p) ==
   /\ phase[p] = "PREPARE"
   /\ p = Leader[curView[p]] \* line 2 
   /\ \E Msrc \in SUBSET AllProcs :
      /\ Cardinality(Msrc) >= STRONG_THRESHOLD \*
      /\ \A s \in Msrc : msgsNewViewJustify[s][curView[p] - 1] /= EmptyQCsSet
      /\ \E s \in Msrc : \E highQC \in msgsNewViewJustify[s][curView[p] - 1]  :
         /\ \A otherSrc \in Msrc : \E qc \in msgsNewViewJustify[otherSrc][curView[p] - 1] :
            \/ otherSrc = s \* because we picked all QCs of all buckets
            \/ highQC.viewNumber \geq qc.viewNumber
         /\ \E newNode \in NextNodes[highQC.node] : 
            msgsPrepareJustify' = [msgsPrepareJustify EXCEPT ![p][curView[p]][newNode] = msgsPrepareJustify[p][curView[p]][newNode] \union {highQC}]
         \* here we use only one branch /\
   /\ phase' = [phase EXCEPT ![p] = "PREPARE'"]
   /\ UNCHANGED <<curView, decision, lockedQC, QCsFormed, lastDecision,
          prepareQC, msgsNewViewJustify, QCsMsgsCount>>
          
\* line 7 - 10
PreparePhaseAsReplica(p) ==
   /\ (phase[p] = "PREPARE" /\ p /= Leader[curView[p]]) \/ phase[p] = "PREPARE'"
   /\ \E n \in NodesOrNil :  \E qc \in msgsPrepareJustify[Leader[curView[p]]][curView[p]][n] :
      /\ IF BranchFrom[n][qc.node] /\ (ExtendsFrom[n][lockedQC[p].node] \/ qc.viewNumber > lockedQC[p].viewNumber) \* HERE WE USE BRANCH, NOT EXTENDS
         THEN QCsMsgsCount' = [QCsMsgsCount EXCEPT !["PREPARE"][curView[p]][n] = QCsMsgsCount["PREPARE"][curView[p]][n] + 1]
         ELSE QCsMsgsCount' = QCsMsgsCount
      /\ phase' = [phase EXCEPT ![p] = "PRECOMMIT"]
      /\ UNCHANGED <<curView, decision, lockedQC, QCsFormed, lastDecision,
          prepareQC, msgsNewViewJustify, msgsPrepareJustify>>

\* PRECOMMIT phase
          
\* line 15 - 18
PrecommitPhaseAsReplica(p) ==
   /\ phase[p] = "PRECOMMIT"
   /\ \E n \in NodesOrNil : LET qc == [viewNumber |-> curView[p], node |-> n] IN
      /\ QCsMsgsCount["PREPARE"][curView[p]][n] >= STRONG_THRESHOLD
      /\ prepareQC' = [prepareQC EXCEPT ![p] = qc] \* line 17
      /\ phase' = [phase EXCEPT ![p] = "COMMIT"]
      /\ QCsMsgsCount' = [QCsMsgsCount EXCEPT !["PRECOMMIT"][curView[p]][qc.node] = QCsMsgsCount["PRECOMMIT"][curView[p]][qc.node] + 1]
      /\ UNCHANGED <<curView, decision, lockedQC, QCsFormed, lastDecision,
          msgsNewViewJustify, msgsPrepareJustify>>


\* COMMIT phase

\* line 23 - 26 
CommitPhaseAsReplica(p) ==
   /\ phase[p] = "COMMIT"
   /\ \E n \in NodesOrNil : LET qc == [viewNumber |-> curView[p], node |-> n] IN
      /\ QCsMsgsCount["PRECOMMIT"][curView[p]][n] >= STRONG_THRESHOLD
      /\ lockedQC' = [lockedQC EXCEPT ![p] = qc] \* line 25
      /\ phase' = [phase EXCEPT ![p] = "DECIDE"]
      /\ QCsMsgsCount' = [QCsMsgsCount EXCEPT !["COMMIT"][curView[p]][qc.node] = QCsMsgsCount["COMMIT"][curView[p]][qc.node] + 1]
      /\ UNCHANGED <<curView, decision, QCsFormed, lastDecision,
          prepareQC, msgsNewViewJustify, msgsPrepareJustify>>

\* DECIDE phase

\* line 31- 34
DecidePhaseAsReplica(p) ==
   /\ phase[p] = "DECIDE" \* There is a very strange line here - wait for message m from leader(curView)
   /\ \E n \in NodesOrNil : LET qc == [viewNumber |-> curView[p], node |-> n] IN
      /\ QCsMsgsCount["COMMIT"][curView[p]][n] >= STRONG_THRESHOLD
      /\ phase' = [phase EXCEPT ![p] = "NEW-VIEW"]
      /\ decision' = [decision EXCEPT ![curView[p]][p] = lockedQC[p].node]
      /\ lastDecision' = [lastDecision EXCEPT ![p] = lockedQC[p].node]
      /\ QCsMsgsCount' = [QCsMsgsCount EXCEPT !["DECIDE"][curView[p]][qc.node] = QCsMsgsCount["DECIDE"][curView[p]][qc.node] + 1]
   /\ UNCHANGED <<curView, lockedQC, QCsFormed,
          prepareQC, msgsNewViewJustify, msgsPrepareJustify>>

\* line 35 - 36
NextViewInterrupt(p) ==
   /\ curView[p] <= MaxView
   /\ msgsNewViewJustify' = [msgsNewViewJustify EXCEPT ![p][curView[p]] = 
                                      msgsNewViewJustify[p][curView[p]] \union {prepareQC[p]}]
   /\ IF curView[p] = MaxView
      THEN /\ phase' = [phase EXCEPT ![p] = "STOP"]
           /\ curView' = curView
      ELSE /\ phase' = [phase EXCEPT ![p] = "PREPARE"]
           /\ curView' = [curView EXCEPT ![p] = curView[p] + 1]
   /\ UNCHANGED <<decision, lockedQC, QCsFormed, lastDecision,
          prepareQC, msgsPrepareJustify, QCsMsgsCount>>

EnableOnByzantine(p, s1, s2) ==
   IF p \in Byzantine
   THEN s1
   ELSE s2
   
\* here we don't change QCsMsgsCount - is this a problem?
AddQCAndFakeMsgs == 
   /\ \E t \in Phases : \E v \in ViewsOrNil : \E n \in NodesOrNil :
      /\ QCsMsgsCount[t][v][n] >= STRONG_THRESHOLD
      /\ QCsFormed[v][n] = FALSE
      /\ LET newQC == [viewNumber |-> v, node |-> n] IN
         /\ msgsNewViewJustify' = [p \in AllProcs |-> 
                                                     EnableOnByzantine(p,
                                                        [byzView \in Views |-> msgsNewViewJustify[p][byzView] \union SetOfQCs({newQC})],
                                                        msgsNewViewJustify[p])]
         /\ msgsPrepareJustify' = [p \in AllProcs |-> 
                                                     EnableOnByzantine(p,
                                                        [byzView \in Views |-> [byzNode \in NodesOrNil |-> msgsPrepareJustify[p][byzView][byzNode] \union SetOfQCs({newQC})]],
                                                        msgsPrepareJustify[p])]
      /\ QCsFormed' = [QCsFormed EXCEPT ![v][n] = TRUE]
   /\ UNCHANGED <<curView, phase, decision, lockedQC, prepareQC, QCsMsgsCount, lastDecision>>
   
   
Next ==
   \/ \E p \in Corr :
      \/ PreparePhaseAsLeader(p)
      \/ PreparePhaseAsReplica(p)
      \/ PrecommitPhaseAsReplica(p)
      \/ CommitPhaseAsReplica(p)
      \/ DecidePhaseAsReplica(p)
      \/ NextViewInterrupt(p) 
   \/ AddQCAndFakeMsgs
   \/ UNCHANGED vars

(******************************** PROPERTIES  ***************************************)

\* list structure holds
RECURSIVE DecisionsValidity(_, _, _)
DecisionsValidity(proc, view, node) ==
   IF view = 0
   THEN TRUE
   ELSE /\ (IF node = NilNode
            THEN TRUE
            ELSE ExtendsFrom[node][decision[view][proc]])
        /\ DecisionsValidity(proc, view - 1, decision[view][proc])

Validity ==
   \A p \in Corr : DecisionsValidity(p, MaxView - 1, NilNode)

\* the safety property -- agreement
Agreement == 
   \A p, q \in Corr:
      \/ ExtendsFrom[lastDecision[p]][lastDecision[q]]
      \/ ExtendsFrom[lastDecision[q]][lastDecision[p]]
    
Inv == Agreement /\ TypeOK
                     
(******************************** DEBUG  ***************************************)

NoDecision == \A v \in Views: \A p \in Corr: decision[v][p] = NilNode 

NoMovement == 
   /\ curView = [p \in Corr |-> 1]
   /\ phase = [p \in Corr |-> "PREPARE"]

=============================================================================
