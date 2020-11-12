--------------------------- MODULE HotStuffBeta ---------------------------
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

(*************************** DEFINITIONS ************************************)
AllProcs == Corr \union Byzantine      \* the set of all processes

Views == 0..MaxView                 \* the set of potential rounds
NilView == 0   \* a special value to denote a nil round, outside of Views
ViewsOrNil == Views \union {NilView} \* this is dumb

(* nodes logic *)

MaxNode == 2 ^ (MaxView + 1) - 1
Nodes == 2..MaxNode \* the set of all nodes
NilNode == 1  \* a special value (_|_ in paper)
NodesOrNil == Nodes \union {NilNode}

BranchFrom == [n \in NodesOrNil |-> [pn \in NodesOrNil |-> (n = pn * 2 \/ n = (pn * 2) + 1)]]

\*logic for tree structure

\* childrens in tree structure
NextNodes == [n \in NodesOrNil |-> IF n <= 2 ^ (MaxView - 1)
                                   THEN {2 * n, 2 * n + 1}
                                   ELSE {n}]

\* The validity predicate
ExtendsFrom == [n \in NodesOrNil |-> [pn \in NodesOrNil |-> 
                                          \E k \in 0..MaxView : \E r \in 0..MaxNode : 
                                             r < 2 ^ k /\ n = pn * (2 ^ k) + r]]

(* nodes logic *)

Phases == {"PREPARE", "PRECOMMIT", "COMMIT", "DECIDE", "NEW-VIEW"}
PhasesExtended == Phases \union {"PREPARE'", "STOP"}

QCs == [viewNumber : ViewsOrNil, node : NodesOrNil]
NilQC == [viewNumber |-> NilView, node |-> NilNode] \* _|_
QCsOrNil == QCs \union {NilQC}

\* the two thresholds that are used in the algorithm
WEAK_THRESHOLD == T + 1     \* at least one process is not faulty
STRONG_THRESHOLD == N - T \* a quorum when having N > 3 * T

(********************* PROTOCOL STATE VARIABLES ******************************)
VARIABLES
  curView,    \* a process round number: Corr -> Views
  phase,      \* a process phase: Corr -> { "PREPARE", "PRECOMMIT", "COMMIT", "DECIDE" }
  decision,   \* process decision: Corr -> QCsOrNilQC
  lockedQC,   \* a locked value: Corr -> QCsOrNil
  prepareQC   \* a valid value: Corr -> QCsOrNil

\* book-keeping variables
VARIABLES
  msgsNewViewJustify,      \* msgs : src -> view -> set_of_QCs
  msgsPrepareJustify,      \* msgs : src -> view -> node -> set_of_QCs
  \* because we really need only them as msgs + QCs
  msgsCount,               \* Count : view -> node -> Int how many msgs were sent that can form that QC
  QCsFormed,               \* for byzantine
  lastDecision
 
\* a handy definition used in UNCHANGED
vars == <<curView, phase, decision, lockedQC, QCsFormed, lastDecision,
          prepareQC, msgsNewViewJustify, msgsPrepareJustify, msgsCount>>
          
(********************* HANDY FUNCTIONS **************************************)

BoroadcastMsgWithoutQC(proc, type, node) == 
    msgsCount' = [msgsCount EXCEPT ![type][curView[proc]][node] = msgsCount[type][curView[proc]][node] + 1]
                                      
BroadcastPrepareJustify(proc, newNode, highQC) ==
    msgsPrepareJustify' = [msgsPrepareJustify EXCEPT ![proc][curView[proc]][newNode] = msgsPrepareJustify[proc][curView[proc]][newNode] \union {highQC}] 

BroadcastNewViewJustify(proc) == 
    msgsNewViewJustify' = [msgsNewViewJustify EXCEPT ![proc][curView[proc]] = 
                           msgsNewViewJustify[proc][curView[proc]] \union {prepareQC[proc]}]
                           
\* core protocol function
SafeNode(proc, node, qc) ==
    ExtendsFrom[node][lockedQC[proc].node] \/ (qc.viewNumber > lockedQC[proc].viewNumber)
    \* ExtendsFrom[n][lockedQC[p].node] \/ qc.viewNumber > lockedQC[p].viewNumber
                                        
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
    /\ msgsCount \in [Phases -> [Views -> [NodesOrNil -> Int]]]
    /\ QCsFormed \in [Views -> [NodesOrNil -> BOOLEAN]]
    /\ lastDecision \in [Corr -> NodesOrNil]

(************************ PROTOCOL INITIALIZATION ******************************)

InitNewViewJustify(s, v) ==
   IF s \in Corr
   THEN IF v = 0
        THEN {NilQC}
        ELSE {}
   ELSE {NilQC}

InitPrepareJustify(s, v, n) ==
   IF s \in Byzantine \* /\ ExtendsFrom[n][NilNode]
   THEN {NilQC}
   ELSE {}

Init ==
    /\ curView = [p \in Corr |-> 1]
    /\ phase = [p \in Corr |-> "PREPARE"]
    /\ decision = [v \in Views |-> [p \in Corr |-> NilNode]]
    /\ lockedQC = [p \in Corr |-> NilQC]
    /\ prepareQC = [p \in Corr |-> NilQC]
    /\ msgsNewViewJustify = [s \in AllProcs |-> [v \in Views |-> InitNewViewJustify(s, v)]]
    /\ msgsPrepareJustify = [s \in AllProcs |-> [v \in Views |-> [n \in NodesOrNil |-> InitPrepareJustify(s, v, n)]]]
    /\ msgsCount = [t \in Phases |-> [v \in ViewsOrNil |-> [n \in NodesOrNil |-> F]]]
    /\ QCsFormed = [[v \in Views |-> [n \in NodesOrNil |-> FALSE]] EXCEPT ![NilView][NilNode] = TRUE]
    /\ lastDecision = [p \in Corr |-> NilNode]
        
(************************ PROTOCOL TRANSLATION ******************************)

\* Phases are used to set the order

\* Leader phase reduced after prepare, because leader only

\* PREPARE phase

\* line 2 - 6
PreparePhaseAsLeader(proc) ==
   /\ phase[proc] = "PREPARE"
   /\ proc = Leader[curView[proc]] \* line 2 
   /\ \E Msrc \in SUBSET AllProcs : \* line 3 start
      /\ Cardinality(Msrc) >= STRONG_THRESHOLD \* enough procs sent msgs
      /\ \A src \in Msrc : msgsNewViewJustify[src][curView[proc] - 1] /= {} \* everybody sent something 
      /\ \E src \in Msrc : \E highQC \in msgsNewViewJustify[src][curView[proc] - 1]  : \* choosing highQC
         /\ \A otherSrc \in Msrc : \E qc \in msgsNewViewJustify[otherSrc][curView[proc] - 1] : 
         \* we use EXIST, because we want to take into account every possible combination
            \/ otherSrc = src \* because we picked all QCs of all buckets
            \/ highQC.viewNumber \geq qc.viewNumber \* line 3 end
         \* lines 4, 5 and 6
         /\ \E newNode \in NextNodes[highQC.node] : BroadcastPrepareJustify(proc, newNode, highQC)
         \* here we use only one branch of tree structure
   /\ phase' = [phase EXCEPT ![proc] = "PREPARE'"]
   /\ UNCHANGED <<curView, decision, lockedQC, QCsFormed, lastDecision,
          prepareQC, msgsNewViewJustify, msgsCount>>
          
\* line 7 - 10
PreparePhaseAsReplica(proc) ==
   \* line 7
   /\ (phase[proc] = "PREPARE" /\ proc /= Leader[curView[proc]]) \/ phase[proc] = "PREPARE'" 
   \* line 8
   /\ \E node \in NodesOrNil :  \E qc \in msgsPrepareJustify[Leader[curView[proc]]][curView[proc]][node] :
      \* Here we use branch, because we are checking 
      \* line 9 
      /\ IF BranchFrom[node][qc.node] /\ SafeNode(proc, node, qc)
         \* line 10
         THEN BoroadcastMsgWithoutQC(proc, "PREPARE", node)
         ELSE msgsCount' = msgsCount
      /\ phase' = [phase EXCEPT ![proc] = "PRECOMMIT"]
      /\ UNCHANGED <<curView, decision, lockedQC, QCsFormed, lastDecision,
          prepareQC, msgsNewViewJustify, msgsPrepareJustify>>

\* PRECOMMIT phase

\* line 15 - 18
PrecommitPhaseAsReplica(proc) ==
   /\ phase[proc] = "PRECOMMIT"
   \* line 15
   /\ \E node \in NodesOrNil : LET qc == [viewNumber |-> curView[proc], node |-> node] IN
      /\ msgsCount["PREPARE"][curView[proc]][node] >= STRONG_THRESHOLD \* line 16
      /\ prepareQC' = [prepareQC EXCEPT ![proc] = qc] \* line 17
      /\ BoroadcastMsgWithoutQC(proc, "PRECOMMIT", node) \* line 18
      /\ phase' = [phase EXCEPT ![proc] = "COMMIT"]
      /\ UNCHANGED <<curView, decision, lockedQC, QCsFormed, lastDecision,
          msgsNewViewJustify, msgsPrepareJustify>>


\* COMMIT phase

\* line 23 - 26 
CommitPhaseAsReplica(proc) ==
   /\ phase[proc] = "COMMIT"
   \* line 23
   /\ \E node \in NodesOrNil : LET qc == [viewNumber |-> curView[proc], node |-> node] IN
      /\ msgsCount["PRECOMMIT"][curView[proc]][node] >= STRONG_THRESHOLD \* line 24
      /\ lockedQC' = [lockedQC EXCEPT ![proc] = qc] \* line 25
      /\ BoroadcastMsgWithoutQC(proc, "COMMIT", node) \* line 26
      /\ phase' = [phase EXCEPT ![proc] = "DECIDE"]
      /\ UNCHANGED <<curView, decision, QCsFormed, lastDecision,
          prepareQC, msgsNewViewJustify, msgsPrepareJustify>>

\* DECIDE phase

\* line 31- 34
DecidePhaseAsReplica(proc) ==
   /\ phase[proc] = "DECIDE" \* There is a very strange line here - wait for message m from leader(curView)
   \* line 31
   /\ \E node \in NodesOrNil : LET qc == [viewNumber |-> curView[proc], node |-> node] IN
      /\ msgsCount["COMMIT"][curView[proc]][node] >= STRONG_THRESHOLD \* line 33
      \* line 34
      /\ decision' = [decision EXCEPT ![curView[proc]][proc] = lockedQC[proc].node]
      /\ lastDecision' = [lastDecision EXCEPT ![proc] = lockedQC[proc].node]
      /\ BoroadcastMsgWithoutQC(proc, "DECIDE", node)
      /\ phase' = [phase EXCEPT ![proc] = "NEW-VIEW"]
   /\ UNCHANGED <<curView, lockedQC, QCsFormed,
          prepareQC, msgsNewViewJustify, msgsPrepareJustify>>

\* line 35 - 36
NextViewInterrupt(proc) ==
   /\ curView[proc] <= MaxView
   /\ BroadcastNewViewJustify(proc)
   /\ IF curView[proc] = MaxView
      THEN /\ phase' = [phase EXCEPT ![proc] = "STOP"] \* Phase to stop algorithm
           /\ curView' = curView
      ELSE /\ phase' = [phase EXCEPT ![proc] = "PREPARE"]
           /\ curView' = [curView EXCEPT ![proc] = curView[proc] + 1]
   /\ UNCHANGED <<decision, lockedQC, QCsFormed, lastDecision,
          prepareQC, msgsPrepareJustify, msgsCount>>

EnableOnByzantine(p, s1, s2) ==
   IF p \in Byzantine
   THEN s1
   ELSE s2

AddQCAndFakeMsgs == 
   /\ \E t \in Phases : \E v \in ViewsOrNil : \E n \in NodesOrNil :
      /\ msgsCount[t][v][n] >= STRONG_THRESHOLD
      /\ QCsFormed[v][n] = FALSE
      /\ LET newQC == [viewNumber |-> v, node |-> n] IN
         /\ msgsNewViewJustify' = [p \in AllProcs |-> 
                                                     EnableOnByzantine(p,
                                                        [byzView \in Views |-> msgsNewViewJustify[p][byzView] \union {newQC}],
                                                        msgsNewViewJustify[p])]
         /\ msgsPrepareJustify' = [p \in AllProcs |-> 
                                                     EnableOnByzantine(p,
                                                        [byzView \in Views |-> [byzNode \in NodesOrNil |-> msgsPrepareJustify[p][byzView][byzNode] \union {newQC}]],
                                                        msgsPrepareJustify[p])]
      /\ QCsFormed' = [QCsFormed EXCEPT ![v][n] = TRUE]
   /\ UNCHANGED <<curView, phase, decision, lockedQC, prepareQC, msgsCount, lastDecision>>
   
   
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

DecisionsValidity(p) ==
   \A v1 \in Views : \A v2 \in Views : 
      \/ decision[v2][p] = NilNode
      \/ (v1 <= v2) => ExtendsFrom[decision[v2][p]][decision[v1][p]]

Validity ==
   \*\A p \in Corr : DecisionsValidity(p, MaxView - 1, NilNode)
   \A p \in Corr : DecisionsValidity(p)

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
