--------------------------- MODULE HotStuffSketch ---------------------------
EXTENDS Integers, FiniteSets

(********************* PROTOCOL PARAMETERS **********************************)
Corr == {0, 1}          \* the set of correct processes 
Byzantine == {2}     \* the set of byzantine processes, may be empty
N == 3             \* the total number of processes: correct, defective, and Byzantine
T == 1             \* an upper bound on the number of Byzantine processes
ValidNodes == {"n0", "n1"}    \* the set of valid nodes, proposed both by correct and faulty
InvalidNodes == {"n2"}  \* the set of invalid nodes, never proposed by the correct ones
MaxView == 3       \* the maximal view number

Leader == [ v \in 0..MaxView |-> v % N]        \* the leader function from 0..NViews to 1..N

ASSUME(N = Cardinality(Corr \union Byzantine))

(********************* TYPE ANNOTATIONS FOR APALACHE *************************)
\* the operator for type annotations
a <: b == a

\* the type of quorum sertificate
QCT == [type |-> STRING, viewNumber |-> Int, node |-> STRING] \* qc.sig - ommited

\* the type of message records
MT == [type |-> STRING, src |-> STRING, viewNumber |-> Int,
       node |-> STRING, justify |-> QCT, partialSig |-> BOOLEAN]
       
\* a type annotation for a message
AsMsg(m) == m <: MT
\* a type annotation for a set of messages
SetOfMsgs(S) == S <: {MT}       
\* a type annotation for an empty set of messages
EmptyMsgSet == SetOfMsgs({})

(*************************** DEFINITIONS ************************************)
AllProcs == Corr \union Byzantine      \* the set of all processes

Views == 0..MaxView                 \* the set of potential rounds
NilView == 0   \* a special value to denote a nil round, outside of Views
ViewsOrNil == Views \union {NilView}

Nodes == ValidNodes \union InvalidNodes \* the set of all nodes
NilNode == "None"  \* a special value (_|_ in paper)
NodesOrNil == Nodes \union {NilNode}

Phases == {"PREPARE", "PRECOMMIT", "COMMIT", "DECIDE", "NEW-VIEW"}

QCs == [type : Phases, viewNumber : Views, node : Nodes] <: {QCT}
NilQC == [type |-> "NONE", viewNumber |-> NilView, node |-> NilNode] <: QCT \* _|_
QCsOrNil == QCs \union {NilQC}

Messages == [type : Phases, src : AllProcs, viewNumber : Views, node : NodesOrNil, justify : QCsOrNil, partialSig : BOOLEAN]

AllPrepare == 
  [type: {"PREPARE"},
   src: AllProcs,
   viewNumber: Views,
   node: NodesOrNil,
   justify : QCsOrNil,
   partialSig : BOOLEAN] <: {MT}
  
AllPrecommit == 
  [type: {"PRECOMMIT"},
   src: AllProcs,
   viewNumber: Views,
   node: NodesOrNil,
   justify : QCsOrNil,
   partialSig : BOOLEAN] <: {MT}

AllCommit == 
  [type: {"COMMIT"},
   src: AllProcs,
   viewNumber: Views,
   node: NodesOrNil,
   justify : QCsOrNil,
   partialSig : BOOLEAN] <: {MT}

AllDecide == 
  [type: {"DECIDE"},
   src: AllProcs,
   viewNumber: Views,
   node: NodesOrNil,
   justify : QCsOrNil,
   partialSig : BOOLEAN] <: {MT}
   
AllNewView == 
  [type: {"NEW-VIEW"},
   src: AllProcs,
   viewNumber: Views,
   node: NodesOrNil,
   justify : QCsOrNil,
   partialSig : BOOLEAN] <: {MT}
   
BenignViewsInMessages(msgfun) ==
  \* the message function never contains a message for a wrong view
  \A r \in Views:
    \A m \in msgfun[r]:
      r = m.viewNumber

\* a value hash is modeled as identity
Id(v) == v

\* The validity predicate
ExtendsFrom(v, pv) == v \in ValidNodes \* prpbably we should specialize it by hands?

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
  msgsPrepare,   \* PREPARE messages broadcast in the system, Views -> Messages
  msgsPrecommit, \* PREOMMIT messages broadcast in the system, Views -> Messages
  msgsCommit,    \* COMMIT messages broadcast in the system, Views -> Messages
  msgsDecide,    \* DECIDE messages broadcast in the system, Views -> Messages
  msgsNewView,   \* NEW-VIEW messages broadcast in the system, Views -> Messages
  evidence \* the messages that were used by the process that made a transition
 
\* a handy definition used in UNCHANGED
vars == <<curView, phase, decision, lockedQC,
          prepareQC, evidence, msgsPrepare, msgsPrecommit, msgsCommit, msgsDecide, msgsNewView>>

(************************ MESSAGE PASSING ***********************************)
BroadcastPrepare(pSrc, pView, pNode, pQC, pSigned) ==
  LET newMsg ==
    AsMsg([type |-> "PREPARE", src |-> pSrc, viewNumber |-> pView,
           node |-> pNode, justify |-> pQC, partialSig |-> pSigned])
  IN
  msgsPrepare' = [msgsPrepare EXCEPT ![pView] = msgsPrepare[pView] \cup {newMsg}]

BroadcastPrecommit(pSrc, pView, pNode, pQC, pSigned) ==
  LET newMsg ==
    AsMsg([type |-> "PRECOMMIT", src |-> pSrc, viewNumber |-> pView,
           node |-> pNode, justify |-> pQC, partialSig |-> pSigned])
  IN
  msgsPrecommit' = [msgsPrecommit EXCEPT ![pView] = msgsPrecommit[pView] \cup {newMsg}]

BroadcastCommit(pSrc, pView, pNode, pQC, pSigned) ==
  LET newMsg ==
    AsMsg([type |-> "COMMIT", src |-> pSrc, viewNumber |-> pView,
           node |-> pNode, justify |-> pQC, partialSig |-> pSigned])
  IN
  msgsCommit' = [msgsCommit EXCEPT ![pView] = msgsCommit[pView] \cup {newMsg}]

BroadcastDecide(pSrc, pView, pNode, pQC, pSigned) ==
  LET newMsg ==
    AsMsg([type |-> "DECIDE", src |-> pSrc, viewNumber |-> pView,
           node |-> pNode, justify |-> pQC, partialSig |-> pSigned])
  IN
  msgsDecide' = [msgsDecide EXCEPT ![pView] = msgsDecide[pView] \cup {newMsg}]

BroadcastNewView(pSrc, pView, pNode, pQC, pSigned) ==
  LET newMsg ==
    AsMsg([type |-> "NEW-VIEW", src |-> pSrc, viewNumber |-> pView,
           node |-> pNode, justify |-> pQC, partialSig |-> pSigned])
  IN
  msgsNewView' = [msgsNewView EXCEPT ![pView] = msgsNewView[pView] \cup {newMsg}]


(************************ TYPE INVARIANT ************************************)

(* the standard type invariant *)
TypeOK ==
    /\ curView \in [Corr -> Views]
    /\ phase \in [Corr -> Phases]
    /\ decision \in [Views -> [Corr -> ValidNodes \union {NilNode}]]
    /\ lockedQC \in [Corr -> QCsOrNil]
    /\ prepareQC \in [Corr -> QCsOrNil]
    /\ msgsPrepare \in [Views -> SUBSET AllPrepare]
    /\ BenignViewsInMessages(msgsPrepare)
    /\ msgsPrecommit \in [Views -> SUBSET AllPrecommit]
    /\ BenignViewsInMessages(msgsPrecommit)
    /\ msgsCommit \in [Views -> SUBSET AllCommit]
    /\ BenignViewsInMessages(msgsCommit)
    /\ msgsDecide \in [Views -> SUBSET AllDecide]
    /\ BenignViewsInMessages(msgsDecide)
    /\ msgsNewView \in [Views -> SUBSET AllNewView]
    /\ BenignViewsInMessages(msgsNewView)
    /\ evidence \in SUBSET (Messages)
    
(************************ PROTOCOL UTILITIES ********************************)

SafeNode(node, qc, p) ==
   ExtendsFrom(node, lockedQC[p].node) \/ qc.viewNumber > lockedQC[p].viewNumber
   
MakeQC(V) == 
   LET m == CHOOSE m \in V : TRUE IN [type |-> m.type, viewNumber |-> m.viewNumber, node |-> m.node]
   (*IF \E SubV \in SUBSET V:
      /\ Cardinality(SubV) >= STRONG_THRESHOLD
      /\ \A m1, m2 \in V :
         /\ m1 /= m2 -> m1.src /= m2.src
         /\ m1 /= m2 -> 
         /\ m1.partialSig = TRUE*)
         
CheckQourumForCertificate(V) ==
   /\ Cardinality(V) >= STRONG_THRESHOLD
   /\ \A m1, m2 \in V :
      /\ m1 /= m2 => m1.src /= m2.src
      /\ m1 /= m2 => m1.node = m2.node
      /\ m1 /= m2 => m1.type = m2.type
      /\ m1.partialSig = TRUE

CheckQourumOfMsgs(V) ==
   /\ Cardinality(V) >= STRONG_THRESHOLD
   /\ \A m1, m2 \in V :
      /\ m1 /= m2 => m1.src /= m2.src
      /\ m1 /= m2 => m1.node = m2.node
      /\ m1 /= m2 => m1.type = m2.type
      /\ m1.partialSig = FALSE
         
         
MatchingMsg(m, t, v) == 
   m.type = t /\ m.viewNumber = v
   
MatchingQC(qc, t, v) ==
  qc.type = t /\ qc.viewNumber = v
         

(************************ PROTOCOL INITIALIZATION ******************************)

\*initial NEW-VIEW messages

FaultyNilQCNewViewByView(v) == 
    SetOfMsgs([type: {"NEW-VIEW"}, src: Byzantine, viewNumber: {v}, node: NodesOrNil, justify : {NilQC}, partialSig : BOOLEAN])

FaultyNilQCPrepareByView(v) == 
    SetOfMsgs([type: {"PREPARE"}, src: Byzantine, viewNumber: {v}, node: NodesOrNil, justify : {NilQC}, partialSig : BOOLEAN])
    
FaultyNilQCPrecommitByView(v) == 
    SetOfMsgs([type: {"PRECOMMIT"}, src: Byzantine, viewNumber: {v}, node: NodesOrNil, justify : {NilQC}, partialSig : BOOLEAN])
  
FaultyNilQCCommitByView(v) == 
    SetOfMsgs([type: {"COMMIT"}, src: Byzantine, viewNumber: {v}, node: NodesOrNil, justify : {NilQC}, partialSig : BOOLEAN])
    
FaultyNilQCDecideByView(v) == 
    SetOfMsgs([type: {"DECIDE"}, src: Byzantine, viewNumber: {v}, node: NodesOrNil, justify : {NilQC}, partialSig : BOOLEAN])

AllCorrectInitialNewView == 
    SetOfMsgs([type: {"NEW-VIEW"}, src: Corr, viewNumber: {0}, node: {NilNode}, justify : {NilQC}, partialSig : {FALSE}])

EnableSetOnZero(v, s) == IF v = 0
                         THEN s
                         ELSE EmptyMsgSet

Init ==
    /\ curView = [p \in Corr |-> 1]
    /\ phase = [p \in Corr |-> "PREPARE"]
    /\ decision = [v \in Views |-> [p \in Corr |-> NilNode]]
    /\ lockedQC = [p \in Corr |-> NilQC]
    /\ prepareQC = [p \in Corr |-> NilQC]
    /\ msgsPrepare = [v \in Views |-> FaultyNilQCPrepareByView(v)]
    /\ msgsPrecommit = [v \in Views |-> FaultyNilQCPrecommitByView(v)]
    /\ msgsCommit = [v \in Views |-> FaultyNilQCCommitByView(v)]
    /\ msgsDecide = [v \in Views |-> FaultyNilQCDecideByView(v)]
    /\ msgsNewView = [v \in Views |-> EnableSetOnZero(v, AllCorrectInitialNewView) \union FaultyNilQCNewViewByView(v)]
    /\ BenignViewsInMessages(msgsPrepare)
    /\ BenignViewsInMessages(msgsPrecommit)
    /\ BenignViewsInMessages(msgsCommit)
    /\ BenignViewsInMessages(msgsDecide)
    /\ BenignViewsInMessages(msgsNewView)
    /\ evidence = EmptyMsgSet
    
(************************ PROTOCOL TRANSLATION ******************************)

\* experimental function

AllMsgs(v) == msgsPrepare[v] \union msgsPrecommit[v] \union msgsCommit[v] \union msgsDecide[v] \union msgsNewView[v]

\* experimental function

\* PREPARE phase

\* line 2 - 6
PreparePhaseAsLeader(p) ==
   /\ phase[p] = "PREPARE"
   /\ p = Leader[curView[p]] \* line 2 
   (*/\ ~ \E m \in msgsPrepare[curView[p]] : \* suspicious check
      /\ m.src = p
      /\ m.viewNumber = curView[p] 
      /\ m.justify /= NilQC
      /\ m.partialSig = FALSE \* less suspicious place*)
   /\ \E M \in SUBSET msgsNewView[curView[p] - 1] : \* line 3
      \* /\ Cardinality(M) >= STRONG_THRESHOLD \* line 3 in CheckQourumOfMsgs
      /\ CheckQourumOfMsgs(M) \* implicit checks
      /\ evidence' = M
      /\ LET highQC == (CHOOSE maxJustifyViewNumber \in M : \* line 4
            \A m \in M : maxJustifyViewNumber.justify.viewNumber \geq m.justify.viewNumber).justify IN \* line 4
         \E n \in ValidNodes : BroadcastPrepare(p, curView[p], n, highQC, FALSE) \* line 6
   /\ UNCHANGED <<curView, phase, decision, lockedQC,
      prepareQC, msgsPrecommit, msgsCommit, msgsDecide, msgsNewView>>
          
\* line 7 - 10
PreparePhaseAsReplica(p) ==
   /\ phase[p] = "PREPARE"
   /\ \E m \in msgsPrepare[curView[p]] : \* line 8
      /\ MatchingMsg(m, "PREPARE", curView[p]) \* double check(if we trust in types)!!!
      /\ m.src = Leader[curView[p]]
      /\ IF ExtendsFrom(m.node, m.justify.node) /\ SafeNode(m.node, m.justify, p) \* line 9
         THEN BroadcastPrepare(p, curView[p], m.node, NilQC, TRUE) \* line 10
         ELSE msgsPrepare' = msgsPrepare
      /\ phase' = [phase EXCEPT ![p] = "PRECOMMIT"]
      /\ evidence' = SetOfMsgs({m})
      /\ UNCHANGED <<curView, decision, lockedQC, prepareQC,
         msgsPrecommit, msgsCommit, msgsDecide, msgsNewView>>

\* PRECOMMIT phase

\* line 11 - 14
PrecommitPhaseAsLeader(p) ==
   /\ phase[p] = "PRECOMMIT"
   /\ p = Leader[curView[p]] \* line 11
   (*/\ ~ \E m \in msgsPrecommit[curView[p]] : \* suspicious check
      /\ m.src = p
      /\ m.viewNumber = curView[p] 
      /\ m.node = NilNode
      /\ m.justify /= NilQC
      /\ m.partialSig = FALSE*)
   /\ \E V \in SUBSET { m \in msgsPrepare[curView[p]] : m.partialSig = TRUE /\ MatchingMsg(m, "PREPARE", curView[p])} : \* line 12  
      \* /\ Cardinality(V) >= STRONG_THRESHOLD \* line 12 in CheckQourumOfMsgs
      /\ CheckQourumForCertificate(V) \* implicit checks
      /\ evidence' = V
      /\ prepareQC' = [prepareQC EXCEPT ![p] = MakeQC(V)] \* line 13 
      /\ BroadcastPrecommit(p, curView[p], NilNode, prepareQC'[p], FALSE) \* line 14
   /\ UNCHANGED <<curView, phase, decision, lockedQC,
          msgsPrepare, msgsCommit, msgsDecide, msgsNewView>>
          
\* line 15 - 18
PrecommitPhaseAsReplica(p) ==
   /\ phase[p] = "PRECOMMIT"
   /\ \E m \in AllMsgs(curView[p]) : \* line 16 !!! probably we don't need AllMsgs here !!!
      /\ MatchingQC(m.justify, "PREPARE", curView[p]) \* line 16
      /\ m.src = Leader[curView[p]] \* line 16
      /\ prepareQC' = [prepareQC EXCEPT ![p] = m.justify] \* line 17
      /\ phase' = [phase EXCEPT ![p] = "COMMIT"]
      /\ evidence' = SetOfMsgs({m}) 
      /\ BroadcastPrecommit(p, curView[p], m.justify.node, NilQC, TRUE) \* line 18
   /\ UNCHANGED <<curView, decision, lockedQC,
          msgsPrepare, msgsCommit, msgsDecide, msgsNewView>>

\* COMMIT phase

\* line 19 - 22
CommitPhaseAsLeader(p) ==
   /\ phase[p] = "COMMIT"
   /\ p = Leader[curView[p]] \* line 19
   (*/\ ~ \E m \in msgsCommit[curView[p]] : \* suspicious check
      /\ m.src = p
      /\ m.viewNumber = curView[p] 
      /\ m.node = NilNode
      /\ m.justify /= NilQC
      /\ m.partialSig = FALSE*)
   /\ \E V \in SUBSET { m \in msgsPrecommit[curView[p]] : m.partialSig = TRUE /\ MatchingMsg(m, "PRECOMMIT", curView[p])} : \* line 20  
      \* /\ Cardinality(V) >= STRONG_THRESHOLD \* line 20 in CheckQourumOfMsgs
      /\ CheckQourumForCertificate(V) \* implicit checks
      /\ evidence' = V
      /\ LET precommitQC == MakeQC(V) IN \* line 21
         BroadcastCommit(p, curView[p], NilNode, precommitQC, FALSE) \* line 22
   /\ UNCHANGED <<curView, phase, decision, lockedQC,
          prepareQC, msgsPrepare, msgsPrecommit, msgsDecide, msgsNewView>>

\* line 23 - 26
CommitPhaseAsReplica(p) ==
   /\ phase[p] = "COMMIT"
   /\ \E m \in AllMsgs(curView[p]) : \* line 24
      /\ MatchingQC(m.justify, "PRECOMMIT", curView[p]) \* line 24
      /\ m.src = Leader[curView[p]] \* line 24
      /\ lockedQC' = [lockedQC EXCEPT ![p] = m.justify] \* line 25
      /\ phase' = [phase EXCEPT ![p] = "DECIDE"]
      /\ evidence' = SetOfMsgs({m}) 
      /\ BroadcastCommit(p, curView[p], m.justify.node, NilQC, TRUE) \* line 26
   /\ UNCHANGED <<curView, decision,
          prepareQC, msgsPrepare, msgsPrecommit, msgsDecide, msgsNewView>>
      
\* DECIDE phase

\* line 27 - 30
DecidePhaseAsLeader(p) ==
   /\ phase[p] = "DECIDE"
   /\ p = Leader[curView[p]] \* line 27
   (*/\ ~ \E m \in msgsDecide[curView[p]] : \* suspicious check
      /\ m.src = p
      /\ m.viewNumber = curView[p] 
      /\ m.node = NilNode
      /\ m.justify /= NilQC
      /\ m.partialSig = FALSE*)
   /\ \E V \in SUBSET { m \in msgsCommit[curView[p]] : m.partialSig = TRUE /\ MatchingMsg(m, "COMMIT", curView[p])} : \* line 28
      \* /\ Cardinality(V) >= STRONG_THRESHOLD \* line 28 in CheckQourumOfMsgs
      /\ CheckQourumForCertificate(V) \* implicit checks
      /\ evidence' = V
      /\ LET commitQC == MakeQC(V) IN \* line 29
         BroadcastDecide(p, curView[p], NilNode, commitQC, FALSE) \* line 30
   /\ UNCHANGED <<curView, phase, decision, lockedQC,
          prepareQC, msgsPrepare, msgsPrecommit, msgsCommit, msgsNewView>>

\* NEW_VIEW state is a final state
\* line 31- 34
DecidePhaseAsReplica(p) ==
   /\ phase[p] = "DECIDE" \* There is a very strange line here - wait for message m from leader(curView)
   /\ \E m \in AllMsgs(curView[p]) : \* line 32
      /\ MatchingQC(m.justify, "COMMIT", curView[p]) \* line 32
      /\ m.src = Leader[curView[p]] \* line 32
      /\ phase' = [phase EXCEPT ![p] = "NEW-VIEW"]
      /\ evidence' = SetOfMsgs({m}) 
      /\ decision' = [decision EXCEPT ![curView[p]][p] = lockedQC[p].node]
      /\ BroadcastDecide(p, curView[p], m.justify.node, NilQC, TRUE) \* line 34
   /\ UNCHANGED <<curView, lockedQC,
          prepareQC, msgsPrepare, msgsPrecommit, msgsCommit, msgsNewView>>

\* line 35 - 36
NextViewInterrupt(p) ==
   /\ BroadcastNewView(p, curView[p], NilNode, prepareQC[p], FALSE)
   /\ phase' = [phase EXCEPT ![p] = "PREPARE"]
   /\ curView[p] < MaxView
   /\ curView' = [curView EXCEPT ![p] = curView[p] + 1]
   /\ evidence' = SetOfMsgs({})
   /\ UNCHANGED <<decision, lockedQC,
          prepareQC, msgsPrepare, msgsPrecommit, msgsCommit, msgsDecide>>

\* for byzantine messages
CleverFakingMsgs ==
   /\ \E t \in Phases : \E v \in ViewsOrNil : \E n \in NodesOrNil :
      \E V \in (CASE t = "NEW-VIEW" -> SUBSET {m \in msgsNewView[v] : m.node = n /\ m.partialSig = TRUE}
                [] t = "PREPARE" -> SUBSET {m \in msgsPrepare[v] : m.node = n /\ m.partialSig = TRUE}
                [] t = "PRECOMMIT" -> SUBSET {m \in msgsPrecommit[v] : m.node = n /\ m.partialSig = TRUE}
                [] t = "COMMIT" -> SUBSET {m \in msgsCommit[v] : m.node = n /\ m.partialSig = TRUE}
                [] t = "DECIDE" -> SUBSET {m \in msgsDecide[v] : m.node = n /\ m.partialSig = TRUE}) : 
         /\ CheckQourumForCertificate(V)
         /\ evidence' = V
         /\ LET FakeMsgsSet(pview, ptype) == [type: {ptype},
                                src: Byzantine,
                                viewNumber: {pview},
                                node: NodesOrNil,
                                justify : {MakeQC(V)},
                                partialSig : BOOLEAN] IN
            /\ msgsNewView' = [view \in Views |-> msgsNewView[view] \union FakeMsgsSet(view, "NEW-VIEW")]
            /\ msgsPrepare' = [view \in Views |-> msgsPrepare[view] \union FakeMsgsSet(view, "PREPARE")]
            /\ msgsPrecommit' = [view \in Views |-> msgsPrecommit[view] \union FakeMsgsSet(view, "PRECOMMIT")]
            /\ msgsCommit' = [view \in Views |-> msgsCommit[view] \union FakeMsgsSet(view, "COMMIT")]
            /\ msgsDecide' = [view \in Views |-> msgsDecide[view] \union FakeMsgsSet(view, "DECIDE")]
   /\ UNCHANGED <<curView, phase, decision, lockedQC, prepareQC>>
   
Next ==
   \/ \E p \in Corr :
      \/ PreparePhaseAsLeader(p)
      \/ PreparePhaseAsReplica(p)
      \/ PrecommitPhaseAsLeader(p)
      \/ PrecommitPhaseAsReplica(p)
      \/ CommitPhaseAsLeader(p)
      \/ CommitPhaseAsReplica(p)
      \/ DecidePhaseAsLeader(p)
      \/ DecidePhaseAsReplica(p)
      \/ NextViewInterrupt(p) 
      \/ CleverFakingMsgs

(******************************** PROPERTIES  ***************************************)

\* the safety property -- agreement
Agreement == 
   \A v \in Views:
      \A p, q \in Corr:
         \/ decision[v][p] = NilNode
         \/ decision[v][q] = NilNode
         \/ decision[v][p] = decision[v][q]

\* the protocol validity
Validity ==
   \A v \in Views: \A p \in Corr: decision[v][p] \in ValidNodes \union {NilNode}
    
Inv == Agreement /\ Validity /\ TypeOK
                     
(******************************** DEBUG  ***************************************)

NoDecision == \A v \in Views: \A p \in Corr: decision[v][p] = NilNode 
    
=============================================================================
