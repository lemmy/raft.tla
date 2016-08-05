--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, Bags, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitHistoryVars == /\ elections = {}
                   /\ allLogs   = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
Init == /\ messages = EmptyBag
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections>>

\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars>>

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           \* The following upper bound on prevLogIndex is unnecessary
           \* but makes verification substantially simpler.
           prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i]) THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ elections'  = elections \cup
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>

RejectAppendEntriesRequest(i, j, m, logOk) ==
    /\ \/ m.mterm < currentTerm[i]
       \/ /\ m.mterm = currentTerm[i]
          /\ state[i] = Follower
          /\ \lnot logOk
    /\ Reply([mtype           |-> AppendEntriesResponse,
              mterm           |-> currentTerm[i],
              msuccess        |-> FALSE,
              mmatchIndex     |-> 0,
              msource         |-> i,
              mdest           |-> j],
              m)
    /\ UNCHANGED <<serverVars, logVars>>

ReturnToFollowerState(i, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Candidate
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>

AppendEntriesAlreadyDone(i, j, index, m) ==
    /\ \/ m.mentries = << >>
       \/ /\ Len(log[i]) >= index
          /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
    /\ Reply([mtype           |-> AppendEntriesResponse,
              mterm           |-> currentTerm[i],
              msuccess        |-> TRUE,
              mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
              msource         |-> i,
              mdest           |-> j],
              m)
    /\ UNCHANGED <<serverVars, logVars>>

ConflictAppendEntriesRequest(i, index, m) ==
    /\ Len(log[i]) >= index
    /\ log[i][index].term /= m.mentries[1].term
    /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |-> log[i][index2]]
       IN log' = [log EXCEPT ![i] = new]
    /\ UNCHANGED <<serverVars, commitIndex, messages>>

NoConflictAppendEntriesRequest(i, m) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) = m.mprevLogIndex
    /\ log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
    /\ UNCHANGED <<serverVars, commitIndex, messages>>

AcceptAppendEntriesRequest(i, j, logOk, m) ==
    \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ AppendEntriesAlreadyDone(i, j, index, m)
                   \/ ConflictAppendEntriesRequest(i, index, m)
                   \/ NoConflictAppendEntriesRequest(i, m)

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ RejectAppendEntriesRequest(i, j, m, logOk)
          \/ ReturnToFollowerState(i, m)
          \/ AcceptAppendEntriesRequest(i, j, logOk, m)
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
Next == /\ \/ \E i \in Server : Restart(i)
           \/ \E i \in Server : Timeout(i)
           \/ \E i,j \in Server : RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server, v \in Value : ClientRequest(i, v)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : AppendEntries(i, j)
           \/ \E m \in DOMAIN messages : Receive(m)
           \/ \E m \in DOMAIN messages : DuplicateMessage(m)
           \/ \E m \in DOMAIN messages : DropMessage(m)
           \* History variable that tracks every log ever:
        /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* The main safety proofs are below
\* We start with type invariants

\* The next four definitions give the types of each type of message
RequestVoteRequestType ==
    [mtype : {RequestVoteRequest},
     mterm : Nat,
     mlastLogTerm : Nat,
     mlastLogIndex : Nat,
     msource : Server,
     mdest : Server]

AppendEntriesRequestType ==
    [mtype : {AppendEntriesRequest},
       mterm : Nat,
       mprevLogIndex : Int,
       mprevLogTerm : Nat,
       mentries : Seq([term : Nat, value : Value]),
       mlog : Seq([term : Nat, value : Value]),
       mcommitIndex : Nat,
       msource : Server,
       mdest : Server]

RequestVoteResponseType ==
    [mtype : {RequestVoteResponse},
     mterm : Nat,
     mvoteGranted : BOOLEAN,
     mlog : Seq([term : Nat, value : Value]),
     msource : Server,
     mdest : Server]

AppendEntriesResponseType ==
    [mtype : {AppendEntriesResponse},
     mterm : Nat,
     msuccess : BOOLEAN,
     mmatchIndex : Nat,
     msource : Server,
     mdest : Server]

MessageType ==
    RequestVoteRequestType \cup AppendEntriesRequestType \cup
    RequestVoteResponseType \cup AppendEntriesResponseType

\* The full type invariant for the system
TypeOK ==
    /\ IsABag(messages) /\ BagToSet(messages) \subseteq MessageType
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Follower, Candidate, Leader}]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ log \in [Server -> Seq([term : Nat, value : Value])]
    /\ commitIndex \in [Server -> Nat]
    /\ votesResponded \in [Server -> SUBSET Server]
    /\ votesGranted \in [Server -> SUBSET Server]
    /\ nextIndex \in [Server -> [Server -> { n \in Nat : 1 <= n } ]]
    /\ matchIndex \in [Server -> [Server -> Nat]]

\* The prefix of the log of server i that has been committed
Committed(i) == SubSeq(log[i],1,commitIndex[i])

\* Every (index, term) pair determines a log prefix
LogMatching ==
    \A i, j \in Server :
        \A n \in 1..Len(log[i]) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* Every log entry that is committed in at least one server
\* is present in the log of at least one server in every quorum.
QuorumCommitted ==
    \A i \in Nat, e \in [term : Nat, value : Value] :
        (\E s \in Server : i <= commitIndex[s] /\ log[s][i] = e) =>
        \A q \in Quorum : \E s \in q : log[s][i] = e

\* The committed entries in every log are a prefix of the
\* leader's committed
LeaderCompleteness ==
    \A i \in Server : state[i] = Leader =>
                      \A j \in Server : IsPrefix(Committed(j),Committed(i))

IndInv == TypeOK /\ LeaderCompleteness

ASSUME DistinctRoles == /\ Leader /= Candidate
                        /\ Candidate /= Follower
                        /\ Follower /= Leader

ASSUME DistinctMessageTypes == /\ RequestVoteRequest /= AppendEntriesRequest
                               /\ RequestVoteRequest /= RequestVoteResponse
                               /\ RequestVoteRequest /= AppendEntriesResponse
                               /\ AppendEntriesRequest /= RequestVoteResponse
                               /\ AppendEntriesRequest /= AppendEntriesResponse
                               /\ RequestVoteResponse /= AppendEntriesResponse

LEMMA WithMessage_IsABag ==
    \A B, m : IsABag(B) => IsABag(WithMessage(m,B))
  BY Bags_SetToBagIsABag, Bags_Union DEF WithMessage

LEMMA WithMessage_MessageType ==
    \A B : IsABag(B) /\ BagToSet(B) \subseteq MessageType =>
           \A m \in MessageType :
                BagToSet(WithMessage(m,B)) \subseteq MessageType
  <1> SUFFICES ASSUME NEW B,
                      IsABag(B) /\ BagToSet(B) \subseteq MessageType,
                      NEW m \in MessageType
               PROVE  BagToSet(WithMessage(m,B)) \subseteq MessageType
    OBVIOUS
  <1>1. DOMAIN (B (+) SetToBag({m})) = DOMAIN B \cup DOMAIN SetToBag({m})
    BY Bags_SetToBagIsABag, Bags_Union
  <1> QED
    BY <1>1 DEF WithMessage, BagToSet, SetToBag

LEMMA WithoutMessage_IsABag ==
    \A B, m : IsABag(B) => IsABag(WithoutMessage(m,B))
  BY Bags_SetToBagIsABag, Bags_Difference DEF WithoutMessage

LEMMA WithoutMessage_MessageType ==
    \A B : IsABag(B) /\ BagToSet(B) \subseteq MessageType =>
           \A m : BagToSet(WithoutMessage(m,B)) \subseteq MessageType
  BY Bags_SetToBagIsABag, Bags_Difference DEF WithoutMessage, BagToSet, SetToBag

LEMMA Reply_messagesType ==
    ASSUME NEW m1 \in MessageType,
           NEW m2 \in MessageType,
           IsABag(messages),
           BagToSet(messages) \subseteq MessageType,
           Reply(m1, m2)
    PROVE  /\ IsABag(messages')
           /\ BagToSet(messages') \subseteq MessageType
<1>1. /\ IsABag(WithMessage(m1, messages))
      /\ BagToSet(WithMessage(m1, messages)) \subseteq MessageType
   BY WithMessage_IsABag, WithMessage_MessageType
<1>2. /\ IsABag(WithoutMessage(m2,WithMessage(m1, messages)))
      /\ BagToSet(WithoutMessage(m2,WithMessage(m1, messages))) \subseteq MessageType
   BY <1>1, WithoutMessage_IsABag, WithoutMessage_MessageType
<1>3. QED
   BY <1>1, <1>2 DEF Reply

LEMMA MaxProperties ==
    ASSUME NEW S \in SUBSET Nat,
           S /= {}
    PROVE /\ Max(S) \in Nat
          /\ \A s \in S : s <= Max(S)
  <1>1. \E x \in S : \A y \in S : ~ <<y, x>> \in OpToRel(<,Nat)
    BY WFMin, NatLessThanWellFounded, IsWellFoundedOnSubset
  <1> QED

LEMMA MinProperties ==
    ASSUME NEW S \in SUBSET Nat,
           S /= {}
    PROVE /\ Min(S) \in Nat
          /\ \A s \in S : Min(S) <= s

LEMMA TypeInvariance == Spec => []TypeOK
<1>1. Init => TypeOK
   <2> SUFFICES ASSUME Init
                PROVE  TypeOK
      OBVIOUS
   <2> USE DEF Init
   <2>1. IsABag(messages) /\ BagToSet(messages) \subseteq MessageType
       BY DEF IsABag, EmptyBag, BagToSet, SetToBag
   <2>2. currentTerm \in [Server -> Nat]
       BY DEF InitServerVars
   <2>3. state \in [Server -> {Follower, Candidate, Leader}]
       BY DEF InitServerVars
   <2>4. votedFor \in [Server -> Server \cup {Nil}]
       BY DEF InitServerVars
   <2>5. log \in [Server -> Seq([term : Nat, value : Value])]
       BY DEF InitLogVars
   <2>6. commitIndex \in [Server -> Nat]
       BY DEF InitLogVars
   <2>7. votesResponded \in [Server -> SUBSET Server]
       BY DEF InitCandidateVars
   <2>8. votesGranted \in [Server -> SUBSET Server]
       BY DEF InitCandidateVars
   <2>9. nextIndex \in [Server -> [Server -> { n \in Nat : 1 <= n } ]]
       BY DEF InitLeaderVars
   <2>10. matchIndex \in [Server -> [Server -> Nat]]
       BY DEF InitLeaderVars
   <2>11. QED
      BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
   <3> USE DEF TypeOK
   <3> SUFFICES ASSUME TypeOK /\ [Next]_vars
                PROVE  TypeOK'
     OBVIOUS
   <3>1. CASE Next
      <4>1. CASE \E i \in Server : Restart(i)
        BY <4>1 DEF Restart
      <4>2. CASE \E i \in Server : Timeout(i)
        <5> SUFFICES ASSUME NEW i \in Server,
                            Timeout(i)
                     PROVE  TypeOK'
          BY <4>2
        <5> QED
           BY <4>2 DEF Timeout, leaderVars, logVars
      <4>3. CASE \E i,j \in Server : RequestVote(i, j)
        <5> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                            RequestVote(i, j)
                     PROVE  TypeOK'
          BY <4>3
        <5>1. [mtype         |-> RequestVoteRequest,
               mterm         |-> currentTerm[i],
               mlastLogTerm  |-> LastTerm(log[i]),
               mlastLogIndex |-> Len(log[i]),
               msource       |-> i,
               mdest         |-> j] \in MessageType
          BY LenProperties DEF MessageType, LastTerm, RequestVoteRequestType
        <5> QED
          BY <5>1, <4>3, WithMessage_MessageType, WithMessage_IsABag
          DEF RequestVote, serverVars, candidateVars, leaderVars, logVars,
              Send
      <4>4. CASE \E i \in Server : BecomeLeader(i)
        BY <4>4 DEF BecomeLeader, candidateVars, logVars
      <4>5. CASE \E i \in Server, v \in Value : ClientRequest(i, v)
         BY <4>5, AppendProperties
         DEF ClientRequest, candidateVars, leaderVars, serverVars
      <4>6. CASE \E i \in Server : AdvanceCommitIndex(i)
        <5> USE DEF AdvanceCommitIndex  
        <5> SUFFICES ASSUME NEW i \in Server,
                            AdvanceCommitIndex(i)
                     PROVE  TypeOK'
          BY <4>6 
        <5>1. (commitIndex \in [Server -> Nat])'
            <6>1. {index \in 1..Len(log[i]) :
                              {i}
                              \cup {k \in Server : matchIndex[i][k] >= index}
                              \in Quorum} \in SUBSET Nat
                BY LenProperties
            <6>2. ASSUME {index \in 1..Len(log[i]) :
                              {i}
                              \cup {k \in Server : matchIndex[i][k] >= index}
                              \in Quorum}
                           # {}
                  PROVE   Max({index \in 1..Len(log[i]) :
                                    {i}
                                    \cup {k \in Server :
                                            matchIndex[i][k] >= index}
                                    \in Quorum}) \in Nat
                BY <6>1, <6>2, MaxProperties
            <6>3. QED
                BY <6>2
        <5>2. QED
          BY <5>1 DEF serverVars, logVars, candidateVars, leaderVars
      <4>7. CASE \E i,j \in Server : AppendEntries(i, j)
        <5> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                            AppendEntries(i, j)
                     PROVE  TypeOK'
          BY <4>7
        <5> state[i] = Leader
           BY DEF AppendEntries 
        <5> DEFINE m ==
               [mtype |-> AppendEntriesRequest,
                mterm |-> currentTerm[i],
                mprevLogIndex |-> nextIndex[i][j] - 1,
                mprevLogTerm |-> IF nextIndex[i][j] - 1 > 0 /\ nextIndex[i][j] - 1 <= Len(log[i])
                                 THEN log[i][nextIndex[i][j] - 1].term
                                 ELSE 0,
                mentries |-> SubSeq(log[i], nextIndex[i][j],
                                    Min({Len(log[i]), nextIndex[i][j]})),
                mlog |-> log[i],
                mcommitIndex |-> Min({commitIndex[i],
                                      Min({Len(log[i]), nextIndex[i][j]})}),
                msource |-> i, mdest |-> j]
        <5>1. Min({Len(log[i]), nextIndex[i][j]}) \in Nat
            BY MinProperties, LenProperties
        <5>2. Min({commitIndex[i], Min({Len(log[i]), nextIndex[i][j]})}) \in Nat
            <6>1. {commitIndex[i], Min({Len(log[i]), nextIndex[i][j]})} /= {}
                OBVIOUS
            <6>2. commitIndex[i] \in Nat
                OBVIOUS
            <6> QED
                BY MinProperties, <5>1, <6>1, <6>2
        <5>3. m.mentries \in Seq([term : Nat, value : Value])
            BY SubSeqProperties, MinProperties
        <5>4. m.mprevLogTerm \in Nat
            OBVIOUS
        <5>5. m.mprevLogIndex \in Int
            OBVIOUS
        <5>6. m \in MessageType
            BY <5>2, <5>3, <5>4, <5>5
            DEF MessageType, AppendEntriesRequestType
        <5> QED
          BY <4>7, <5>6, WithMessage_MessageType, WithMessage_IsABag
          DEF AppendEntries, serverVars, candidateVars, leaderVars, logVars, Send
      <4>8. CASE \E m \in DOMAIN messages : Receive(m)
        <5> USE DEF Receive
        <5> SUFFICES ASSUME NEW m \in DOMAIN messages,
                            Receive(m)
                     PROVE  TypeOK'
          BY <4>8
        <5> DEFINE i == m.mdest
        <5> DEFINE j == m.msource
        <5>0. i \in Server /\ j \in Server
           BY DEF BagToSet, MessageType, RequestVoteRequestType,
                  AppendEntriesRequestType, RequestVoteResponseType,
                  AppendEntriesResponseType
        <5>1. CASE UpdateTerm(i, j, m)
           <6>1. m \in MessageType
              BY DEF BagToSet
           <6>2. m.mterm \in Nat
              BY <6>1
              DEF MessageType, RequestVoteRequestType,
                  AppendEntriesRequestType, RequestVoteResponseType,
                  AppendEntriesResponseType
           <6> QED
              BY <5>1, <6>2, DistinctRoles
              DEF UpdateTerm, candidateVars, leaderVars, logVars
        <5>2. CASE /\ m.mtype = RequestVoteRequest
                   /\ HandleRequestVoteRequest(i, j, m)
           <6> DEFINE logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                               \/ /\ m.mlastLogTerm = LastTerm(log[i])
                                  /\ m.mlastLogIndex >= Len(log[i])
           <6> DEFINE grant == /\ m.mterm = currentTerm[i]
                               /\ logOk
                               /\ votedFor[i] \in {Nil, j}
           <6> DEFINE m_1 == [mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm[i],
                            mvoteGranted |-> grant,
                            mlog         |-> log[i],
                            msource      |-> i,
                            mdest        |-> j]
                     
           <6>2. m_1 \in MessageType
              BY <5>0 DEF MessageType, RequestVoteResponseType
           <6>3. m \in MessageType
              BY DEF BagToSet
           <6>4. /\ IsABag(WithMessage(m_1, messages))
                 /\ BagToSet(WithMessage(m_1, messages)) \subseteq MessageType
              BY <6>2, WithMessage_IsABag, WithMessage_MessageType
           <6>5. /\ IsABag(WithoutMessage(m,WithMessage(m_1, messages)))
                 /\ BagToSet(WithoutMessage(m,WithMessage(m_1, messages))) \subseteq MessageType
              BY <6>3, <6>4, WithoutMessage_IsABag, WithoutMessage_MessageType
           <6>6. IsABag(messages') /\ BagToSet(messages') \subseteq MessageType
              BY <5>2, <6>5 DEF HandleRequestVoteRequest, Reply
           <6> QED
              BY <5>2, <5>0, <6>2, <6>6
              DEF HandleRequestVoteRequest, leaderVars, candidateVars, logVars
        <5>3. CASE /\ m.mtype = RequestVoteResponse
                   /\ \/ DropStaleResponse(m.mdest, m.msource, m)
                      \/ HandleRequestVoteResponse(m.mdest, m.msource, m)
           <6>1. m \in MessageType
              BY DEF BagToSet
           <6>2. CASE DropStaleResponse(i, j, m)
              BY <5>3, <6>1, <6>2, WithoutMessage_IsABag,
                  WithoutMessage_MessageType
              DEF DropStaleResponse, Discard, serverVars,
                  candidateVars, leaderVars, logVars
           <6>3. CASE HandleRequestVoteResponse(i, j, m)
                BY <5>0, <5>3, <6>1, <6>3, WithoutMessage_IsABag,
                   WithoutMessage_MessageType
                DEF HandleRequestVoteResponse, Discard,
                    serverVars, leaderVars, logVars
           <6> QED
              BY <5>3, <6>2, <6>3
        <5>4. CASE /\ m.mtype = AppendEntriesRequest
                   /\ HandleAppendEntriesRequest(i, j, m)
           <6> m \in MessageType
              BY DEF MessageType, AppendEntriesRequestType, BagToSet
           <6>0. m \in AppendEntriesRequestType
                 BY <5>4, DistinctMessageTypes
                 DEF MessageType, RequestVoteRequestType, AppendEntriesRequestType,
                     RequestVoteResponseType, AppendEntriesResponseType
           <6> DEFINE logOk == \/ m.mprevLogIndex = 0
                               \/ /\ m.mprevLogIndex > 0
                                  /\ m.mprevLogIndex <= Len(log[i])
                                  /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
           <6>1. CASE RejectAppendEntriesRequest(i, j, m, logOk)
              <7> DEFINE m_1 ==
                     [mtype |-> AppendEntriesResponse,
                      mterm |-> currentTerm[m.mdest], msuccess |-> FALSE,
                      mmatchIndex |-> 0, msource |-> m.mdest,
                      mdest |-> m.msource]
              <7>1. m_1 \in MessageType
                BY <5>0 DEF MessageType, AppendEntriesResponseType
              <7> QED
                 BY <5>4, <6>1, <7>1, Reply_messagesType
                 DEF HandleAppendEntriesRequest, RejectAppendEntriesRequest,
                     serverVars, logVars, candidateVars, leaderVars
           <6>2. CASE ReturnToFollowerState(i, m)
              BY <5>4, <6>2, DistinctRoles
              DEF HandleAppendEntriesRequest, ReturnToFollowerState, logVars,
                  candidateVars, leaderVars
           <6>3. CASE AcceptAppendEntriesRequest(i, j, logOk, m)
              <7> DEFINE index == m.mprevLogIndex + 1
              <7>0. state[i] = Follower
                BY <6>3 DEF AcceptAppendEntriesRequest
              <7>2. m.mprevLogIndex \in Nat
                BY <6>3, <6>0
                DEF AcceptAppendEntriesRequest, AppendEntriesRequestType
              <7>3. CASE AppendEntriesAlreadyDone(i, j, index, m)
                 <8>1. [mtype |-> AppendEntriesResponse,
                        mterm |-> currentTerm[m.mdest], msuccess |-> TRUE,
                        mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                        msource |-> m.mdest, mdest |-> m.msource] \in MessageType
                    BY <5>0, <6>0, <7>2, LenProperties
                    DEF MessageType, AppendEntriesRequestType, AppendEntriesResponseType
                 <8> QED
                    BY <5>4, <7>2, <8>1, <7>3, Reply_messagesType
                    DEF AppendEntriesAlreadyDone, HandleAppendEntriesRequest,
                        AppendEntriesRequestType, candidateVars, leaderVars,
                        serverVars, logVars
              <7>4. CASE ConflictAppendEntriesRequest(i, index, m)
                <8>1. [index2 \in 1..Len(log[m.mdest]) - 1 |->
                               log[m.mdest][index2]]
                      \in Seq([term : Nat, value : Value])
                   BY <5>0
                <8>2. [log EXCEPT
                           ![m.mdest] = [index2 \in 1..Len(log[m.mdest]) - 1 |->
                                        log[m.mdest][index2]]]
                      \in [Server -> Seq([term : Nat, value : Value])]
                   BY <8>1
                <8>3. log' \in [Server -> Seq([term : Nat, value : Value])]
                   BY <8>2, <7>4 DEF ConflictAppendEntriesRequest
                <8>4. UNCHANGED <<messages, currentTerm, state, votedFor, commitIndex,
                                  votesResponded, votesGranted, nextIndex, matchIndex>>
                   BY <5>4, <7>4
                   DEF HandleAppendEntriesRequest, ConflictAppendEntriesRequest,
                       serverVars, candidateVars, leaderVars
                <8> QED
                    BY <8>3, <8>4, <7>0, <7>4, DistinctRoles
                    DEF ConflictAppendEntriesRequest
              <7>5. CASE NoConflictAppendEntriesRequest(i, m)
                <8>1. UNCHANGED <<messages, currentTerm, state, votedFor, commitIndex,
                                  votesResponded, votesGranted, nextIndex, matchIndex>>
                   BY <5>4, <7>5
                   DEF HandleAppendEntriesRequest, NoConflictAppendEntriesRequest,
                       serverVars, candidateVars, leaderVars
                <8>2. Append(log[m.mdest], (m.mentries)[1])
                      \in Seq([term : Nat, value : Value])
                   BY <7>5, <5>0, <6>0, AppendProperties
                   DEF AppendEntriesRequestType, NoConflictAppendEntriesRequest
                <8> QED
                   BY <7>0, <7>5, <8>1, <8>2, DistinctRoles
                   DEF NoConflictAppendEntriesRequest
              <7> QED
                BY <5>4, <6>3, <7>3, <7>4, <7>5
                DEF AcceptAppendEntriesRequest, candidateVars, leaderVars
           <6> QED
              BY <5>4, <6>1, <6>2, <6>3 DEF HandleAppendEntriesRequest
        <5>5. CASE /\ m.mtype = AppendEntriesResponse
                   /\ \/ DropStaleResponse(i, j, m)
                      \/ HandleAppendEntriesResponse(i, j, m)
           <6>1. CASE DropStaleResponse(i, j, m)
              BY <6>1, WithoutMessage_IsABag, WithoutMessage_MessageType
              DEF DropStaleResponse, Discard,
                  serverVars, candidateVars, leaderVars, logVars
           <6>2. CASE HandleAppendEntriesResponse(i, j, m)
              <7>1. m \in AppendEntriesResponseType
                 BY <5>5, DistinctMessageTypes
                 DEF BagToSet, MessageType, AppendEntriesResponseType,
                     RequestVoteRequestType, AppendEntriesRequestType,
                     RequestVoteResponseType
              <7> QED
                 BY <6>2, <7>1, WithoutMessage_IsABag, WithoutMessage_MessageType,
                    MaxProperties
                 DEF HandleAppendEntriesResponse, Discard, AppendEntriesResponseType,
                     serverVars, candidateVars, logVars 
           <6> QED
              BY <5>5, <6>1, <6>2
        <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
      <4>9. CASE \E m \in DOMAIN messages : DuplicateMessage(m)
        BY <4>9, WithMessage_IsABag, WithMessage_MessageType
        DEF DuplicateMessage, Send, leaderVars, serverVars, candidateVars,
            logVars, BagToSet
      <4>10. CASE \E m \in DOMAIN messages : DropMessage(m)
        BY <4>10, WithoutMessage_IsABag, WithoutMessage_MessageType
        DEF DropMessage, Discard, leaderVars, serverVars, candidateVars,
            logVars, BagToSet
      <4>11. QED
        BY <3>1, <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9
        DEF Next
    <3>2. CASE UNCHANGED vars
        BY <3>2 DEF vars, serverVars, candidateVars, leaderVars, logVars
    <3>3. QED
      BY <3>1, <3>2
<1>3. QED
   BY <1>1, <1>2, PTL DEF Spec

LEMMA Invariance == Spec => []IndInv
<1>1. Init => IndInv
  <2> SUFFICES ASSUME Init
               PROVE  IndInv
    OBVIOUS
  <2>1. TypeOK
    <3> USE DEF Init
    <3>1. IsABag(messages) /\ BagToSet(messages) \subseteq MessageType
        BY DEF IsABag, EmptyBag, BagToSet, SetToBag
    <3>2. currentTerm \in [Server -> Nat]
        BY DEF InitServerVars
    <3>3. state \in [Server -> {Follower, Candidate, Leader}]
        BY DEF InitServerVars
    <3>4. votedFor \in [Server -> Server \cup {Nil}]
        BY DEF InitServerVars
    <3>5. log \in [Server -> Seq([term : Nat, value : Value])]
        BY DEF InitLogVars
    <3>6. commitIndex \in [Server -> Nat]
        BY DEF InitLogVars
    <3>7. votesResponded \in [Server -> SUBSET Server]
        BY DEF InitCandidateVars
    <3>8. votesGranted \in [Server -> SUBSET Server]
        BY DEF InitCandidateVars
    <3>9. nextIndex \in [Server -> [Server -> { n \in Nat : 1 <= n } ]]
        BY DEF InitLeaderVars
    <3>10. matchIndex \in [Server -> [Server -> Nat]]
        BY DEF InitLeaderVars
    <3>11. QED
      BY <3>1, <3>10, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF TypeOK
  <2>2. LeaderCompleteness
    BY DistinctRoles DEF Init, InitServerVars, LeaderCompleteness
  <2>3. QED
    BY <2>1, <2>2 DEF IndInv
<1>2. IndInv /\ [Next]_vars => IndInv'
  <2> USE DEF IndInv
  <2> SUFFICES ASSUME IndInv /\ [Next]_vars
               PROVE  IndInv'
    OBVIOUS
  <2>1. TypeOK'
    <3> USE DEF TypeOK
    <3>1. CASE Next
      <4>1. CASE \E i \in Server : Restart(i)
        BY <4>1 DEF Restart
      <4>2. CASE \E i \in Server : Timeout(i)
        <5> SUFFICES ASSUME NEW i \in Server,
                            Timeout(i)
                     PROVE  TypeOK'
          BY <4>2
        <5> QED
           BY <4>2 DEF Timeout, leaderVars, logVars
      <4>3. CASE \E i,j \in Server : RequestVote(i, j)
        <5> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                            RequestVote(i, j)
                     PROVE  TypeOK'
          BY <4>3
        <5>1. [mtype         |-> RequestVoteRequest,
               mterm         |-> currentTerm[i],
               mlastLogTerm  |-> LastTerm(log[i]),
               mlastLogIndex |-> Len(log[i]),
               msource       |-> i,
               mdest         |-> j] \in MessageType
          BY LenProperties DEF MessageType, LastTerm, RequestVoteRequestType
        <5> QED
          BY <5>1, <4>3, WithMessage_MessageType, WithMessage_IsABag
          DEF RequestVote, serverVars, candidateVars, leaderVars, logVars,
              Send
      <4>4. CASE \E i \in Server : BecomeLeader(i)
        BY <4>4 DEF BecomeLeader, candidateVars, logVars
      <4>5. CASE \E i \in Server, v \in Value : ClientRequest(i, v)
         BY <4>5, AppendProperties
         DEF ClientRequest, candidateVars, leaderVars, serverVars
      <4>6. CASE \E i \in Server : AdvanceCommitIndex(i)
        <5> USE DEF AdvanceCommitIndex  
        <5> SUFFICES ASSUME NEW i \in Server,
                            AdvanceCommitIndex(i)
                     PROVE  TypeOK'
          BY <4>6 
        <5>1. (commitIndex \in [Server -> Nat])'
            <6>1. {index \in 1..Len(log[i]) :
                              {i}
                              \cup {k \in Server : matchIndex[i][k] >= index}
                              \in Quorum} \in SUBSET Nat
                BY LenProperties
            <6>2. ASSUME {index \in 1..Len(log[i]) :
                              {i}
                              \cup {k \in Server : matchIndex[i][k] >= index}
                              \in Quorum}
                           # {}
                  PROVE   Max({index \in 1..Len(log[i]) :
                                    {i}
                                    \cup {k \in Server :
                                            matchIndex[i][k] >= index}
                                    \in Quorum}) \in Nat
                BY <6>1, <6>2, MaxProperties
            <6>3. QED
                BY <6>2
        <5>2. QED
          BY <5>1 DEF serverVars, logVars, candidateVars, leaderVars
      <4>7. CASE \E i,j \in Server : AppendEntries(i, j)
        <5> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                            AppendEntries(i, j)
                     PROVE  TypeOK'
          BY <4>7
        <5> state[i] = Leader
           BY DEF AppendEntries 
        <5> DEFINE m ==
               [mtype |-> AppendEntriesRequest,
                mterm |-> currentTerm[i],
                mprevLogIndex |-> nextIndex[i][j] - 1,
                mprevLogTerm |-> IF nextIndex[i][j] - 1 > 0 /\ nextIndex[i][j] - 1 <= Len(log[i])
                                 THEN log[i][nextIndex[i][j] - 1].term
                                 ELSE 0,
                mentries |-> SubSeq(log[i], nextIndex[i][j],
                                    Min({Len(log[i]), nextIndex[i][j]})),
                mlog |-> log[i],
                mcommitIndex |-> Min({commitIndex[i],
                                      Min({Len(log[i]), nextIndex[i][j]})}),
                msource |-> i, mdest |-> j]
        <5>1. Min({Len(log[i]), nextIndex[i][j]}) \in Nat
            BY MinProperties, LenProperties
        <5>2. Min({commitIndex[i], Min({Len(log[i]), nextIndex[i][j]})}) \in Nat
            <6>1. {commitIndex[i], Min({Len(log[i]), nextIndex[i][j]})} /= {}
                OBVIOUS
            <6>2. commitIndex[i] \in Nat
                OBVIOUS
            <6> QED
                BY MinProperties, <5>1, <6>1, <6>2
        <5>3. m.mentries \in Seq([term : Nat, value : Value])
            BY SubSeqProperties, MinProperties
        <5>4. m.mprevLogTerm \in Nat
            OBVIOUS
        <5>5. m.mprevLogIndex \in Int
            OBVIOUS
        <5>6. m \in MessageType
            BY <5>2, <5>3, <5>4, <5>5
            DEF MessageType, AppendEntriesRequestType
        <5> QED
          BY <4>7, <5>6, WithMessage_MessageType, WithMessage_IsABag
          DEF AppendEntries, serverVars, candidateVars, leaderVars, logVars, Send
      <4>8. CASE \E m \in DOMAIN messages : Receive(m)
        <5> USE DEF Receive
        <5> SUFFICES ASSUME NEW m \in DOMAIN messages,
                            Receive(m)
                     PROVE  TypeOK'
          BY <4>8
        <5> DEFINE i == m.mdest
        <5> DEFINE j == m.msource
        <5>0. i \in Server /\ j \in Server
           BY DEF BagToSet, MessageType, RequestVoteRequestType,
                  AppendEntriesRequestType, RequestVoteResponseType,
                  AppendEntriesResponseType
        <5>1. CASE UpdateTerm(i, j, m)
           <6>1. m \in MessageType
              BY DEF BagToSet
           <6>2. m.mterm \in Nat
              BY <6>1
              DEF MessageType, RequestVoteRequestType,
                  AppendEntriesRequestType, RequestVoteResponseType,
                  AppendEntriesResponseType
           <6> QED
              BY <5>1, <6>2, DistinctRoles
              DEF UpdateTerm, candidateVars, leaderVars, logVars
        <5>2. CASE /\ m.mtype = RequestVoteRequest
                   /\ HandleRequestVoteRequest(i, j, m)
           <6> DEFINE logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                               \/ /\ m.mlastLogTerm = LastTerm(log[i])
                                  /\ m.mlastLogIndex >= Len(log[i])
           <6> DEFINE grant == /\ m.mterm = currentTerm[i]
                               /\ logOk
                               /\ votedFor[i] \in {Nil, j}
           <6> DEFINE m_1 == [mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm[i],
                            mvoteGranted |-> grant,
                            mlog         |-> log[i],
                            msource      |-> i,
                            mdest        |-> j]
                     
           <6>2. m_1 \in MessageType
              BY <5>0 DEF MessageType, RequestVoteResponseType
           <6>3. m \in MessageType
              BY DEF BagToSet
           <6>4. /\ IsABag(WithMessage(m_1, messages))
                 /\ BagToSet(WithMessage(m_1, messages)) \subseteq MessageType
              BY <6>2, WithMessage_IsABag, WithMessage_MessageType
           <6>5. /\ IsABag(WithoutMessage(m,WithMessage(m_1, messages)))
                 /\ BagToSet(WithoutMessage(m,WithMessage(m_1, messages))) \subseteq MessageType
              BY <6>3, <6>4, WithoutMessage_IsABag, WithoutMessage_MessageType
           <6>6. IsABag(messages') /\ BagToSet(messages') \subseteq MessageType
              BY <5>2, <6>5 DEF HandleRequestVoteRequest, Reply
           <6> QED
              BY <5>2, <5>0, <6>2, <6>6
              DEF HandleRequestVoteRequest, leaderVars, candidateVars, logVars
        <5>3. CASE /\ m.mtype = RequestVoteResponse
                   /\ \/ DropStaleResponse(m.mdest, m.msource, m)
                      \/ HandleRequestVoteResponse(m.mdest, m.msource, m)
           <6>1. m \in MessageType
              BY DEF BagToSet
           <6>2. CASE DropStaleResponse(i, j, m)
              BY <5>3, <6>1, <6>2, WithoutMessage_IsABag,
                  WithoutMessage_MessageType
              DEF DropStaleResponse, Discard, serverVars,
                  candidateVars, leaderVars, logVars
           <6>3. CASE HandleRequestVoteResponse(i, j, m)
                BY <5>0, <5>3, <6>1, <6>3, WithoutMessage_IsABag,
                   WithoutMessage_MessageType
                DEF HandleRequestVoteResponse, Discard,
                    serverVars, leaderVars, logVars
           <6> QED
              BY <5>3, <6>2, <6>3
        <5>4. CASE /\ m.mtype = AppendEntriesRequest
                   /\ HandleAppendEntriesRequest(i, j, m)
           <6> m \in MessageType
              BY DEF MessageType, AppendEntriesRequestType, BagToSet
           <6>0. m \in AppendEntriesRequestType
                 BY <5>4, DistinctMessageTypes
                 DEF MessageType, RequestVoteRequestType, AppendEntriesRequestType,
                     RequestVoteResponseType, AppendEntriesResponseType
           <6> DEFINE logOk == \/ m.mprevLogIndex = 0
                               \/ /\ m.mprevLogIndex > 0
                                  /\ m.mprevLogIndex <= Len(log[i])
                                  /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
           <6>1. CASE RejectAppendEntriesRequest(i, j, m, logOk)
              <7> DEFINE m_1 ==
                     [mtype |-> AppendEntriesResponse,
                      mterm |-> currentTerm[m.mdest], msuccess |-> FALSE,
                      mmatchIndex |-> 0, msource |-> m.mdest,
                      mdest |-> m.msource]
              <7>1. m_1 \in MessageType
                BY <5>0 DEF MessageType, AppendEntriesResponseType
              <7> QED
                 BY <5>4, <6>1, <7>1, Reply_messagesType
                 DEF HandleAppendEntriesRequest, RejectAppendEntriesRequest,
                     serverVars, logVars, candidateVars, leaderVars
           <6>2. CASE ReturnToFollowerState(i, m)
              BY <5>4, <6>2, DistinctRoles
              DEF HandleAppendEntriesRequest, ReturnToFollowerState, logVars,
                  candidateVars, leaderVars
           <6>3. CASE AcceptAppendEntriesRequest(i, j, logOk, m)
              <7> DEFINE index == m.mprevLogIndex + 1
              <7>0. state[i] = Follower
                BY <6>3 DEF AcceptAppendEntriesRequest
              <7>2. m.mprevLogIndex \in Nat
                BY <6>3, <6>0
                DEF AcceptAppendEntriesRequest, AppendEntriesRequestType
              <7>3. CASE AppendEntriesAlreadyDone(i, j, index, m)
                 <8>1. [mtype |-> AppendEntriesResponse,
                        mterm |-> currentTerm[m.mdest], msuccess |-> TRUE,
                        mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                        msource |-> m.mdest, mdest |-> m.msource] \in MessageType
                    BY <5>0, <6>0, <7>2, LenProperties
                    DEF MessageType, AppendEntriesRequestType, AppendEntriesResponseType
                 <8> QED
                    BY <5>4, <7>2, <8>1, <7>3, Reply_messagesType
                    DEF AppendEntriesAlreadyDone, HandleAppendEntriesRequest,
                        AppendEntriesRequestType, candidateVars, leaderVars,
                        serverVars, logVars
              <7>4. CASE ConflictAppendEntriesRequest(i, index, m)
                <8>1. [index2 \in 1..Len(log[m.mdest]) - 1 |->
                               log[m.mdest][index2]]
                      \in Seq([term : Nat, value : Value])
                   BY <5>0
                <8>2. [log EXCEPT
                           ![m.mdest] = [index2 \in 1..Len(log[m.mdest]) - 1 |->
                                        log[m.mdest][index2]]]
                      \in [Server -> Seq([term : Nat, value : Value])]
                   BY <8>1
                <8>3. log' \in [Server -> Seq([term : Nat, value : Value])]
                   BY <8>2, <7>4 DEF ConflictAppendEntriesRequest
                <8>4. UNCHANGED <<messages, currentTerm, state, votedFor, commitIndex,
                                  votesResponded, votesGranted, nextIndex, matchIndex>>
                   BY <5>4, <7>4
                   DEF HandleAppendEntriesRequest, ConflictAppendEntriesRequest,
                       serverVars, candidateVars, leaderVars
                <8> QED
                    BY <8>3, <8>4, <7>0, <7>4, DistinctRoles
                    DEF ConflictAppendEntriesRequest
              <7>5. CASE NoConflictAppendEntriesRequest(i, m)
                <8>1. UNCHANGED <<messages, currentTerm, state, votedFor, commitIndex,
                                  votesResponded, votesGranted, nextIndex, matchIndex>>
                   BY <5>4, <7>5
                   DEF HandleAppendEntriesRequest, NoConflictAppendEntriesRequest,
                       serverVars, candidateVars, leaderVars
                <8>2. Append(log[m.mdest], (m.mentries)[1])
                      \in Seq([term : Nat, value : Value])
                   BY <7>5, <5>0, <6>0, AppendProperties
                   DEF AppendEntriesRequestType, NoConflictAppendEntriesRequest
                <8> QED
                   BY <7>0, <7>5, <8>1, <8>2, DistinctRoles
                   DEF NoConflictAppendEntriesRequest
              <7> QED
                BY <5>4, <6>3, <7>3, <7>4, <7>5
                DEF AcceptAppendEntriesRequest, candidateVars, leaderVars
           <6> QED
              BY <5>4, <6>1, <6>2, <6>3 DEF HandleAppendEntriesRequest
        <5>5. CASE /\ m.mtype = AppendEntriesResponse
                   /\ \/ DropStaleResponse(i, j, m)
                      \/ HandleAppendEntriesResponse(i, j, m)
           <6>1. CASE DropStaleResponse(i, j, m)
              BY <6>1, WithoutMessage_IsABag, WithoutMessage_MessageType
              DEF DropStaleResponse, Discard,
                  serverVars, candidateVars, leaderVars, logVars
           <6>2. CASE HandleAppendEntriesResponse(i, j, m)
              <7>1. m \in AppendEntriesResponseType
                 BY <5>5, DistinctMessageTypes
                 DEF BagToSet, MessageType, AppendEntriesResponseType,
                     RequestVoteRequestType, AppendEntriesRequestType,
                     RequestVoteResponseType
              <7> QED
                 BY <6>2, <7>1, WithoutMessage_IsABag, WithoutMessage_MessageType,
                    MaxProperties
                 DEF HandleAppendEntriesResponse, Discard, AppendEntriesResponseType,
                     serverVars, candidateVars, logVars 
           <6> QED
              BY <5>5, <6>1, <6>2
        <5> QED
            BY <5>1, <5>2, <5>3, <5>4, <5>5
      <4>9. CASE \E m \in DOMAIN messages : DuplicateMessage(m)
        BY <4>9, WithMessage_IsABag, WithMessage_MessageType
        DEF DuplicateMessage, Send, leaderVars, serverVars, candidateVars,
            logVars, BagToSet
      <4>10. CASE \E m \in DOMAIN messages : DropMessage(m)
        BY <4>10, WithoutMessage_IsABag, WithoutMessage_MessageType
        DEF DropMessage, Discard, leaderVars, serverVars, candidateVars,
            logVars, BagToSet
      <4>11. QED
        BY <3>1, <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9
        DEF Next
    <3>2. CASE UNCHANGED vars
        BY <3>2 DEF vars, serverVars, candidateVars, leaderVars, logVars
    <3>3. QED
      BY <3>1, <3>2
  <2>2. LeaderCompleteness'
  <2>3. QED
    BY <2>1, <2>2 DEF IndInv
<1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

\*<6>1. m \in AppendEntriesRequestType
\*           <6> DEFINE m_1 == [mtype |-> AppendEntriesResponse,
\*                            mterm |-> currentTerm[m.mdest],
\*                            msuccess |-> FALSE, mmatchIndex |-> 0,
\*                            msource |-> m.mdest, mdest |-> m.msource]
\*           <6>2. CASE Reply(m_1,m)
\*              <7>1. m_1 \in MessageType
\*              <7> QED
\*           <6> DEFINE m_2 == [mtype |-> AppendEntriesResponse,
\*                              mterm |-> currentTerm[m.mdest],
\*                              msuccess |-> TRUE,
\*                              mmatchIndex |-> m.mprevLogIndex
\*                                              + Len(m.mentries),
\*                              msource |-> m.mdest, mdest |-> m.msource]
\*           <6>3a. CASE Reply(m_2,m)
\*           <6>3b. log' = [log EXCEPT ![i] = [index2 \in 1..(Len(log[i]) - 1) |->
\*                                          log[i][index2]]]
\*           <6>3c. log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
\*           <6>4. state' = [state EXCEPT ![i] = Follower]
\*           <6> QED
\*              BY <5>4, <6>2, <6>3a, <6>3b, <6>3c, <6>4
\*              DEF HandleAppendEntriesRequest, candidateVars, leaderVars

\*        <5>1. ASSUME NEW i_1 \in Server,
\*                         state[i_1] = Leader
\*              PROVE nextIndex'[i_1] \in [Server -> 1..(Len(log'[i_1]) + 1)]
\*           <6>1. CASE i = i_1
\*              <7>1. Len(log'[i]) = Len(log[i]) + 1
\*                 BY <6>1, AppendProperties DEF ClientRequest
\*              <7>2. nextIndex[i] \in [Server -> 1..(Len((log)[i]) + 1)]
\*                 BY LenProperties DEF ClientRequest, leaderVars
\*              <7>3. 1..(Len((log)[i]) + 1) \subseteq 1..(Len((log)[i]) + 2)
\*                 BY LenProperties
\*              <7>4. nextIndex[i] \in [Server -> 1..(Len((log)[i]) + 2)]
\*                 BY <7>2, <7>3
\*              <7> QED
\*                 BY <5>1, <7>1, <7>4 DEF ClientRequest, leaderVars
\*           <6>2. CASE i /= i_1
\*              BY <5>1, <6>2 DEF ClientRequest, leaderVars
\*           <6> QED
\*              BY <6>1, <6>2

LEMMA TypeOKCorrect == Spec => TypeOK
<1>1. Init => TypeOK
    <2>1. Init => currentTerm \in [Server -> Nat]
        BY DEF Init, InitServerVars
    <2>2. Init => IsABag(messages) /\ BagToSet(messages) \subseteq MessageType
        <3>1. Init => IsABag(messages)
            BY DEF Init, IsABag, EmptyBag, SetToBag
        <3>2. QED
            BY <3>1, Bags_EmptyBag DEF Init, BagToSet
    <2>3. Init => log \in [Server -> Seq([term : Nat, value : Value])]
        BY DEF Init, InitLogVars
    <2>4. QED
        BY <2>1, <2>2, <2>3 DEF TypeOK
<1>2. TypeOK /\ Next => TypeOK'
  <2> USE DEF TypeOK
  <2> SUFFICES ASSUME TypeOK /\ Next
               PROVE  TypeOK'
    OBVIOUS
  <2>1. (currentTerm \in [Server -> Nat])'
    <3>1. CASE \E i \in Server : Restart(i)
        BY <3>1 DEF Restart
    <3>2. CASE \E i \in Server : Timeout(i)
        BY <3>2 DEF Timeout
    <3>3. CASE \E i,j \in Server : RequestVote(i, j)
        BY <3>3 DEF RequestVote, serverVars
    <3>4. CASE \E i \in Server : BecomeLeader(i)
        BY <3>4 DEF BecomeLeader
    <3>5. CASE \E i \in Server, v \in Value : ClientRequest(i, v)
        BY <3>5 DEF ClientRequest, serverVars
    <3>6. CASE \E i \in Server : AdvanceCommitIndex(i)
        BY <3>6 DEF AdvanceCommitIndex, serverVars
    <3>7. CASE \E i,j \in Server : AppendEntries(i, j)
        BY <3>7 DEF AppendEntries, serverVars
    <3>8. CASE \E m \in DOMAIN messages : Receive(m)
      <4> SUFFICES ASSUME NEW m \in DOMAIN messages,
                          Receive(m)
                   PROVE  (currentTerm \in [Server -> Nat])'
        BY <3>8
      <4> DEFINE i == m.mdest
      <4> DEFINE j == m.msource
      <4>1. CASE UpdateTerm(i, j, m)
        BY <4>1 DEF UpdateTerm, BagToSet, MessageType
      <4>2. CASE HandleRequestVoteRequest(i, j, m)
        BY <4>2 DEF HandleRequestVoteRequest
      <4>3. CASE DropStaleResponse(i, j, m)
        BY <4>3 DEF DropStaleResponse, serverVars
      <4>4. CASE HandleRequestVoteResponse(i, j, m)
        BY <4>4 DEF HandleRequestVoteResponse, serverVars
      <4>5. CASE HandleAppendEntriesRequest(i, j, m)
        BY <4>5 DEF HandleAppendEntriesRequest, serverVars
      <4>6. CASE DropStaleResponse(i, j, m)
        BY <4>6 DEF DropStaleResponse, serverVars
      <4>7. CASE HandleAppendEntriesResponse(i, j, m)
        BY <4>7 DEF HandleAppendEntriesResponse, serverVars
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7 DEF Receive
    <3>9. CASE \E m \in DOMAIN messages : DuplicateMessage(m)
        BY <3>9 DEF DuplicateMessage, serverVars
    <3>10. CASE \E m \in DOMAIN messages : DropMessage(m)
        BY <3>10 DEF DropMessage, serverVars
    <3>11. QED
      BY <3>1, <3>10, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Next
  <2>2. (log \in [Server -> Seq([term : Nat, value : Value])])'
  <2>3. (IsABag(messages) /\ BagToSet(messages) \subseteq MessageType)'
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF TypeOK
<1>3. QED
    BY <1>1, <1>2

LEMMA TypeOKCorrect1 ==
    Spec => TypeOK
<1>1. Init => TypeOK
    <2>1. Init => currentTerm \in [Server -> Nat]
        BY DEF Init, InitServerVars
    <2>2. Init => IsABag(messages) /\ BagToSet(messages) \subseteq MessageType
        <3>1. Init => IsABag(messages)
            BY DEF Init, IsABag, EmptyBag, SetToBag
        <3>2. QED
            BY <3>1, Bags_EmptyBag DEF Init, BagToSet
    <2>3. Init => log \in [Server -> Seq([term : Nat, value : Value])]
        BY DEF Init, InitLogVars
    <2>4. QED
        BY <2>1, <2>2, <2>3 DEF TypeOK
<1>2. TypeOK /\ Next => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      allLogs' = allLogs \cup {log[i] : i \in Server},
                      \/ \E i \in Server : Restart(i)
                      \/ \E i \in Server : Timeout(i)
                      \/ \E i,j \in Server : RequestVote(i, j)
                      \/ \E i \in Server : BecomeLeader(i)
                      \/ \E i \in Server, v \in Value : ClientRequest(i, v)
                      \/ \E i \in Server : AdvanceCommitIndex(i)
                      \/ \E i,j \in Server : AppendEntries(i, j)
                      \/ \E m \in DOMAIN messages : Receive(m)
                      \/ \E m \in DOMAIN messages : DuplicateMessage(m)
                      \/ \E m \in DOMAIN messages : DropMessage(m)
               PROVE  TypeOK'
    BY DEF Next
  <2> USE DEF TypeOK
  <2>1. CASE \E i \in Server : Restart(i)
    BY <2>1 DEF Restart
  <2>2. CASE \E i \in Server : Timeout(i)
    BY <2>2 DEF Timeout, logVars
  <2>3. CASE \E i,j \in Server : RequestVote(i, j)
    BY <2>3 DEF MessageType, RequestVote, Send, WithMessage,
                               LastTerm
  <2>4. CASE \E i \in Server : BecomeLeader(i)
    BY <2>4 DEF BecomeLeader, logVars
  <2>5. CASE \E i \in Server, v \in Value : ClientRequest(i, v)
    BY <2>5 DEF ClientRequest, serverVars
  <2>6. CASE \E i \in Server : AdvanceCommitIndex(i)
    BY <2>6 DEF AdvanceCommitIndex, serverVars
  <2>7. CASE \E i,j \in Server : AppendEntries(i, j)
    BY <2>7 DEF AppendEntries, Send, WithMessage, serverVars, logVars
  <2>8. CASE \E m \in DOMAIN messages : Receive(m)
    BY <2>8 DEF Receive, WithMessage, serverVars, logVars
  <2>9. CASE \E m \in DOMAIN messages : DuplicateMessage(m)
    <3> SUFFICES ASSUME NEW m \in DOMAIN messages,
                          DuplicateMessage(m)
                   PROVE  TypeOK'
        BY <2>9
    <3>1. IsABag(SetToBag({m}))
        BY DEF IsABag, SetToBag
    <3>2. DOMAIN messages' = DOMAIN messages
      <4>1. DOMAIN (messages (+) SetToBag({m})) =
            DOMAIN messages \cup DOMAIN SetToBag({m})
        BY Bags_Union, <3>1
      <4>2. QED
        BY <4>1 DEF DuplicateMessage, Send, WithMessage, SetToBag
    <3>3. IsABag(messages')
        BY <2>9, <3>1, Bags_Union DEF DuplicateMessage, Send, WithMessage
    <3>4. QED
        BY <3>2, <3>3, <2>9 DEF DuplicateMessage, BagToSet, serverVars, logVars
  <2>10. CASE \E m \in DOMAIN messages : DropMessage(m)
    <3>1. (currentTerm \in [Server -> Nat])'
        BY <2>10 DEF DropMessage, serverVars
    <3>2. (IsABag(messages) /\ BagToSet(messages) \subseteq MessageType)'
      <4> SUFFICES ASSUME NEW m \in DOMAIN messages,
                          DropMessage(m)
                   PROVE  (IsABag(messages) /\ BagToSet(messages) \subseteq MessageType)'
        BY <2>10
      <4>1. IsABag(SetToBag({m}))
        BY DEF IsABag, SetToBag
      <4>2. IsABag(messages')
        BY <2>1, <4>1, Bags_Difference DEF DropMessage, Discard, WithoutMessage 
      <4>3. DOMAIN messages' \subseteq DOMAIN messages
        BY <2>1, <4>1, Bags_Difference DEF DropMessage, Discard, WithoutMessage
      <4>4. QED
        BY <4>2, <4>3 DEF BagToSet
    <3>3. (log \in [Server -> Seq([term : Nat, value : Value])])'
        BY <2>10 DEF DropMessage, logVars
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF TypeOK
  <2>11. QED
    BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
<1>3. QED
    BY <1>1, <1>2

LEMMA TermMonotonic ==
  TypeOK /\ Next => \A i \in Server : currentTerm[i] =< currentTerm'[i]
  <1> SUFFICES ASSUME TypeOK,
                      allLogs' = allLogs \cup {log[i_1] : i_1 \in Server},
                      NEW i \in Server,
                      \/ \E i_1 \in Server : Restart(i_1)
                      \/ \E i_1 \in Server : Timeout(i_1)
                      \/ \E i_1,j \in Server : RequestVote(i_1, j)
                      \/ \E i_1 \in Server : BecomeLeader(i_1)
                      \/ \E i_1 \in Server, v \in Value : ClientRequest(i_1, v)
                      \/ \E i_1 \in Server : AdvanceCommitIndex(i_1)
                      \/ \E i_1,j \in Server : AppendEntries(i_1, j)
                      \/ \E m \in DOMAIN messages : Receive(m)
                      \/ \E m \in DOMAIN messages : DuplicateMessage(m)
                      \/ \E m \in DOMAIN messages : DropMessage(m)
               PROVE  currentTerm[i] =< currentTerm'[i]
    BY DEF Next
  <1>1. CASE \E i_1 \in Server : Restart(i_1)
    BY <1>1 DEF Restart, TypeOK
  <1>2. CASE \E i_1 \in Server : Timeout(i_1)
    BY <1>2 DEF Timeout, TypeOK
  <1>3. CASE \E i_1,j \in Server : RequestVote(i_1, j)
    BY <1>3 DEF RequestVote, TypeOK, serverVars
  <1>4. CASE \E i_1 \in Server : BecomeLeader(i_1)
    BY <1>4 DEF BecomeLeader, TypeOK
  <1>5. CASE \E i_1 \in Server, v \in Value : ClientRequest(i_1, v)
    BY <1>5 DEF ClientRequest, TypeOK, serverVars
  <1>6 CASE \E i_1 \in Server : AdvanceCommitIndex(i_1)
    BY <1>6 DEF AdvanceCommitIndex, TypeOK, serverVars
  <1>7. CASE \E i_1,j \in Server : AppendEntries(i_1, j)
    BY <1>7 DEF AppendEntries, TypeOK, serverVars
  <1>8. CASE \E m \in DOMAIN messages : Receive(m)
    BY <1>8 DEF Receive, TypeOK, UpdateTerm, HandleRequestVoteRequest,
                DropStaleResponse, HandleRequestVoteResponse,
                HandleAppendEntriesRequest, DropStaleResponse,
                HandleAppendEntriesResponse, serverVars
  <1>9. CASE \E m \in DOMAIN messages : DuplicateMessage(m)
    BY <1>9 DEF DuplicateMessage, TypeOK, serverVars
  <1>10. CASE \E m \in DOMAIN messages : DropMessage(m)
    BY <1>10 DEF DropMessage, TypeOK, serverVars
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10
===============================================================================

\* Changelog:
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
