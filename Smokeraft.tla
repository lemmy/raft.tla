---- MODULE Smokeraft ----
EXTENDS MCraft, TLC, Randomization

LOCAL BoundedSeq(S, n) ==
    (* Copy&Pasted from CommunityModules *)
    UNION {[1..m -> S] : m \in 0..n}

SmokeSeq(S) ==
    BoundedSeq(S, 1)

SmokeNat ==
    0..1

SmokeInt ==
    -1..1

k ==
    1

\* The next four definitions give the types of each type of message.
\* Contrary to the ones in raft.tla, these defs are changed to define
\* finite sets.
SmokeRequestVoteRequestType ==
    [mtype : {RequestVoteRequest},
     mterm : SmokeNat,
     mlastLogTerm : SmokeNat,
     mlastLogIndex : SmokeNat,
     msource : Server,
     mdest : Server]

SmokeAppendEntriesRequestType ==
    [mtype : {AppendEntriesRequest},
       mterm : SmokeNat,
       mprevLogIndex : SmokeInt,
       mprevLogTerm : SmokeNat,
       mentries : SmokeSeq([term : SmokeNat, value : Value]),
       mcommitIndex : SmokeNat,
       msource : Server,
       mdest : Server]

SmokeRequestVoteResponseType ==
    [mtype : {RequestVoteResponse},
     mterm : SmokeNat,
     mvoteGranted : BOOLEAN,
     mlog : SmokeSeq([term : SmokeNat, value : Value]),
     msource : Server,
     mdest : Server]

SmokeAppendEntriesResponseType ==
    [mtype : {AppendEntriesResponse},
     mterm : SmokeNat,
     msuccess : BOOLEAN,
     mmatchIndex : SmokeNat,
     msource : Server,
     mdest : Server]

SmokeMessageType ==
    RandomSubset(k, SmokeRequestVoteRequestType) \cup 
    RandomSubset(k, SmokeAppendEntriesRequestType) \cup
    RandomSubset(k, SmokeRequestVoteResponseType) \cup
    RandomSubset(k, SmokeAppendEntriesResponseType)

SmokeInit ==
    (* A variant of raft!TypeOK that defines a finite set of initial states. *)
    (* https://lamport.azurewebsites.net/tla/inductive-invariant.pdf *)
    /\ currentTerm \in RandomSubset(k, [Server -> SmokeNat])
    /\ state \in RandomSubset(k, [Server -> {Follower, Candidate, Leader}])
    /\ votedFor \in RandomSubset(k, [Server -> Server \cup {Nil}])
    /\ log \in RandomSubset(k, [Server -> BoundedSeq([term : SmokeNat, value : Value], 2)])
    /\ commitIndex \in RandomSubset(k, [Server -> SmokeNat])
    /\ votesResponded \in RandomSubset(k, [Server -> SUBSET Server])
    /\ votesGranted \in RandomSubset(k, [Server -> SUBSET Server])
    /\ nextIndex \in RandomSubset(k, [Server -> [Server -> { n \in SmokeNat : 1 <= n } ]])
    /\ matchIndex \in RandomSubset(k, [Server -> [Server -> SmokeNat]])
    \* /\ messages \in [RandomSubset(k, SmokeMessageType) -> {1}]
    /\ messages = EmptyBag \* The set MessageType would have to be "tamed" for RandomElement(MessageType) to work.
    /\ IsABag(messages)
    /\ BagToSet(messages) \subseteq MessageType

----

\* StopAfter  has to be configured as a state constraint. It stops TLC after ~1
\* second or after generating 100 traces, whatever comes first, unless TLC
\* encountered an error.  In this case,  StopAfter  has no relevance.
StopAfter ==
    (* The smoke test has a time budget of 1 second. *)
    \* \/ TLCSet("exit", TLCGet("duration") > 1)
    \* (* Generating 100 traces should provide reasonable coverage. *)
    \* \/ TLCSet("exit", TLCGet("diameter") > 100)
    TRUE

====