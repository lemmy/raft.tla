---- MODULE Smokeraft ----
EXTENDS MCraft, TLC

LOCAL BoundedSeq(S, n) ==
    (* Copy&Pasted from CommunityModules *)
    UNION {[1..m -> S] : m \in 0..n}

SmokeNat ==
    0..2

SmokeInit ==
    (* A variant of raft!TypeOK that defines a finite set of initial states. *)
    (* https://lamport.azurewebsites.net/tla/inductive-invariant.pdf *)
    /\ currentTerm \in {RandomElement([Server -> SmokeNat])}
    /\ state \in {RandomElement([Server -> {Follower, Candidate, Leader}])}
    /\ votedFor \in {RandomElement([Server -> Server \cup {Nil}])}
    /\ log \in {RandomElement([Server -> BoundedSeq([term : SmokeNat, value : Value], 3)])}
    /\ commitIndex \in {RandomElement([Server -> SmokeNat])}
    /\ votesResponded \in {RandomElement([Server -> SUBSET Server])}
    /\ votesGranted \in {RandomElement([Server -> SUBSET Server])}
    /\ nextIndex \in {RandomElement([Server -> [Server -> { n \in SmokeNat : 1 <= n } ]])}
    /\ matchIndex \in {RandomElement([Server -> [Server -> SmokeNat]])}
    /\ messages = EmptyBag \* The set MessageType would have to be "tamed" for RandomElement(MessageType) to work.
    /\ IsABag(messages)
    /\ BagToSet(messages) \subseteq MessageType

----

\* StopAfter  has to be configured as a state constraint. It stops TLC after ~1
\* second or after generating 100 traces, whatever comes first, unless TLC
\* encountered an error.  In this case,  StopAfter  has no relevance.
StopAfter ==
    (* The smoke test has a time budget of 1 second. *)
    \/ TLCSet("exit", TLCGet("duration") > 1)
    (* Generating 100 traces should provide reasonable coverage. *)
    \/ TLCSet("exit", TLCGet("diameter") > 100)    

====