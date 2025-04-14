---------------------------- MODULE extension ----------------------------
EXTENDS RaftVanlightly
followerWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteTofollower")
    ELSE FALSE)]_vars

followerWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartTofollower")
    ELSE FALSE)]_vars

followerWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

followerWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

followerWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestTofollower")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

followerWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermTofollower")
    ELSE FALSE)]_vars

followerWithHRqVRqLEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRqLEQCurrentTermTofollower")
    ELSE FALSE)]_vars

followerWithHRqVRpGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

followerWithHRqVRpNotGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpNotGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

followerWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

followerWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

followerWithRequestVoteToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithRestartToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithAppendEntriesToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithClientRequestToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithUpdateTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithRequestVoteToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithRestartToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithAppendEntriesToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithBecomeLeaderToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithClientRequestToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithUpdateTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

followerWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithRestartToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithClientRequestToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithRequestVoteToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithRestartToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithAppendEntriesToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithClientRequestToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithUpdateTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

followerWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRqLEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRqLEQCurrentTermTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRequestVoteTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRestartTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithClientRequestTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithUpdateTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRequestVoteToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRequestVoteToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRestartToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRestartToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithClientRequestToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithClientRequestToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithUpdateTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithUpdateTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRequestVoteToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRequestVoteToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRestartToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRestartToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithAppendEntriesToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithAppendEntriesToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithClientRequestToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithClientRequestToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithUpdateTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithUpdateTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRestartToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRestartToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithClientRequestToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithClientRequestToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRequestVoteToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRequestVoteToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithRestartToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithRestartToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithAppendEntriesToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithAppendEntriesToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithClientRequestToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithClientRequestToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithUpdateTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithUpdateTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRequestVoteTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRestartTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithClientRequestTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithUpdateTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRequestVoteToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRequestVoteToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRestartToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRestartToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithClientRequestToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithClientRequestToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithUpdateTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithUpdateTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRequestVoteToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRequestVoteToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRestartToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRestartToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithAppendEntriesToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithAppendEntriesToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithBecomeLeaderToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithBecomeLeaderToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithClientRequestToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithClientRequestToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithUpdateTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithUpdateTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRestartToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRestartToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithClientRequestToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithClientRequestToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRequestVoteToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRequestVoteToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithRestartToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithRestartToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithAppendEntriesToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithAppendEntriesToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithClientRequestToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithClientRequestToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithUpdateTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithUpdateTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRestartTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithClientRequestTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRestartToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRestartToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithClientRequestToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithClientRequestToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRestartToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRestartToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithClientRequestToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithClientRequestToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRestartToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRestartToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithClientRequestToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithClientRequestToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRequestVoteToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithRestartToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithRestartToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithClientRequestToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithClientRequestToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithUpdateTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRequestVoteTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRestartTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithClientRequestTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithUpdateTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRequestVoteToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRequestVoteToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRestartToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRestartToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithClientRequestToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithClientRequestToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithUpdateTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithUpdateTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRequestVoteToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRequestVoteToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRestartToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRestartToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithClientRequestToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithClientRequestToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithUpdateTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithUpdateTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRequestVoteToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRestartToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRestartToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithClientRequestToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithClientRequestToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithUpdateTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderNotMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRequestVoteToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRequestVoteToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithRestartToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithRestartToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithAppendEntriesToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithBecomeLeaderToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithClientRequestToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithClientRequestToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithUpdateTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithUpdateTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)
                                      /\ LET j     == m.msource
                                             logOk == \/ m.mlastLogTerm > LastTerm(log[i])
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
                                                      msource      |-> i,
                                                      mdest        |-> j],
                                                      m)
                                            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                                                           logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRqLEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ i = m.mdest
                                      /\ ~m.mvoteGranted
                                      /\ LET j     == m.msource
                                         IN
                                             /\ \/ /\ m.mvoteGranted
                                                   /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                                             votesGranted[i] \cup {j}]
                                                \/ /\ ~m.mvoteGranted
                                                   /\ UNCHANGED <<votesGranted>>
                                             /\ Discard(m)
                                             /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,
                                                             auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpdatedWithHRqVRpNotGrantedEQCurrentTermToleaderMatchingQuorumNotLogUpdated")
    ELSE FALSE)]_vars

=============================================================================