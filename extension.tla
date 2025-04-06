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

followerWithRequestVoteToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithRestartToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithClientRequestToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithUpdateTermToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithRequestVoteToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithRestartToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithAppendEntriesToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithBecomeLeaderToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithClientRequestToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithUpdateTermToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

followerWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithRestartToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithRequestVoteToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithRequestVoteToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithRestartToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithRestartToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithClientRequestToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithClientRequestToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

followerWithUpdateTermToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Follower
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("followerWithUpdateTermToleaderMatchingQuorumNotLogUpToDate")
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

candidateVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRequestVoteToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRequestVoteToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithRestartToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithRestartToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithClientRequestToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithClientRequestToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateVotesInQuorumWithUpdateTermToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ votesGranted[i] \in Quorum
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateVotesInQuorumWithUpdateTermToleaderMatchingQuorumNotLogUpToDate")
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

candidateNotVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRequestVoteToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRequestVoteToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithRestartToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithRestartToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithClientRequestToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithClientRequestToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

candidateNotVotesInQuorumWithUpdateTermToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Candidate /\ \lnot(votesGranted[i] \in Quorum)
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("candidateNotVotesInQuorumWithUpdateTermToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRequestVoteTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRestartTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithClientRequestTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithUpdateTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRequestVoteToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRequestVoteToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRestartToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRestartToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithClientRequestToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithClientRequestToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithUpdateTermToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithUpdateTermToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRequestVoteToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRequestVoteToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRestartToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRestartToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithAppendEntriesToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithAppendEntriesToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithClientRequestToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithClientRequestToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithUpdateTermToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithUpdateTermToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRestartToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRestartToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRequestVoteToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRequestVoteToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithRestartToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithRestartToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithClientRequestToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithClientRequestToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumLogUpToDateWithUpdateTermToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumLogUpToDateWithUpdateTermToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRequestVoteTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRestartTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithClientRequestTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithUpdateTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRequestVoteToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRequestVoteToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRestartToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRestartToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithClientRequestToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithClientRequestToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithUpdateTermToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithUpdateTermToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRequestVoteToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRequestVoteToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRestartToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRestartToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithAppendEntriesToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithAppendEntriesToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithBecomeLeaderToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithBecomeLeaderToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithClientRequestToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithClientRequestToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithUpdateTermToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithUpdateTermToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRestartToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRestartToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRequestVoteToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRequestVoteToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithRestartToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithRestartToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithClientRequestToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithClientRequestToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumLogUpToDateWithUpdateTermToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ commitIndex[i] = Len(log[i])
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumLogUpToDateWithUpdateTermToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRestartTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithClientRequestTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermTofollower")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRestartToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRestartToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithClientRequestToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithClientRequestToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRestartToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRestartToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithClientRequestToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithClientRequestToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRestartToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRestartToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRequestVoteToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithRestartToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithRestartToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithClientRequestToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithClientRequestToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ \lnot({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderNotMatchingQuorumNotLogUpToDateWithUpdateTermToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRequestVoteTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRequestVoteTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRestartTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRestartTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithAppendEntriesTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithAppendEntriesTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithClientRequestTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithClientRequestTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithUpdateTermTofollower == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Follower
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithUpdateTermTofollower")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRequestVoteTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRequestVoteTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRestartTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRestartTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithAppendEntriesTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithAppendEntriesTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithClientRequestTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithClientRequestTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithUpdateTermTocandidateVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ votesGranted'[i] \in Quorum
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithUpdateTermTocandidateVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRequestVoteTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRequestVoteTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRestartTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRestartTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithAppendEntriesTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithAppendEntriesTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithClientRequestTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithClientRequestTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithUpdateTermTocandidateNotVotesInQuorum == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Candidate /\ \lnot(votesGranted'[i] \in Quorum)
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithUpdateTermTocandidateNotVotesInQuorum")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRequestVoteToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRequestVoteToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRestartToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRestartToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithClientRequestToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithClientRequestToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithUpdateTermToleaderNotMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithUpdateTermToleaderNotMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRequestVoteToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRequestVoteToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRestartToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRestartToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithClientRequestToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithClientRequestToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithUpdateTermToleaderMatchingQuorumLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ commitIndex'[i] = Len(log'[i])
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithUpdateTermToleaderMatchingQuorumLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRequestVoteToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRestartToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRestartToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithClientRequestToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ \lnot({index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i]) /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithUpdateTermToleaderNotMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRequestVoteToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ RequestVote(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRequestVoteToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithRestartToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ Restart(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithRestartToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E j \in Server : AppendEntries(i, j))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithAppendEntriesToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ BecomeLeader(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithBecomeLeaderToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithClientRequestToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E v \in Value : ClientRequest(i, v))
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithClientRequestToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ \lnot(/\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
                /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i]) 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} 
       /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] 
       /\ AdvanceCommitIndex(i)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithNoTrivialAdvanceCommitIndexToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

leaderMatchingQuorumNotLogUpToDateWithUpdateTermToleaderMatchingQuorumNotLogUpToDate == [][\lnot (\E i \in Server :
    IF /\ state[i] = Leader /\ {index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum} /= {} /\ log[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex[i][k] >= index }) \in Quorum})].term = currentTerm[i] /\ \lnot(commitIndex[i] = Len(log[i]))
       /\ (\E m \in DOMAIN messages : /\ m.mdest = i 
                                      /\ m.mterm > currentTerm[m.mdest] 
                                      /\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]
                                      /\ state'          = [state       EXCEPT ![m.mdest] = Follower]
                                      /\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]
                                      /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)
       /\ state'[i] = Leader /\ {index \in 1..Len(log'[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum} /= {} /\ log'[i][Max({index \in 1..Len(log[i]) : ({i} \cup {k \in Server : /\ matchIndex'[i][k] >= index }) \in Quorum})].term = currentTerm'[i] /\ \lnot(commitIndex'[i] = Len(log'[i]))
    THEN /\ TRUE 
         /\ PrintT("leaderMatchingQuorumNotLogUpToDateWithUpdateTermToleaderMatchingQuorumNotLogUpToDate")
    ELSE FALSE)]_vars

=============================================================================