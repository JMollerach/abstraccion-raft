states =        {"follower":"/\\ state[i] = Follower",
                 "candidateVotesInQuorum":"/\\ state[i] = Candidate /\\ votesGranted[i] \\in Quorum",
                 "candidateNotVotesInQuorum":"/\\ state[i] = Candidate /\\ \\lnot(votesGranted[i] \\in Quorum)",
                 "leaderNotMatchingQuorumLogUpdated":"/\\ state[i] = Leader /\\ \\lnot({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i]) /\\ commitIndex[i] = Len(log[i])",
                 "leaderMatchingQuorumLogUpdated":"/\\ state[i] = Leader /\\ {index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i] /\\ commitIndex[i] = Len(log[i])",
                 "leaderNotMatchingQuorumNotLogUpdated":"/\\ state[i] = Leader /\\ \\lnot({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i]) /\\ \\lnot(commitIndex[i] = Len(log[i]))",
                 "leaderMatchingQuorumNotLogUpdated":"/\\ state[i] = Leader /\\ {index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i] /\\ \\lnot(commitIndex[i] = Len(log[i]))"}

primed_states = {"follower":"/\\ state'[i] = Follower",
                 "candidateVotesInQuorum":"/\\ state'[i] = Candidate /\\ votesGranted'[i] \\in Quorum",
                 "candidateNotVotesInQuorum":"/\\ state'[i] = Candidate /\\ \\lnot(votesGranted'[i] \\in Quorum)",
                 "leaderNotMatchingQuorumLogUpdated":"/\\state'[i] = Leader /\\ \\lnot({index \\in 1..Len(log'[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum} /= {} /\\ log'[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum})].term = currentTerm'[i]) /\\ commitIndex'[i] = Len(log'[i])",
                 "leaderMatchingQuorumLogUpdated":"/\\ state'[i] = Leader /\\ {index \\in 1..Len(log'[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum} /= {} /\\ log'[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum})].term = currentTerm'[i] /\\ commitIndex'[i] = Len(log'[i])",
                 "leaderNotMatchingQuorumNotLogUpdated":"/\\ state'[i] = Leader /\\ \\lnot({index \\in 1..Len(log'[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum} /= {} /\\ log'[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum})].term = currentTerm'[i]) /\\ \\lnot(commitIndex'[i] = Len(log'[i]))",
                 "leaderMatchingQuorumNotLogUpdated":"/\\ state'[i] = Leader /\\ {index \\in 1..Len(log'[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum} /= {} /\\ log'[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum})].term = currentTerm'[i] /\\ \\lnot(commitIndex'[i] = Len(log'[i]))"}




transitions = {"RequestVote": "RequestVote(i)",
               "Restart": "Restart(i)",
               "AppendEntries": "(\\E j \\in Server : AppendEntries(i, j))",
               "BecomeLeader":"BecomeLeader(i)",
               "ClientRequest":"(\\E v \\in Value : ClientRequest(i, v))",
               "TrivialAdvanceCommitIndex":"\\lnot(/\\ {index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} \n                /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i]) \n       /\\ AdvanceCommitIndex(i)",
               "NoTrivialAdvanceCommitIndex":"{index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} \n       /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i] \n       /\\ AdvanceCommitIndex(i)",
               "UpdateTerm": "(\\E m \\in DOMAIN messages : /\\ m.mdest = i \n                                      /\\ m.mterm > currentTerm[m.mdest] \n                                      /\\ currentTerm'    = [currentTerm EXCEPT ![m.mdest] = m.mterm]\n                                      /\\ state'          = [state       EXCEPT ![m.mdest] = Follower]\n                                      /\\ votedFor'       = [votedFor    EXCEPT ![m.mdest] = Nil]\n                                      /\\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>)",
               "HRqVRqLEQCurrentTerm": "(\\E m \\in DOMAIN messages : /\\ i = m.mdest\n                                      /\\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm)\n                                      /\\ LET j     == m.msource\n                                             logOk == \\/ m.mlastLogTerm > LastTerm(log[i])\n                                                      \\/ /\\ m.mlastLogTerm = LastTerm(log[i])\n                                                         /\\ m.mlastLogIndex >= Len(log[i])\n                                             grant == /\\ m.mterm = currentTerm[i]\n                                                      /\\ logOk\n                                                      /\\ votedFor[i] \\in {Nil, j}\n                                         IN /\\ m.mterm <= currentTerm[i]\n                                            /\\ \\/ grant  /\\ votedFor' = [votedFor EXCEPT ![i] = j]\n                                               \\/ ~grant /\\ UNCHANGED votedFor\n                                            /\\ Reply([mtype        |-> RequestVoteResponse,\n                                                      mterm        |-> currentTerm[i],\n                                                      mvoteGranted |-> grant,\n                                                      msource      |-> i,\n                                                      mdest        |-> j],\n                                                      m)\n                                            /\\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, \n                                                           logVars, auxVars>>)",
               "HRqVRpGrantedEQCurrentTerm":"(\\E m \\in DOMAIN messages : /\\ i = m.mdest\n                                      /\ ReceivableMessage(m, RequestVoteResponse, EqualTerm)\n                                      /\\ m.mvoteGranted\n                                      /\\ LET j     == m.msource\n                                         IN\n                                             /\\ \\/ /\\ m.mvoteGranted\n                                                   /\\ votesGranted' = [votesGranted EXCEPT ![i] =\n                                                                             votesGranted[i] \\cup {j}]\n                                                \\/ /\\ ~m.mvoteGranted\n                                                   /\\ UNCHANGED <<votesGranted>>\n                                             /\\ Discard(m)\n                                             /\\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,\n                                                             auxVars>>)"}
##               "HRqVRpNotGrantedEQCurrentTerm":"(\\E m \\in DOMAIN messages : /\\ i = m.mdest\n                                      /\\ ~m.mvoteGranted\n                                      /\\ LET j     == m.msource\n                                         IN\n                                             /\\ \\/ /\\ m.mvoteGranted\n                                                   /\\ votesGranted' = [votesGranted EXCEPT ![i] =\n                                                                             votesGranted[i] \\cup {j}]\n                                                \\/ /\\ ~m.mvoteGranted\n                                                   /\\ UNCHANGED <<votesGranted>>\n                                             /\\ Discard(m)\n                                             /\\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars,\n                                                             auxVars>>)"}
##               "RejectAppEnRq":"(\\E m \\in DOMAIN messages : /\\ i = m.mdest\n        /\\ ReceivableMessage(m, AppendEntriesRequest, LessOrEqualTerm)\n        /\\ LET j     == m.msource\n               logOk == LogOk(i, m)\n           IN  /\\ \\/ m.mterm < currentTerm[i]\n                  \\/ /\\ m.mterm = currentTerm[i]\n                     /\\ state[i] = Follower\n                     /\\ \\lnot logOk\n               /\\ Reply([mtype           |-> AppendEntriesResponse,\n                         mterm           |-> currentTerm[i],\n                         msuccess        |-> FALSE,\n                         mmatchIndex     |-> 0,\n                         msource         |-> i,\n                         mdest           |-> j],\n                         m)\n               /\\ UNCHANGED <<state, candidateVars, leaderVars, serverVars, \n                              logVars, auxVars>>)"}

#faltaría arreglar indentanción en 2 transiciones (HRqVRqLEQCurrentTerm y rejectappenrq)

def extend_specification():
    with open("extension.tla", "w") as extension:
        extension.write("---------------------------- MODULE extension ----------------------------\n")
        extension.write("EXTENDS RaftVanlightly\n")
        for state_name in states.keys():
            for primed_state_name in primed_states.keys():
                    for transition_name in transitions.keys():
                        extension.write(state_name + "With" + transition_name + "To" + primed_state_name)
                        extension.write (" == [][\\lnot (\\E i \\in Server :\n    IF ")
                        extension.write(states[state_name]+"\n")
                        extension.write("       /\\ " + transitions[transition_name] + "\n ")
                        extension.write("      " + primed_states[primed_state_name] + "\n")
                        extension.write("    THEN /\\ TRUE \n         /\\ PrintT(\""+state_name+"With"+transition_name+"To"+primed_state_name+"\")\n")
                        extension.write("    ELSE FALSE)]_vars\n\n")
        extension.write("=============================================================================")
        
def generar_config():
     with open("config.cfg", "w") as config:
        config.write("CONSTANTS\n    n1 = n1\n    n2 = n2\n    n3 = n3\n    v1 = v1\n    Server = { n1, n2, n3}\n    Value = { v1 }\n    Follower = Follower\n    ")
        config.write("Candidate = Candidate\n    Leader = Leader\n    Nil = Nil\n    RequestVoteRequest = RequestVoteRequest\n    RequestVoteResponse = RequestVoteResponse\n    ")
        config.write("AppendEntriesRequest = AppendEntriesRequest\n    AppendEntriesResponse = AppendEntriesResponse\n    EqualTerm = EqualTerm\n    LessOrEqualTerm = LessOrEqualTerm\n    ")
        config.write("MaxElections = 2\n    MaxRestarts = 1\n\n")
        config.write("INIT Init\nNEXT Next\n\nVIEW view\nSYMMETRY symmServers\n\nPROPERTY\n")
        for state_name in states.keys():
            for primed_state_name in primed_states.keys():
                for transition_name in transitions.keys():
                    config.write(state_name+"With"+transition_name+"To"+primed_state_name+"\n")

extend_specification()
generar_config()
