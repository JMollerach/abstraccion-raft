import graphviz

states =        {"follower":"/\\ state[i] = Follower",
                 "candidateVotesInQuorum":"/\\ state[i] = Candidate /\\ votesGranted[i] \\in Quorum",
                 "candidateNotVotesInQuorum":"/\\ state[i] = Candidate /\\ \\lnot(votesGranted[i] \\in Quorum)",
                 "leaderNotMatchingQuorumLogUpToDate":"/\\ state[i] = Leader /\\ \\lnot({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i]) /\\ commitIndex[i] = Len(log[i])",
                 "leaderMatchingQuorumLogUpToDate":"/\\ state[i] = Leader /\\ {index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i] /\\ commitIndex[i] = Len(log[i])",
                 "leaderNotMatchingQuorumNotLogUpToDate":"/\\ state[i] = Leader /\\ \\lnot({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i]) /\\ \\lnot(commitIndex[i] = Len(log[i]))",
                 "leaderMatchingQuorumNotLogUpToDate":"/\\ state[i] = Leader /\\ {index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i] /\\ \\lnot(commitIndex[i] = Len(log[i]))"}

transitions = {"RequestVote": "RequestVote(i)",
               "Restart": "Restart(i)",
               "AppendEntries": "(\\E j \\in Server : AppendEntries(i, j))",
               "BecomeLeader":"BecomeLeader(i)",
               "ClientRequest":"(\\E v \\in Value : ClientRequest(i, v))",
               "TrivialAdvanceCommitIndex":"\\lnot(/\\ {index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} \n                /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i]) \n       /\\ AdvanceCommitIndex(i)",
               "NoTrivialAdvanceCommitIndex":"{index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} \n       /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i] \n       /\\ AdvanceCommitIndex(i)"}


def generate_digraph():
    dot = graphviz.Digraph()    
    for flecha in etiquetas:
        dot.edge(
            flecha[0].replace("-", "\\n"),
            flecha[1].replace("-", "\\n"),
            label="\\n".join(etiquetas[flecha]),
            fontsize="10")
    dot.render(f"{ruta_archivos_salidas}/abstraccion.dot")
    registro(f"Digrafo guardado en {ruta_archivos_salidas}/abstraccion.dot[.pdf]")