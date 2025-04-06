predicados =          {"follower":"state[i] = Follower",
                       "candidate":"state[i] = Candidate",
                       "leader":"state[i] = Leader",
                       "votesInQuorum":"state[i] = Candidate /\\ votesGranted[i] \\in Quorum",
                       "matchingQuorum":"state[i] = Leader /\\ {index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i]",
                       "committedLogUpToDate":"/\\ commitIndex[i] = Len(log[i])"}
predicados_primados = {"follower":"state'[i] = Follower",
                       "candidate":"state'[i] = Candidate",
                       "leader":"state'[i] = Leader",
                       "votesInQuorum":"state'[i] = Candidate /\\ votesGranted'[i] \\in Quorum",
                       "matchingQuorum":"state'[i] = Leader /\\ {index \\in 1..Len(log'[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum} /= {} /\\ log'[i][Max({index \\in 1..Len(log'[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex'[i][k] >= index }) \\in Quorum})].term = currentTerm'[i]",
                       "committedLogUpToDate":"/\\ commitIndex'[i] = Len(log'[i])"}
etiquetas = {"RequestVote": "RequestVote(i)",
             "Restart": "Restart(i)",
             "AppendEntries": "\\E j \\in Server : AppendEntries(i, j)",
             "BecomeLeader":"BecomeLeader(i)",
             "ClientRequest":"\\E v \\in Value : ClientRequest(i, v)",
             "TrivialAdvanceCommitIndex":"\\lnot({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i] /\\ AdvanceCommitIndex(i))",
             "NoTrivialAdvanceCommitIndex":"{index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum} /= {} /\\ log[i][Max({index \\in 1..Len(log[i]) : ({i} \\cup {k \\in Server : /\\ matchIndex[i][k] >= index }) \\in Quorum})].term = currentTerm[i] /\\ AdvanceCommitIndex(i)"}
#             "UpdateTerm":"(\\E m \\in DOMAIN messages : i = m.mdest /\\ m.mterm > currentTerm[m.mdest] /\\ currentTerm' = [currentTerm EXCEPT ![m.mdest] = m.mterm] /\\ state' = [state EXCEPT ![m.mdest] = Follower] /\\ votedFor' = [votedFor EXCEPT ![m.mdest] = Nil]) /\\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, auxVars>>",
#             "HRqVRq<=CurrentTerm":"\\E m \\in DOMAIN messages : i = m.mdest /\\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm) /\\ LET logOk == \\/ m.mlastLogTerm > LastTerm(log[i]) \\/ /\\ m.mlastLogTerm = LastTerm(log[i]) /\\ m.mlastLogIndex >= Len(log[i]) grant == /\\ m.mterm = currentTerm[i] /\\ logOk /\\ votedFor[i] \\in {Nil, j} IN /\\ m.mterm <= currentTerm[i] /\\ \\/ grant  /\\ votedFor' = [votedFor EXCEPT ![i] = j] \\/ ~grant /\\ UNCHANGED votedFor /\\ Reply([mtype|-> RequestVoteResponse, mterm        |-> currentTerm[i], mvoteGranted |-> grant,msource      |-> i,mdest        |-> j],m) /\\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, auxVars>>",
#             "HRqVRpGranted=CurrentTerm":"\\E m \\in DOMAIN messages : /\\ ReceivableMessage(m, RequestVoteRequest, LessOrEqualTerm) /\\ LET j     == m.msource \n logOk == \\/ m.mlastLogTerm > LastTerm(log[i]) \\/ /\\ m.mlastLogTerm = LastTerm(log[i]) /\\ m.mlastLogIndex >= Len(log[i]) grant == /\\ m.mterm = currentTerm[i] /\\ logOk /\\ votedFor[i] \\in {Nil, j} IN /\\ m.mterm <= currentTerm[i] /\\ \\/ grant  /\\ votedFor' = [votedFor EXCEPT ![i] = j] \\/ ~grant /\ UNCHANGED votedFor /\\ Reply([mtype        |-> RequestVoteResponse, mterm        |-> currentTerm[i], mvoteGranted |-> grant,msource      |-> i, mdest        |-> j],m) /\\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, auxVars>>",
#             "HRqVRpNotGranted":"\\E m \in DOMAIN messages :"}
estados = {}
estados_primados = {}

def generar_estados(dicc_predicados):
    n = len(dicc_predicados)
    result = {}

    # 1 << n = to 2^n
    for i in range(1 << n):   
        subset = ""
        nombre = ""
        j=0
        for predicado in dicc_predicados.keys():
          
            # If the j-th bit is set in i, include
            # the j-th character from s
            if i & (1 << j):
                nombre += predicado
                subset += " /\\ " + dicc_predicados[predicado]
            else:
                nombre += "not" + predicado
                subset += " /\\ \\lnot(" + dicc_predicados[predicado] + ")"
            j+=1
        result[nombre]=subset

    return result

            

def extender_especificacion():
    with open("extension.tla", "w") as extension:
        extension.write("---------------------------- MODULE extension ----------------------------\n")
        extension.write("EXTENDS RaftVanlightly\n")
        global estados
        global estados_primados
        estados = generar_estados(predicados)
        estados_primados = generar_estados(predicados_primados)
        for i in estados.keys():
            for j in estados_primados.keys():
                for etiqueta in etiquetas.keys():
                    extension.write(i + etiqueta + "To" + j)
                    extension.write (" == [][\\lnot (\\E i \\in Server :\n    IF")
                    extension.write(estados[i]+"\n")
                    extension.write("       /\\ " + etiquetas[etiqueta] + "\n")
                    extension.write("      " + estados_primados[j] + "\n")
                    extension.write("    THEN /\\ TRUE \n         /\\ PrintT(\""+str(i)+etiqueta+"to"+str(j)+"\")\n")
                    extension.write("    ELSE FALSE)]_vars\n\n")
        extension.write("=============================================================================")
        

def generar_config():
    with open("config.cfg", "w") as config:
        config.write("CONSTANTS\n    n1 = n1\n    n2 = n2\n    n3 = n3\n    v1 = v1\n    Server = { n1, n2, n3}\n    Value = { v1 }\n    Follower = Follower\n    ")
        config.write("Candidate = Candidate\n    Leader = Leader\n    Nil = Nil\n    RequestVoteRequest = RequestVoteRequest\n    RequestVoteResponse = RequestVoteResponse\n    ")
        config.write("AppendEntriesRequest = AppendEntriesRequest\n    AppendEntriesResponse = AppendEntriesResponse\n    EqualTerm = EqualTerm\n    LessOrEqualTerm = LessOrEqualTerm\n    ")
        config.write("MaxElections = 2\n    MaxRestarts = 0\n\n")
        config.write("INIT Init\nNEXT Next\n\nVIEW view\nSYMMETRY symmServers\n\nPROPERTY\n")
        for i in estados.keys():
            for j in estados_primados.keys():
                for etiqueta in etiquetas.keys():
                    config.write(i + etiqueta + "To" + j + "\n")

"""
def generar_digrafo():
    digraph finite_state_machine { 
    fontname="Helvetica,Arial,sans-serif"
    node [fontname="Helvetica,Arial,sans-serif"]
    edge [fontname="Helvetica,Arial,sans-serif"]
    rankdir=LR;
    node [shape = circle];
    n0[label="Follower"];
    n1[label="Candidate0"];
    n2[label="Candidate1"];
    n0->n1;
}
"""
extender_especificacion()
generar_config()

""""
def generar_digrafo(ruta_archivos_salidas, transiciones_respondidas):
    # Agrupar transiciones entre estados iguales
    etiquetas = {}
    for transición in transiciones_respondidas:
        respuesta = transiciones_respondidas[transición]
        if respuesta is False: continue
        estados = (transición.estado_partida.nombre, transición.estado_llegada.nombre)
        if estados not in etiquetas.keys():
            etiquetas[estados] = []
        if respuesta is True:
            etiquetas[estados].append(transición.función_tomada.nombre)
        if respuesta is None:
            etiquetas[estados].append(transición.función_tomada.nombre + "[¿?]")
    
    # Generar el digrafo con tales transiciones
    dot = graphviz.Digraph()    
    for flecha in etiquetas:
        dot.edge(
            flecha[0].replace("-", "\\n"),
            flecha[1].replace("-", "\\n"),
            label="\\n".join(etiquetas[flecha]),
            fontsize="10")
    dot.render(f"{ruta_archivos_salidas}/abstraccion.dot")
    registro(f"Digrafo guardado en {ruta_archivos_salidas}/abstraccion.dot[.pdf]")"
    """