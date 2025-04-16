import re
from collections import defaultdict

# Diccionario que agrupa transiciones por (origen, destino)
transiciones_por_arista = defaultdict(set)

with open("prints", "r") as f:
    for linea in f:
        linea = linea.strip().strip('"')
        match = re.match(r'(.*)With(.*)To(.*)', linea)
        if match:
            origen = match.group(1)
            transicion = match.group(2)
            destino = match.group(3)

            # Agrupamos las transiciones por (origen, destino)
            transiciones_por_arista[(origen, destino)].add(transicion)

# Ahora escribimos el .dot
with open("grafo.dot", "w") as f:
    f.write("digraph Estados {\n")
    f.write("    rankdir=TB;\n")
    for (origen, destino), transiciones in sorted(transiciones_por_arista.items()):
        # Unimos las transiciones con saltos de línea (doble backslash)
        etiqueta = "\\n".join(sorted(transiciones))
        f.write(f'    "{origen}" -> "{destino}" [label="{etiqueta}"];\n')
    f.write("}\n")
