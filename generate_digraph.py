import re

# Usamos un set para guardar las transiciones únicas
transiciones_unicas = set()

with open("prints", "r") as f:
    for linea in f:
        linea = linea.strip().strip('"')
        match = re.match(r'(.*)With(.*)To(.*)', linea)
        if match:
            origen = match.group(1)
            transicion = match.group(2)
            destino = match.group(3)

            # Guardamos una tupla que representa la transición
            transiciones_unicas.add((origen, transicion, destino))

# Ahora escribimos el .dot solo con las transiciones únicas
with open("grafo.dot", "w") as f:
    f.write("digraph Estados {\n")
    f.write("    rankdir=TB;\n")
    for origen, transicion, destino in sorted(transiciones_unicas):
        f.write(f'    "{origen}" -> "{destino}" [label="{transicion}"];\n')
    f.write("}\n")
