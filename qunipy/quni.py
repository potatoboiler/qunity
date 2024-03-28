"""
re-create the type system here inside the Qunity class so that we can use it to map registers and outputs and groupings of auxiliary wires
"""

from collections import OrderedDict
import graphviz

import pprint

from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
from qiskit.converters import circuit_to_dag, dag_to_circuit
from qiskit.visualization import dag_drawer
from qiskit.dagcircuit import DAGCircuit
from qiskit.circuit.library import MCMT
from qiskit.circuit import Qubit
from qiskit.dagcircuit import DAGOutNode

cr0 = ClassicalRegister(1, "cr0")

circ1 = QuantumCircuit(QuantumRegister(3), cr0)
circ1.h([0, 1, 2])
circ1.measure(0, cr0[0])
# circ1.y([0, 2])

circ2 = QuantumCircuit(QuantumRegister(3), cr0)
circ2.x([0, 1, 2])
circ2.measure(0, cr0[0])

circ = QuantumCircuit(6)
circ.compose(circ1, [0, 1, 2], inplace=True)
circ.compose(circ2, [3, 4, 5], inplace=True)

circ3 = QuantumCircuit(QuantumRegister(6), cr0)
circ3.y([0, 1, 2, 3, 4, 5])
circ3.compose(circ, inplace=True)

a = circuit_to_dag(circ1)
b = circuit_to_dag(circ2)
c = b.compose(a, inplace=False)
# print(circ3)


class QunityComponent(QuantumCircuit):
    """
    Contains Qunity type information and corresponding
    """

    def __init__(self, *args, **kwargs):
        super(QunityComponent, self).__init__(*args, **kwargs)

    def compose(self, other, qubits=None, clbits=None, front=False, inplace=False):
        if isinstance(other, QunityComponent):
            return create_purepair(other)
        else:
            return super(QunityComponent, self).compose(
                other, qubits, clbits, front, inplace
            )


class QunityDAGComponent(DAGCircuit):
    def __init__(self):
        super(QunityDAGComponent, self).__init__()


print(QunityComponent(QuantumRegister(3), ClassicalRegister(1)))


# input
def create_control(component: DAGCircuit):
    pass


def create_purepair(component: DAGCircuit) -> DAGCircuit:
    num_qubits = component.num_qubits()
    print(component.qregs)

    output = circuit_to_dag(
        QuantumCircuit(
            QuantumRegister(num_qubits, "pair0"), QuantumRegister(num_qubits, "pair1")
        )
    )

    mcmt = circuit_to_dag(MCMT("x", num_qubits, num_qubits))
    output.compose(
        mcmt,
        qubits=list(range(num_qubits * 2)),
        inplace=True,
    )
    output.compose(component, qubits=list(range(num_qubits)), inplace=True)
    output.compose(
        component, qubits=list(range(num_qubits, 2 * num_qubits)), inplace=True
    )

    return output


def resize_registers(component: QuantumCircuit, new_qubits: int) -> DAGCircuit:
    component.qregs


d = QuantumCircuit(q := QuantumRegister(2, "qr0"), QuantumRegister(2, "qr1"))
d.x(q[0:2])
d.y(q[0:2])
d.cx(3, 0)
d.z([0])
dagd = circuit_to_dag(d)
pdagd = create_purepair(dagd)
# print(dag_to_circuit(pdagd))

pprint.pprint(pdagd.input_map)
pprint.pprint(pdagd.output_map)

print(dag_to_circuit(pdagd))
pprint.pprint(pdagd.input_map)
pprint.pprint(q[0:2])

QunityComponent(QuantumRegister(3), ClassicalRegister(1))
