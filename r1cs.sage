load("polysys.sage")
load("hpr.sage")

class R1csSystem:
    def __init__( self, hpr_circuit ):
        self.A = []
        self.B = []
        self.C = []
        self.F = hpr_circuit.F
        n = hpr_circuit.GetMultiplicationCount()
        self.width = 1 + 3*n + len(hpr_circuit.linear_relations)
        for i in range(len(hpr_circuit.linear_relations)):
            left, right, output, constant = hpr_circuit.linear_relations[i]
            a = dict()
            b = dict()
            c = dict()
            if constant != self.F(0):
                c[0] = constant
            for k, v in left.items():
                c[1+k] = v
            for k, v in right.items():
                c[1+n+k] = v
            for k, v in output.items():
                c[1+2*n+k] = v
            c[1+3*n+i] = self.F(-1) # instance element selector
            self.A += [a]
            self.B += [b]
            self.C += [c]
        for k in range(hpr_circuit.GetMultiplicationCount()):
            a = {1+k: self.F(1)}
            b = {1+n+k: self.F(1)}
            c = {1+2*n+k: self.F(1)}
            self.A += [a]
            self.B += [b]
            self.C += [c]

    def LiftHprInstance( self, instance ):
        m = max(instance.keys())
        return [self.F(0) if not i in instance.keys() else instance[i] for i in range(m+1)]

    def LiftHprWitness( self, left_wires, right_wires, output_wires ):
        return [] + left_wires + right_wires + output_wires

    def IsRelationMember( self, instance, witness ):
        vector = [self.F(1)] + witness + instance
        vector += [self.F(0)] * (self.width - len(vector))
        for i in range(len(self.A)):
            ipa = self.F(0)
            for k, v in self.A[i].items():
                ipa += vector[k] * v
            ipb = self.F(0)
            for k, v in self.B[i].items():
                ipb += vector[k] * v
            ipc = self.F(0)
            for k, v in self.C[i].items():
                ipc += vector[k] * v
            if ipa * ipb != ipc:
                return False
        return True

    def GetNonzeroElementCount( self ):
        ka = sum(len(a) for a in self.A)
        kb = sum(len(b) for b in self.B)
        kc = sum(len(c) for c in self.C)
        k = ka
        if kb > k:
            k = kb
        if kc > k:
            k = kc
        return kc

    def GetMultiplicationCount( self ):
        return len(self.A)

def R1csSystemTest():
    F = FiniteField(previous_prime(2^128))
    n = 15
    m = 15
    Fx = PolynomialRing(F, n, "x")
    variables = list(Fx.gens())

    system = []
    for k in range(m):
        poly = Fx(0)
        for i in range(0, n):
            for j in range(0, i):
                poly += Fx(F.random_element()) * variables[i] * variables[j]
            poly += Fx(F.random_element()) * variables[i]
        poly += Fx(F.random_element())
        system += [poly]

    inputs = [F.random_element() for i in range(n)]
    hpr_circuit = HprSystem(system)
    hpr_instance, left_wires, right_wires, output_wires = hpr_circuit.GetInstanceAndWitness(inputs)

    r1cs_circuit = R1csSystem(hpr_circuit)
    instance = r1cs_circuit.LiftHprInstance(hpr_instance)
    fake_instance = [F.random_element() for i in instance]
    witness = r1cs_circuit.LiftHprWitness(left_wires, right_wires, output_wires)
    fake_witness = [F.random_element() for w in witness]

    assert True == r1cs_circuit.IsRelationMember(instance, witness), "R1CS constraint system generator does not recognize valid instance-witness pair"
    assert False == r1cs_circuit.IsRelationMember(fake_instance, witness), "R1CS constraint system generator does not reject invalid instance-witness pair"
    assert False == r1cs_circuit.IsRelationMember(instance, fake_witness), "R1CS constraint system generator does not reject invalid instance-witness pair"

    return True

class MarlinIop:
    def __init__( self, hpr_circuit ):
        self.circuit = hpr_circuit
    
    def GetPolyCount( self ):
        return 12

    def GetUniquePointCount( self ):
        return 3

    def GetQueryCount( self ):
        return 18

    def GetMaxDeg( self ):
        k = self.circuit.GetNonzeroElementCount()
        return 6 * k + 6

