load("polysys.sage")

class PlonkSystem:
    def __add_constant__( self, constant ):
        if not constant in self.wires.keys():
            index = len(self.wires)
            self.constants += [index]
            self.wires[constant] = index
            self.reverse_wires[index] = constant

    def __compute_term__( self, term ):
        #assert term.is_term(), "In __compute_term__ cannot compute term when argument is not a term!"
        assert len(term.exponents()) == 1, "In __compute_term__ cannot compute term when argument is not a term!"
        variables = list(self.polynomial_ring.gens())

        # collect factors
        factors = []        
        exponent = list(term.exponents()[0])
        coefficient = term.monomial_coefficient(term.monomials()[0])
        for i in range(len(variables)):
            while exponent[i] != 0:
                factors += [variables[i]]
                exponent[i] -= 1
        factors += [coefficient]

        # multiply them together
        accumulator = self.wires[factors[0]]
        for f in factors[1:]:
            assert f in self.wires.keys(), "In __compute_term__, cannot multiply accumulator by wires[f] because f is not in dictionary's keys"
            accumulator = self.__add_multiplication__(accumulator, self.wires[f])

        return accumulator

    def __add_multiplication__( self, lhs, rhs ):
        if (lhs, rhs) in self.multiplications.keys():
            return self.multiplications[(lhs, rhs)]
        elif (rhs, lhs) in self.multiplications.keys():
            return self.multiplications[(rhs, lhs)]
        else:
            index = len(self.wires)
            self.multiplications[(lhs, rhs)] = index
            product = self.reverse_wires[lhs]*self.reverse_wires[rhs]
            self.wires[product] = index
            self.reverse_wires[index] = product
            return index

    def __add_addition__( self, lhs, rhs ):
        if (lhs, rhs) in self.additions.keys():
            return self.additions[(lhs, rhs)]
        elif (rhs, lhs) in self.additions.keys():
            return self.additions[(rhs, lhs)]
        else:
            index = len(self.wires)
            self.additions[(lhs, rhs)] = index
            summ = self.reverse_wires[lhs] + self.reverse_wires[rhs]
            self.wires[summ] = index
            self.reverse_wires[index] = summ
            return index

    def __set_output__( self, output_index ):
        if not output_index in self.output_wires:
            self.output_wires += [output_index]

    def __init__( self, quadratic_polysys ):
        self.polynomial_ring = quadratic_polysys[0].parent() # every variable in this polynomial ring is an input
        variables = list(self.polynomial_ring.gens())
        self.F = self.polynomial_ring.base_ring()

        # declare member variables
        self.wires = dict() # maps polynomials to indices
        self.reverse_wires = dict() # maps indices to polynomials
        for i in range(len(variables)):
            self.wires[variables[i]] = i
            self.reverse_wires[i] = variables[i]
        self.additions = dict() # maps pairs of indices to singletons
        self.multiplications = dict() # maps pairs of indices to singletons
        self.output_wires = [] # list of indices

        # for all constants, add it to wires dict
        self.constants = []
        self.__add_constant__(self.F(0))
        self.__add_constant__(self.F(1))
        for p in quadratic_polysys:
            for v in p.dict().values():
                self.__add_constant__(v)

        # for all polynomials
        for p in quadratic_polysys:
            # compute sum of terms
            monomials = p.monomials()
            terms = [p.monomial_coefficient(m) * m for m in monomials]
            if len(terms) == 0:
                continue
            accumulator = self.__compute_term__(terms[0])
            for t in terms[1:]:
                accumulator = self.__add_addition__(accumulator, self.__compute_term__(t))
            self.__set_output__(accumulator)

    def IsRelationMember( self, inputs, outputs ):
        for k in range(len(outputs)):
            output_index = self.output_wires[k]
            polynomial = self.reverse_wires[output_index]
            if polynomial(inputs) != outputs[k]:
                return False
        return True

    def GetWireValues( self, inputs ):
        wire_values = []
        for k, v in self.wires.items():
            poly = self.polynomial_ring(k)
            wire_values += [poly(inputs)]
        return wire_values

    def AreGatesConsistent( self, wire_values ):
        for k, v in self.additions.items():
            l, r = k
            if wire_values[l] + wire_values[r] != wire_values[v]:
                return False
        for k, v in self.multiplications.items():
            l, r = k
            if wire_values[l] * wire_values[r] != wire_values[v]:
                return False
        return True

    def GetInputCount( self ):
        return len(list(self.polynomial_ring.gens()))

    def GetAdditionCount( self ):
        return len(self.additions)

    def GetMultiplicationCount( self ):
        return len(self.multiplications)

    def GetConstantsCount( self ):
        return len(self.constants)

    def GetWireCount( self ):
        return len(self.wires)

def PlonkSystemTest():
    F = FiniteField(previous_prime(2^128))
    n = 3
    m = 31
    Fx = PolynomialRing(F, n, "x")
    variables = list(Fx.gens())

    system = []
    for k in range(m):
        poly = Fx(0)
        for i in range(0, n):
            for j in range(0, i):
                poly += Fx(F.random_element()) * variables[i] * variables[j]
        system += [poly]

    plonk_circuit = PlonkSystem(system)

    inputs = [F.random_element() for i in range(n)]
    outputs = [s(inputs) for s in system]
    fake_outputs = [F.random_element() for s in system]
    wire_values = plonk_circuit.GetWireValues(inputs)
    fake_wire_values = [F.random_element() for w in wire_values]

    assert True == plonk_circuit.IsRelationMember(inputs, outputs), "Plonk constraint system generator does not recognize valid inputs"
    assert False == plonk_circuit.IsRelationMember(inputs, fake_outputs), "Plonk constraint system generator does not reject invalid outputs"
    assert True == plonk_circuit.AreGatesConsistent(wire_values), "Plonk system cannot generate consistent wire values"
    assert False == plonk_circuit.AreGatesConsistent(fake_wire_values), "Plonk system refuses to reject inconsistent wire values"
    assert plonk_circuit.GetWireCount() == plonk_circuit.GetInputCount() + plonk_circuit.GetAdditionCount() + plonk_circuit.GetMultiplicationCount() + plonk_circuit.GetConstantsCount(), "number of wires does not add up %i inputs %i additions %i multiplications %i constants %i total " % (plonk_circuit.GetInputCount(), plonk_circuit.GetAdditionCount(), plonk_circuit.GetMultiplicationCount(), plonk_circuit.GetConstantsCount(), plonk_circuit.GetWireCount())

    return True


class PlonkIop:
    def __init__( self, plonk_circuit ):
        self.circuit = plonk_circuit

    def GetPolyCount( self ):
        return 6

    def GetUniquePointCount( self ):
        return 2

    def GetQueryCount( self ):
        return 7

    def GetMaxDeg( self ):
        n = self.circuit.GetMultiplicationCount()
        a = self.circuit.GetAdditionCount()
        return 12 * (n + a)

