load("polysys.sage")

class HprSystem:
    def __add_linear_relation__( self, left, right, output, constant ):
        self.linear_relations += [(left, right, output, constant)]

    def __copy_left__( self, source_index, target_index ):
        '''Inserts a copy constraint from output to left wire vectors'''
        self.left_wires[target_index] = self.output_wires[source_index]
        left = dict()
        left[target_index] = self.F(-1)
        right = dict()
        output = dict()
        output[source_index] = self.F(1)
        self.__add_linear_relation__(left, right, output, self.F(0))

    def __copy_right__( self, source_index, target_index ):
        '''Inserts a copy constraint from output to right wire vectors'''
        self.right_wires[target_index] = self.output_wires[source_index]
        left = dict()
        right = dict()
        right[target_index] = self.F(-1)
        output = dict()
        output[source_index] = self.F(1)
        self.__add_linear_relation__(left, right, output, self.F(0))

    def __compute_monomial__( self, monomial ):
        if monomial in self.wires.keys():
            return self.wires[monomial]
        else:
            assert monomial.degree() <= 2, "__compute_monomial__: cannot compute monomial of degree higher than 2"
            assert monomial.degree() > 0, "__compute_monomial__: cannot compute monomial of degree 0 or less"
            assert monomial.degree() != 1, f"__compute_monomial__: monomial of degree 1 should already be in wires keys {self.wires.keys()}"
            # otherwise, degree == 2
            # split into left and right operands
            exponents = list(monomial.exponents()[0])
            i = min(k for k in range(len(exponents)) if exponents[k] != 0)
            lhs = self.polynomial_ring.gens()[i]
            j = max(k for k in range(len(exponents)) if exponents[k] != 0)
            rhs = self.polynomial_ring.gens()[j]

            # create new multiplication triple
            new_index = len(self.left_wires)
            self.left_wires[new_index] = lhs
            self.right_wires[new_index] = rhs
            self.output_wires[new_index] = monomial
            self.wires[monomial] = new_index

            # copy left and right wires
            self.__copy_left__(self.wires[lhs], new_index)
            self.__copy_right__(self.wires[rhs], new_index)

            # return index of wire
            return new_index

    def __init__( self, quadratic_polysys ):
        self.polynomial_ring = quadratic_polysys[0].parent()
        variables = list(self.polynomial_ring.gens())
        self.F = self.polynomial_ring.base_ring()

        # declare member variables
        self.linear_relations = [] # list of tuples dict x dict x dict x field_element where the dicts map indices to field elements
        self.left_wires = dict() # maps indices to polynomials
        self.right_wires = dict() # maps indices to polynomials
        self.output_wires = dict() # maps indices to polynomials
        self.wires = dict() # maps polynomials to indices
        for i in range(len(variables)):
            self.wires[variables[i]] = i
            self.left_wires[i] = variables[i]
            self.right_wires[i] = self.polynomial_ring(1)
            self.output_wires[i] = variables[i]

        # for all polynomials
        for p in quadratic_polysys:
            indices = []
            relation = dict()
            constant = self.F(0)
            # for all monomials
            for m in p.monomials():
                if m.degree() >= 1:
                    # compute monomial
                    index = self.__compute_monomial__(m)
                    relation[index] = p.monomial_coefficient(m)
                else:
                    constant = p.monomial_coefficient(m)
            # add linear relation
            self.__add_linear_relation__(dict(), dict(), relation, constant)

    def IsRelationMember( self, instance, left_wires, right_wires, output_wires ):
        # check hadamard relation
        if len(left_wires) != len(right_wires) or len(right_wires) != len(output_wires):
            return False
        for i in range(len(left_wires)):
            if left_wires[i] * right_wires[i] != output_wires[i]:
                return False
        # check linear relation
        for i in range(len(self.linear_relations)):
            left, right, output, constant = self.linear_relations[i]
            acc = copy(constant)
            for k, v in left.items():
                acc += left_wires[k] * v
            for k, v in right.items():
                acc += right_wires[k] * v
            for k, v in output.items():
                acc += output_wires[k] * v
            if (i not in instance.keys() and acc != self.F(0)) or (i in instance.keys() and acc != instance[i]):
                return False
        return True

    def GetInstanceAndWitness( self, inputs ):
        # compute wires
        left_wires = [self.left_wires[i](inputs) for i in range(len(self.left_wires))]
        right_wires = [self.right_wires[i](inputs) for i in range(len(self.left_wires))]
        output_wires = [self.output_wires[i](inputs) for i in range(len(self.left_wires))]
        
        # compute instance
        instance = dict()
        for i in range(len(self.linear_relations)):
            left, right, output, constant = self.linear_relations[i]
            acc = copy(constant)
            for k, v in left.items():
                acc += left_wires[k] * v
            for k, v in right.items():
                acc += right_wires[k] * v
            for k, v in output.items():
                acc += output_wires[k] * v
            if acc != self.F(0):
                instance[i] = acc

        return instance, left_wires, right_wires, output_wires

    def ReduceMaxFanIn( self, M, left_wires=[], right_wires=[], output_wires=[] ):
        assert M > 2, "cannot reduce fanin below 3"
        i = 0
        while i < len(self.linear_relations): # we may need to keep iterating as we expand this set
            left, right, output, constant = self.linear_relations[i]
            if ( constant != self.F(0) and len(output) >= M ) or len(output) > M:
                # split in two
                outputl = dict()
                outputr = dict()
                j = 0
                for k, v in output.items():
                    if j < M-1 - (0 if constant == self.F(0) else 1):
                        outputl[k] = v
                    else:
                        outputr[k] = v
                    j += 1
                # compute symbolic value
                symbolic_value = sum(self.output_wires[k] for k, v in outputr.items())
                # create new multiplication triple
                index = len(self.left_wires)
                self.left_wires[index] = symbolic_value
                self.right_wires[index] = self.polynomial_ring(1)
                self.output_wires[index] = symbolic_value
                self.wires[symbolic_value] = index
                # update witness if necessary
                if len(left_wires) != 0:
                    concrete_value = sum(output_wires[k] * v for k, v in outputr.items())
                    left_wires += [concrete_value]
                    right_wires += [self.F(1)]
                    output_wires += [concrete_value]
                    # test new witness
                    assert left_wires[index] * right_wires[index] == output_wires[index], "multiplication relation of new multiplication triple does not hold"
                # reference new output wire in left and right linear relation
                outputl[index] = self.F(1)
                outputr[index] = self.F(-1)
                # test new linear relations
                if len(left_wires) != 0:
                    sumo = constant + sum(left_wires[k] * v for k, v in left.items()) + sum(right_wires[k] * v for k, v in right.items()) + sum(output_wires[k] * v for k, v in output.items())
                    suml = constant + sum(left_wires[k] * v for k, v in left.items()) + sum(right_wires[k] * v for k, v in right.items()) + sum(output_wires[k] * v for k, v in outputl.items())
                    sumr = sum(output_wires[k] * v for k, v in outputr.items())
                    assert sumo == suml + sumr, "sum of new linear relation does not equal original sum"
                # replace and append linear relations
                self.linear_relations[i] = (left, right, outputl, constant)
                self.linear_relations += [(dict(), dict(), outputr, self.F(0))]
            i += 1

    def GetMaxFanIn( self ):
        maxfanin = 0
        for relation in self.linear_relations:
            left, right, output, constant = relation
            if constant == self.F(0):
                fanin = 0
            else:
                fanin = 1
            fanin += len(left) + len(right) + len(output)
            if fanin > maxfanin:
                maxfanin = fanin
        return maxfanin

    def GetMaxColWeight( self ):
        maxcolweight = 0
        # max of left wires
        for i in range(len(self.left_wires)):
            colweight = 0
            for left, right, output, constant in self.linear_relations:
                if i in left.keys() and left[i] != 0:
                    colweight += 1
            if colweight > maxcolweight:
                maxcolweight = colweight
        # max of right wires
        for i in range(len(self.left_wires)):
            colweight = 0
            for left, right, output, constant in self.linear_relations:
                if i in right.keys() and right[i] != 0:
                    colweight += 1
            if colweight > maxcolweight:
                maxcolweight = colweight
        # max of output wires
        for i in range(len(self.left_wires)):
            colweight = 0
            for left, right, output, constant in self.linear_relations:
                if i in output.keys() and output[i] != 0:
                    colweight += 1
            if colweight > maxcolweight:
                maxcolweight = colweight
        return maxcolweight

    def GetConstantsColWeight( self ):
        colweight = 0
        for left, right, output, constant in self.linear_relations:
            if constant != 0:
                colweight += 1
        return colweight

    def ReduceMaxColWeight( self, M, left_wires = [], right_wires = [], output_wires = [] ):
        # fix left wires
        i = 0
        while i < len(self.left_wires):
            # determine col weight
            weight = 0
            for left, right, output, constant in self.linear_relations:
                if i in left.keys() and left[i] != 0:
                    weight += 1
            # if small enough, ignore
            if weight <= M:
                i += 1
                continue
            # otherwise:
            # add wire
            index = len(self.left_wires)
            p = self.left_wires[i]
            self.left_wires[index] = p
            self.right_wires[index] = self.F(1)
            self.output_wires[index] = p
            # self.wires[p] = index
            # if necessary, expand witness
            if left_wires != []:
                left_wires += [left_wires[i]]
                right_wires += [self.F(1)]
                output_wires += [left_wires[i]]
            # create copy constraint
            copy_constraint = {i: self.F(1), index: -self.F(1)}
            copy_relation = (copy_constraint, dict(), dict(), self.F(0))
            # keep M-1 relations, move remaining relations to new wire
            counter = 0
            for j in range(len(self.linear_relations)):
                left, right, output, constant = self.linear_relations[j]
                if not i in left.keys() or left[i] == self.F(0):
                    continue
                else:
                    counter += 1
                if counter >= M:
                    left[index] = left[i]
                    del left[i]
                    self.linear_relations[j] = (left, right, output, constant)
            # add copy constraint to new wire
            self.linear_relations += [copy_relation]
            # prepare for next loop iteration
            i += 1

        # fix right wires
        i = 0
        while i < len(self.left_wires):
            # determine col weight
            weight = 0
            for left, right, output, constant in self.linear_relations:
                if i in right.keys() and right[i] != 0:
                    weight += 1
            # if small enough, ignore
            if weight <= M:
                i += 1
                continue
            # otherwise:
            # add wire
            index = len(self.right_wires)
            p = self.right_wires[i]
            self.right_wires[index] = p
            self.left_wires[index] = self.F(1)
            self.output_wires[index] = p
            # self.wires[p] = index
            # if necessary, expand witness
            if right_wires != []:
                right_wires += [right_wires[i]]
                left_wires += [self.F(1)]
                output_wires += [right_wires[i]]
            # create copy constraint
            copy_constraint = {i: self.F(1), index: -self.F(1)}
            copy_relation = (dict(), copy_constraint, dict(), self.F(0))
            # keep M-1 relations, move remaining relations to new wire
            counter = 0
            for j in range(len(self.linear_relations)):
                left, right, output, constant = self.linear_relations[j]
                if not i in right.keys() or right[i] == self.F(0):
                    continue
                else:
                    counter += 1
                if counter >= M:
                    right[index] = right[i]
                    del right[i]
                    self.linear_relations[j] = (left, right, output, constant)
            # add copy constraint to new wire
            self.linear_relations += [copy_relation]
            # prepare for next loop iteration
            i += 1

        # fix output wires
        i = 0
        while i < len(self.output_wires):
            # determine col weight
            weight = 0
            for left, right, output, constant in self.linear_relations:
                if i in output.keys() and output[i] != 0:
                    weight += 1
            # if small enough, ignore
            if weight <= M:
                i += 1
                continue
            # otherwise:
            # add wire
            index = len(self.output_wires)
            p = self.output_wires[i]
            self.right_wires[index] = p
            self.left_wires[index] = self.F(1)
            self.output_wires[index] = p
            # self.wires[p] = index
            # if necessary, expand witness
            if output_wires != []:
                right_wires += [output_wires[i]]
                left_wires += [self.F(1)]
                output_wires += [output_wires[i]]
            # create copy constraint
            copy_constraint = {i: self.F(1), index: -self.F(1)}
            copy_relation = (dict(), dict(), copy_constraint, self.F(0))
            # keep M-1 relations, move remaining relations to new wire
            counter = 0
            for j in range(len(self.linear_relations)):
                left, right, output, constant = self.linear_relations[j]
                if not i in output.keys() or output[i] == self.F(0):
                    continue
                else:
                    counter += 1
                if counter >= M:
                    output[index] = output[i]
                    del output[i]
                    self.linear_relations[j] = (left, right, output, constant)
            # add copy constraint to new wire
            self.linear_relations += [copy_relation]
            # prepare for next loop iteration
            i += 1

    def GetMultiplicationCount( self ):
        return len(self.left_wires)

    def GetInputCount( self ):
        return len(list(self.polynomial_ring.gens()))

    def GetLinearRelationCount( self ):
        return len(self.linear_relations)

    def GetNonzeroElementCount( self ):
        acc = 0
        for relation in self.linear_relations:
            left, right, output, constant = relation
            acc += len(left)
            acc += len(right)
            acc += len(output)
            if constant != self.F(0):
                acc += 1
        return acc

def HprSystemTest():
    F = FiniteField(previous_prime(2^128))
    n = 5
    m = 5
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

    hpr_circuit = HprSystem(system)
    print("Have HPR circuit with ", hpr_circuit.GetMultiplicationCount(), " multiplications, fan-in ", hpr_circuit.GetMaxFanIn(), ", and max col weight ", hpr_circuit.GetMaxColWeight())

    inputs = [F.random_element() for i in range(n)]
    return_value = hpr_circuit.GetInstanceAndWitness(inputs)
    instance, left_wires, right_wires, output_wires = hpr_circuit.GetInstanceAndWitness(inputs)
    fake_instance_0 = {k: F.random_element() for k, v in instance.items()}
    fake_instance_1 = copy(instance)
    fake_instance_1[ZZ(Integers(len(instance)).random_element())] = F.random_element()
    fake_left_wires = [F.random_element() for i in range(len(left_wires))]
    fake_right_wires = [F.random_element() for i in range(len(left_wires))]
    fake_output_wires = [F.random_element() for i in range(len(left_wires))]

    fanin = hpr_circuit.GetMaxFanIn()

    assert True == hpr_circuit.IsRelationMember(instance, left_wires, right_wires, output_wires), "HPR constraint system generator does not recognize valid instance-witness pair"
    assert False == hpr_circuit.IsRelationMember(fake_instance_0, left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(fake_instance_1, left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, fake_left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, left_wires, fake_right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, left_wires, right_wires, fake_output_wires)

    M = 3

    hpr_circuit.ReduceMaxFanIn(M, left_wires, right_wires, output_wires)
    fake_left_wires = [F.random_element() for i in range(len(left_wires))]
    fake_right_wires = [F.random_element() for i in range(len(left_wires))]
    fake_output_wires = [F.random_element() for i in range(len(left_wires))]

    assert True == hpr_circuit.IsRelationMember(instance, left_wires, right_wires, output_wires), "HPR constraint system does not correctly reduce fan-in"
    assert hpr_circuit.GetMaxFanIn() <= M, f"HPR constraint system's max fan-in ({hpr_circuit.GetMaxFanIn()}) is greater than what it should have been reduced to ({M})"
    assert False == hpr_circuit.IsRelationMember(fake_instance_0, left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(fake_instance_1, left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, fake_left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, left_wires, fake_right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, left_wires, right_wires, fake_output_wires)

    hpr_circuit.ReduceMaxColWeight(M, left_wires, right_wires, output_wires)
    print("Have HPR circuit with ", hpr_circuit.GetMultiplicationCount(), " multiplications, fan-in ", hpr_circuit.GetMaxFanIn(), ", and max col weight ", hpr_circuit.GetMaxColWeight())
    fake_left_wires = [F.random_element() for i in range(len(left_wires))]
    fake_right_wires = [F.random_element() for i in range(len(left_wires))]
    fake_output_wires = [F.random_element() for i in range(len(left_wires))]

    assert True == hpr_circuit.IsRelationMember(instance, left_wires, right_wires, output_wires), "HPR constraint system does not correctly reduce max column weight"
    assert hpr_circuit.GetMaxColWeight() <= M, f"HPR constraint system's max column weight ({hpr_circuit.GetMaxColWeight()}) is greater than what it should have been reduced to ({M})"
    assert False == hpr_circuit.IsRelationMember(fake_instance_0, left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(fake_instance_1, left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, fake_left_wires, right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, left_wires, fake_right_wires, output_wires)
    assert False == hpr_circuit.IsRelationMember(instance, left_wires, right_wires, fake_output_wires)

    return True


class DenseClaymoreIop:
    def __init__( self, hpr_circuit ):
        self.circuit = hpr_circuit

    def GetPolyCount( self ):
        return 4

    def GetUniquePointCount( self ):
        return 6

    def GetQueryCount( self ):
        return 10

    def GetMaxDeg( self ):
        q = 2
        n = self.circuit.GetMultiplicationCount()
        m = self.circuit.GetLinearRelationCount()
        return (3 * (n + 3*q) + 1) * m - 1

class SparseClaymoreIop:
    def __init__( self, hpr_circuit ):
        self.circuit = hpr_circuit
    
    def GetPolyCount( self ):
        return 10

    def GetUniquePointCount( self ):
        return 10

    def GetQueryCount( self ):
        return 30

    def GetMaxDeg( self ):
        K = self.circuit.GetNonzeroElementCount()
        return 6 * K - 1

class SonicIop:
    def __init__( self, hpr_circuit, M ):
        self.circuit = hpr_circuit
        self.circuit.ReduceMaxFanIn(M)
        self.circuit.ReduceMaxColWeight(M)
        self.M = M

    def GetPolyCount( self ):
        return 3 * self.M + 7

    def GetUniquePointCount( self ):
        return 9 * self.M + 2

    def GetQueryCount( self ):
        return 11 * self.M + 3

    def GetMaxDeg( self ):
        return 7 * self.circuit.GetMultiplicationCount()

