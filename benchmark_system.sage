load("rescue_prime.sage")
load("merkle_tree.sage")
load("polysys.sage")

def RescuePrime_PolySys(rescue_prime):
    N = rescue_prime.N
    MDS = rescue_prime.MDS
    MDSinv = MDS.inverse()
    m = rescue_prime.m
    cap = rescue_prime.capacity
    rate = rescue_prime.rate
    F = rescue_prime.Fp
    p = F.order()
    alpha = rescue_prime.alpha

    Fx = PolynomialRing(F, N*m+rate, "x")
    variables = list(Fx.gens())

    index=0
    state = matrix([variables[0:rate] + [F(0)] * (m-rate)]).transpose()
    index += rate
    sys = []
    for rnd in range(N):
        lhs = MDS * matrix([[state[i,0]^alpha] for i in range(m)]) + matrix([[rescue_prime.round_constants[2*rnd*m+i]] for i in range(0,m)])
        next_state = matrix([variables[index:index+m]]).transpose()
        index += m
        rhs = MDSinv * (next_state - matrix([[rescue_prime.round_constants[(2*rnd+1)*m+i]] for i in range(0,m)]))
        sys += [lhs[i,0] - rhs[i,0]^alpha for i in range(m)]
        state = next_state

    return sys

def RescuePrime_Trace(preimage, rescue_prime):
    N = rescue_prime.N
    MDS = rescue_prime.MDS
    MDSinv = MDS.inverse()
    m = rescue_prime.m
    capacity = rescue_prime.capacity
    rate = rescue_prime.rate
    assert len(preimage) == rate
    F = rescue_prime.Fp
    p = F.order()
    alpha = rescue_prime.alpha
    alphainv = rescue_prime.alphainv

    trace = copy(preimage)
    state = matrix(preimage + [F(0)]*capacity).transpose()
    for rnd in range(N):
        for i in range(m):
            state[i,0] = state[i,0]^alpha
        state = MDS * state
        for i in range(m):
            state[i,0] += rescue_prime.round_constants[2*rnd*m+i]
        for i in range(m):
            state[i,0] = state[i,0]^alphainv
        state = MDS * state
        for i in range(m):
            state[i,0] += rescue_prime.round_constants[(2*rnd+1)*m+i]
        trace += [state[i,0] for i in range(m)]
    return trace

def RescuePrime_Test():
    load("rescue_prime.sage")
    p = 5*2^127+1
    F = FiniteField(p)
    rescue_prime = RescuePrime(p, 3, 1, 128)
    rate = rescue_prime.rate
    m = rescue_prime.m
    
    preimage = [Random(F), Random(F)]
    image = rescue_prime.rescue_prime_hash(preimage)[0]

    system = RescuePrime_PolySys(rescue_prime)
    trace = RescuePrime_Trace(preimage, rescue_prime)

    assert PolySys_Eval(system, trace) == [F(0)] * len(system), "polynomial system does not evaluate to zero"
    assert trace[0] == preimage[0] and trace[1] == preimage[1] and trace[len(trace)-m] == image, "trace does not match regular hash evaluation"

    for i in range(10):
        index = ZZ(Integers(len(trace)).random_element())
        diff = 1 + ZZ(Integers(p-1).random_element())
        trace[index] += diff
        assert PolySys_Eval(system, trace) != [F(0)] * len(system), "polynomial system does evaluate to zero even though the trace was changed"
        trace[index] -= diff
    return True

def MerkleTreeMembership_PolySys(root, path_length, rescue_prime):
    rate = rescue_prime.rate
    capacity = rescue_prime.capacity
    m = rescue_prime.m
    F = FiniteField(rescue_prime.p)
    Fx = PolynomialRing(F, path_length, "x")
    path_bits = list(Fx.gens())

    # constraints for path bit variables
    polysys = [path_bits[i] * (path_bits[i]-1) for i in range(len(path_bits))]

    # add variables that represent leaf and authentication path
    polysys, leaf = PolySys_AddVars(polysys, 1)
    current_hash = leaf[0]
    polysys, authentication_path = PolySys_AddVars(polysys, path_length)

    # for each node on the path
    for i in range(path_length):
        # adjoin new rescue-prime system
        sys = RescuePrime_PolySys(rescue_prime)
        sys = PolySys_Shift(sys, len(list(polysys[0].parent().gens())))
        new_vars = PolySys_ActiveVars(sys)
        polysys = polysys + sys
        polysys = PolySys_Uniformize(polysys)
        # equate inputs
        polysys += [new_vars[0] - current_hash * (1-path_bits[i]) - authentication_path[i] * path_bits[i]]
        polysys += [new_vars[1] - current_hash * path_bits[i] - authentication_path[i] * (1-path_bits[i])]
        # update current hash
        current_hash = new_vars[-m]
    
    # equate final current hash
    polysys += [current_hash - root]

    return polysys

def MerkleTreeMembership_Trace(leaf, index, path, rescue_prime):
    F = rescue_prime.Fp
    bit_string = bin(index)[2:]
    while len(bit_string) < len(path):
        bit_string = "0" + bit_string
    bit_string = list(reversed(bit_string))
    assert len(bit_string) == len(path), "bit length of index cannot be larger than length of path"

    trace = []

    # path variables
    for i in range(len(bit_string)):
        if bit_string[i] == "0":
            trace += [F(0)]
        elif bit_string[i] == "1":
            trace += [F(1)]
        else:
            print("Error, can't parse bit string")

    # leaf
    trace += [leaf]

    # authentication path
    trace += path

    # internal variables for every hash invocation
    current_hash = leaf
    for i in range(len(bit_string)):
        if bit_string[i] == "1":
            current_trace = RescuePrime_Trace([path[i], current_hash], rescue_prime)
            current_hash = rescue_prime.rescue_prime_hash([path[i], current_hash])[0]
        elif bit_string[i] == "0":
            current_trace = RescuePrime_Trace([current_hash, path[i]], rescue_prime)
            current_hash = rescue_prime.rescue_prime_hash([current_hash, path[i]])[0]
        else:
            print("bit_string[i]:", bit_string[i])
        trace += current_trace

    # root
    # (already added; root is in final state of permutation)

    return trace

def MerkleTreeMembership_Test():
    p = 5*2^127+1
    F = FiniteField(p)
    load("rescue_prime.sage")
    rescue_prime = RescuePrime(p, 3, 1, 128)

    N = 8
    array = [Random(F) for i in range(N)]

    load("merkle_tree.sage")
    root = MerkleRoot(array, rescue_prime)
    index = 1
    leaf = array[index]
    path = MerklePath(array, index, rescue_prime)

    polysys = MerkleTreeMembership_PolySys(root, len(path), rescue_prime)
    trace = MerkleTreeMembership_Trace(leaf, index, path, rescue_prime)
    fake_trace_0 = [Random(F) for i in range(len(trace))]
    fake_trace_2 = MerkleTreeMembership_Trace(Random(F), index, path, rescue_prime)
    fake_trace_3 = MerkleTreeMembership_Trace(leaf, (index + 1 + ZZ(Integers(N-1).random_element())) % N, path, rescue_prime)
    fake_trace_4 = MerkleTreeMembership_Trace(leaf, index , [Random(F) for i in range(0, len(path))], rescue_prime)

    assert PolySys_Eval(polysys, trace) == [F(0)]*len(polysys)
    assert PolySys_Eval(polysys, fake_trace_0) != [F(0)]*len(polysys), "random trace evaluates to zero"
    assert PolySys_Eval(polysys, fake_trace_2) != [F(0)]*len(polysys), "trace for random leaf evaluates to zero"
    assert PolySys_Eval(polysys, fake_trace_3) != [F(0)]*len(polysys), "trace for random index evaluates to zero"
    assert PolySys_Eval(polysys, fake_trace_4) != [F(0)]*len(polysys), "trace for random path evaluates to zero"
    
    return True

def PolySys_MakeQuadratic_Test():
    p = 5*2^127+1
    F = FiniteField(p)
    load("rescue_prime.sage")
    rescue_prime = RescuePrime(p, 3, 1, 128)

    polysys = RescuePrime_PolySys(rescue_prime)
    preimage = [F.random_element() for i in range(2)]
    trace = RescuePrime_Trace(preimage, rescue_prime)
    faketrace = [F.random_element() for i in range(len(trace))]

    quadratic_polysys_1, quadratic_trace = PolySys_MakeQuadratic(copy(polysys), copy(trace))
    quadratic_polysys_2, quadratic_fake = PolySys_MakeQuadratic(copy(polysys), copy(faketrace))

    assert PolySys_Eval(quadratic_polysys_1, quadratic_trace) == [F(0)] * len(quadratic_polysys_1)
    assert PolySys_Eval(quadratic_polysys_2, quadratic_fake) != [F(0)] * len(quadratic_polysys_2)
    assert quadratic_polysys_1 == quadratic_polysys_2
    for qp in quadratic_polysys_1:
        assert qp.degree() <= 2

    return True

