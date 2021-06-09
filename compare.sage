load("benchmark_system.sage")
load("plonk.sage")
load("hpr.sage")
load("r1cs.sage")
import time

def TableRow(iop, F, Gpairing, Gguo, lambd, s, rho):
    P = iop.GetPolyCount()
    U = iop.GetUniquePointCount()
    Q = iop.GetQueryCount()
    d = iop.GetMaxDeg()

    print("max degree:", d)

    kzg = (P+1) * Gpairing + (U+1) * (F+Gpairing)
    dark = P * floor(log(1.0*d, 2.0)) * (2*Gguo + U*F) + lambd * floor(log(1.0*d, 2.0)) + F
    fri = P * 2*lambd + Q * F + floor(log(1.0 * d, 2.0)) * s * ( floor(log(1.0 * rho * d, 2.0)) * 2*lambd + F )

    print("KZG:", ceil(kzg/8))
    print("DARK:", ceil(dark/8))
    print("FRI:", ceil(fri/8))

def Compare():
    # time
    tick = time.time()

    # parameters
    F = 256
    lambd = 128
    Gpairing = 385
    Gguo = 2000
    s = 32
    rho = 16
    M = 3
    logN = 10 # >= 2
    N = 2^logN

    # generate circuit
    print("Generatic circuit for proof of knowledge of Merkle path in tree of depth", logN, "...")
    p = 103 * 2^250 + 1
    m = 3
    c = 1
    rescue_prime = RescuePrime(p, m, c, 128)
    print("Rescue-Prime has ", rescue_prime.N, " rounds ...")
    array = [FiniteField(p).random_element() for i in range(N)]
    root = MerkleRoot(array, rescue_prime)
    index = ZZ(Integers(N).random_element())
    leaf = array[index]
    path = MerklePath(array, index, rescue_prime)

    system = MerkleTreeMembership_PolySys(root, len(path), rescue_prime)
    trace = MerkleTreeMembership_Trace(leaf, index, path, rescue_prime)

    # make quadratic
    quadratic_system, quadratic_trace = PolySys_MakeQuadratic(system, trace)

    # plonk
    print("Plonk ...")
    plonk_circuit = PlonkSystem(copy(quadratic_system))
    print("Have PLONK circuit with ", plonk_circuit.GetAdditionCount(), " additions, ", plonk_circuit.GetMultiplicationCount(), " multiplications, and ", plonk_circuit.GetWireCount(), " wires.")
    plonk_iop = PlonkIop(plonk_circuit)
    print("\nPLONK IOP:")
    TableRow(plonk_iop, F, Gpairing, Gguo, lambd, s, rho)
    print("\n")

    # hpr
    print("HPR ...")
    hpr_circuit = HprSystem(copy(quadratic_system))
    print("Have HPR circuit with ", hpr_circuit.GetLinearRelationCount(), " linear relations, ", hpr_circuit.GetMultiplicationCount(), " multiplications, and fan-in M =", hpr_circuit.GetMaxFanIn(), ".")
    dc_iop = DenseClaymoreIop(hpr_circuit)
    print("\nDenseClaymore IOP:")
    TableRow(dc_iop, F, Gpairing, Gguo, lambd, s, rho)
    sc_iop = SparseClaymoreIop(hpr_circuit)
    print("\nSparseClaymore IOP:")
    TableRow(sc_iop, F, Gpairing, Gguo, lambd, s, rho)
    print("\n")

    # r1cs
    print("R1CS ...")
    r1cs_circuit = R1csSystem(copy(hpr_circuit))
    print("Have R1CS circuit with ", r1cs_circuit.GetNonzeroElementCount(), " nonzero elements in A, B, or C, and ", r1cs_circuit.GetMultiplicationCount(), " multiplicative relations.")
    marlin_iop = MarlinIop(r1cs_circuit)
    print("\nMarlin IOP:")
    TableRow(marlin_iop, F, Gpairing, Gguo, lambd, s, rho)
    print("\n")

    # hpr, again
    print("HPR ...")
    hpr_circuit.ReduceMaxFanIn(M)
    hpr_circuit.ReduceMaxColWeight(M)
    print("After weight reduction to M=3, wave HPR circuit with ", hpr_circuit.GetLinearRelationCount(), " linear relations and ", hpr_circuit.GetMultiplicationCount(), " multiplications.")
    sonic_iop = SonicIop(hpr_circuit, M)
    print("\nSonic IOP:")
    TableRow(sonic_iop, F, Gpairing, Gguo, lambd, s, rho)
    print("\n")

    # complete timing info
    tock = time.time()
    print("Comparison took ", (tock - tick), " seconds.")
