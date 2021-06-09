load("CompactFIPS202.sage")
from binascii import hexlify, unhexlify

randomness = bytearray(unhexlify("deadbeef"))

def Random(Fp):
    '''samples random prime field element using a csprng'''
    global randomness
    num_bits = len(bin(Fp.order()))-2
    num_bytes = ceil(num_bits / 8)
    margin = 1
    squeeze = SHAKE256(randomness, 32+num_bytes+margin)
    randomness = squeeze[:32]
    stream = squeeze[32:]
    integer = 0
    for i in range(len(stream)):
        integer += ZZ(stream[i]) * 2^(8*i)
    return Fp(integer)

def MerkleRoot(array, rescue_prime):
    if len(array) == 1:
        return array[0]
    halfway = ceil(len(array)/2)
    left_half = array[:halfway]
    left_root = MerkleRoot(left_half, rescue_prime)
    right_half = array[halfway:]
    right_root = MerkleRoot(right_half, rescue_prime)
    return rescue_prime.rescue_prime_hash([left_root, right_root])[0]

def MerklePath(array, index, rescue_prime):
    assert index in range(len(array)), "cannot generate merkle path for an element not in the array; %i not in range(%i)" % (index, len(array))
    if len(array) == 1:
        return []
    if len(array) == 2:
        if index == 0:
            return [array[1]]
        elif index == 1:
            return [array[0]]
    halfway = ceil(len(array)/2)
    left_half = array[:halfway]
    right_half = array[halfway:]
    left_root = MerkleRoot(left_half, rescue_prime)
    right_root = MerkleRoot(right_half, rescue_prime)
    if index < halfway:
        return MerklePath(left_half, index, rescue_prime) + [right_root]
    else:
        return MerklePath(right_half, index-halfway, rescue_prime) + [left_root]

def MerkleVerify(index, element, root, path, rescue_prime):
    current_hash = element
    bit_string = bin(index)[2:]
    assert len(path) >= len(bit_string), "length of path must match bit length of index, but lengths are %i and %i respectively" % (len(path), len(bit_string))
    while len(bit_string) < len(path):
        bit_string = "0" + bit_string
    bit_string = list(reversed(bit_string))
    for i in range(len(bit_string)):
        if bit_string[i] == "1":
            current_hash = rescue_prime.rescue_prime_hash([path[i], current_hash])[0]
        elif bit_string[i] == "0":
            current_hash = rescue_prime.rescue_prime_hash([current_hash, path[i]])[0]
        else:
            print("bit_string[i]:", bit_string[i])

    return current_hash == root

def MerkleTest():
    p = 5*2^127 + 1
    Fp = FiniteField(p)
    load("rescue_prime.sage")
    rescue_prime = RescuePrime(p, 3, 2, 128)
    N = 32
    array = [Random(Fp) for i in range(N)]
    root = MerkleRoot(array, rescue_prime)
    for i in range(N):
        path = MerklePath(array, i, rescue_prime)
        assert True == MerkleVerify(i, array[i], root, path, rescue_prime), "valid Merkle path verification failed"
        j = (i+ZZ(Integers(N-1).random_element())+1) % N # random other number from [0:N)
        assert False == MerkleVerify(j, array[j], root, path, rescue_prime), "invalid Merkle path verification succeeded"
        assert False == MerkleVerify(j, array[i], root, path, rescue_prime), "invalid Merkle path verification succeeded"
    print("Merkle Test success. \\o/")
    return True

