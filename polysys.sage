def PolySys_Lift(polysys, ring):
    sys = []
    x = ring.gens()[0]
    for p in polysys:
        try:
            sys += [ring(p)]
        except:
            try:
                coeffs = p.coefficients(sparse=False)
            except:
                coeffs = p.coefficients()
            sys += [sum(coeffs[i] * x^i for i in range(len(coeffs)))]
    return sys

def PolySys_AddVars(polysys, numvars):
    Fx = polysys[0].parent()
    F = Fx.base_ring()
    n = len(list(Fx.gens()))

    new_ring = PolynomialRing(F, n+numvars, "x")
    variables = list(new_ring.gens())
    sys = PolySys_Lift(polysys, new_ring)
    return sys, variables[-numvars:]

def PolySys_Eval(polysys, point):
    return [p(point) for p in polysys]

def PolySys_Uniformize(polysys):
    ring = polysys[0].parent()
    for i in range(1, len(polysys)):
        if len(list(ring.gens())) < len(list(polysys[i].parent().gens())):
            ring = polysys[i].parent()
    return PolySys_Lift(polysys, ring)

def PolySys_ActiveVars(polysys):
    variables = list(polysys[0].parent().gens())
    active_variables = [False] * len(variables)
    for p in polysys:
        for k, v in p.dict().items():
            for i in range(len(k)):
                if k[i] != 0:
                    active_variables[i] = True
    return [variables[i] for i in range(len(variables)) if active_variables[i]]

def PolySys_Subs(polysys, new_vars):
    Fx = polysys[0].parent()
    F = Fx.parent()
    old_vars = PolySys_ActiveVars(polysys)
    assert len(old_vars) == len(new_vars), "In PolySys_Subs, number of old variables must be equal to number of new variables"
    book = dict()
    for i in range(len(new_vars)):
        book[old_vars[i]] = new_vars[i]
    return [p.subs(book) for p in polysys]

def PolySys_Shift(polysys, shamt):
    Fx = polysys[0].parent()
    F = Fx.base_ring()
    num_variables = len(list(Fx.gens()))
    new_ring = PolynomialRing(F, num_variables+shamt, "x")
    new_variables = list(new_ring.gens())
    book = dict()
    for i in range(num_variables):
        book[new_variables[i]] = new_variables[i+shamt]
    sys = [new_ring(p).subs(book) for p in polysys]
    return sys

def PolySys_MakeQuadratic(polysys, trace):
    # find first active cubic or higher-order monomial
    ring = polysys[0].parent()
    monomial = ring(0)
    for p in polysys:
        if monomial != ring(0):
            break
        for m in p.monomials():
            if m.degree() >= 3:
                monomial = m
                break
    if monomial == ring(0):
        return polysys, trace # already quadratic

    # choose quadratic factor
    k = list(monomial.exponents()[0])
    for i in range(len(k)):
        if k[i] != 0:
            break
    k_ = copy(k)
    k_[i] -= 1
    for j in range(len(k)):
        if k_[j] != 0:
            break

    quadratic_monomial = ring.gens()[i] * ring.gens()[j]
    quadratic_value = trace[i] * trace[j]

    # add new variable
    polysys, variables = PolySys_AddVars(polysys, 1)
    new_ring = polysys[0].parent()

    # reduce other equations modulo linearization equation
    linearization_equation = quadratic_monomial - variables[0]
    ideal = Ideal([linearization_equation])
    polysys = [p.reduce(ideal) for p in polysys]

    # adjoin linearization equation, and value of monomial
    polysys += [linearization_equation]
    trace += [quadratic_value]

    return PolySys_MakeQuadratic(polysys, trace)

