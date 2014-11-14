r"""
Utility functions to "reduce" Eisenstein polynomials, and to obtain the set of
all reduced polynomials.


REFERENCES:

- Monge, Maurizio. "A family of Eisenstein polynomials
  generating totally ramified extensions, identification of extensions and
  construction of class fields." International Journal of Number Theory
  (2014): 1-29.

  
AUTHORS:

- Maurizio Monge (2014-11-14): initial version

"""

def local_residue_class(x):
    v = valuation(x)
    assert(v >= 0)
    k_K = x.parent().residue_field()
    return k_K(0) if v > 0 else k_K(x.list()[0])


def lift_local_residue(x, residue):
    vec = residue.parent().vector_space()(residue)
    #print "LIFT: ", x, vec, residue
    #print x.parent()(vec)
    retv = x.parent()(vec).lift_to_precision(15)
    #print retv
    return retv

########################################################################################
# returns the L-valuation of f(pi)-g(pi), over a uniformizer pi of
# a generic totally ramified ext L/K of degree n
def poly_delta(f, g):
    fcoeffs = f.coeffs()
    gcoeffs = g.coeffs()
    n = f.degree()
    assert(n == g.degree())
    return min(n*valuation(fcoeffs[i] - gcoeffs[i])+i for i in range(n))


########################################################################################
# return true if f is Eisenstein
def is_eisenstein(f):
    coeffs = f.coeffs()
    n      = f.degree()
    return (valuation(coeffs[0]) == 1 
            and valuation(coeffs[n]) == 0
            and all(valuation(coeffs[x]) >= 1 for x in range(1,n)))


########################################################################################
# computes the ordinate of the point with abscissa p^k
# in the polygon of Phi(T) = pi^-n * f(pi + piT)
def ramification_polygon_ordinate(f, k):
    coeffs = f.coeffs()
    n      = f.degree()
    return min(d + n * (valuation(coeffs[d]) + max(valuation(O_K(d)) - k, 0) - 1)
               for d in [1..n])

class RamVertex:
    def __init__(self, r, ordinate, coeff, i):
        self.r        = r         # the degree in x (ie. the abscissa in the polygon)
        self.ordinate = ordinate  # the ordinate in the polygon
        self.coeff    = coeff     # the coeff which is binom(i,r) f_i pi^(i-n) [without the factor pi^(i-n)]
        self.i        = i         # the corresponding i
    def __repr__(self):
        return "(%d,%d){%s}·π^(%d-n)" % (self.r, self.ordinate, self.coeff, self.i)        

class RamData:
    def __init__(self, f, vertices):
        self.f = f
        self.n = f.degree()
        self.f_0 = f.constant_coefficient()
        self.pi = f.parent().base_ring().uniformizer()
        self.eta = -self.f_0 / self.pi
        self.vertices = vertices
    def __repr__(self):
        return "{%s+...,%s}" % (self.eta, self.vertices)


# returns a list of pairs [p^k, ordinate of the ramification polygon at p^k]
def ramification_data(f):
    n      = f.degree()
    coeffs = f.coeffs()
    l      = valuation(n,p)
    retv   = []

    for k in range(0,l+1):
        r = p^k
        ordinate, i = min((d + n * (valuation(coeffs[d]) + max(valuation(O_K(d)) - k, 0) - 1), d) for d in [1..n])
        coeff = coeffs[i]*binomial(i, r)
        retv.append(RamVertex(r, ordinate, coeff, i))
    return RamData(f, retv)


# returns where a deformation pi -> pi+theta p^(m+1) will change something in the coefficients
def deformation_level(ram_data, i):
    n = ram_data.f.degree()
    return min(rd.r*i+rd.ordinate+n for rd in ram_data.vertices)

# the level after which we have total freedom
def compute_final_deformation_level(ram_data):
    n = ram_data.f.degree()
    i = 1
    while true:
        lev,phi_ord = min((rd.r*i + rd.ordinate + n,-rd.r) for rd in ram_data.vertices)
        if phi_ord == -1:
            return lev
        i += 1

# returns the "side polynomial"
def side_polynomial(ram_data, m):
    lev = min(rd.r*m+rd.ordinate for rd in ram_data.vertices)
    verts = [rd for rd in ram_data.vertices if lev == rd.r*m+rd.ordinate]
    retv = O_K_x(0)
    for rd in verts:
        pi_pow = rd.r*m + rd.i - ram_data.n
        assert(lev == (pi_pow + valuation(rd.coeff) * ram_data.n))
        monomial = rd.coeff * (-ram_data.f_0)^int(pi_pow/ram_data.n) * x^rd.r
        retv += monomial
    retv /= (ram_data.pi)^int(lev / ram_data.n)
    return retv.map_coefficients(local_residue_class, k_K)


########################################################################################
# return the "deformed" Eisenstein polynomial, ie. the minimal polynomial
# of the (unique) uniformizer q such that
#    q + theta*q^(m+1) = pi,
# note that we also have that
#    q = pi - theta*pi^(m+1) + O(pi^(m+2))
def poly_deform(f, m, th, truncn):
    n = f.degree()

    # truncation level, because x^trucn = 0 mod piK^prec, as v(x) = 1/n
    g = f(x + th*x^(m+1)).truncate(truncn) # IMPROVE-ME: use f_0 instead of x^n

    prev = (0, n)
    while(g.degree() > n):
        g_coeffs = g.coeffs()

        #where f has terms we want to kick out
        extra_range = range(n+1, g.degree()+1)
        
        cur_prec = min( (valuation(g_coeffs[i])*n + i) for i in extra_range)
        if cur_prec >= truncn:
            break
        
        # lexicographically minimal pair (val(f_i), i), for i in the extra range
        min_val, min_idx = min( (valuation(g_coeffs[i]), i) for i in extra_range)

        # the bad terms should be going away...
        #print prev, (min_val, min_idx)
        #print "Gne"
        #print g_coeffs[min_idx], min_idx
        assert(prev < (min_val, min_idx))
        #print "Gno"
        prev = (min_val, min_idx)

        # enough precision? - WRONG
        ## if min_val*n+min_idx > truncn:
        ##    break

        # subtract, from g, (badmononial/x^n)*g
        g = g - g_coeffs[min_idx] * g.shift(min_idx-n).truncate(truncn)
    return g.truncate(n+1).monic()

# f_ij coefficient
def f_ij(f, lev):
    R = f.parent().base_ring()
    n = f.degree()
    i = lev % n
    f_i = f.coeffs()[i]
    f_i_list = f_i.teichmuller_list()
    #print "TCH", f_i, f_i_list, "ETCH"
    j = int(lev / n) - valuation(f_i)
    #print i,j,f_i,f_i_list
    return R(f_i_list[j]) if j>=0 and j < len(f_i_list) else R(0)

# returns the index of the last nonzero coord in a vector
def last_nonzero(v):
    return max(x for x in range(-1, len(v)) if x < 0 or not v[x].is_zero())

def index_with_last_nonzero(vs):
    if (len(vs)) == 0:
        return (-1,-1)
    return max( (last_nonzero(vs[vidx]),vidx) for vidx in range(len(vs)) )

def reductions(target, gen, deg, add_polynomial):
    elems = [gen^i for i in range(deg)]
    VEC = gen.parent().vector_space()
    Vimgs = [VEC(add_polynomial(e)) for e in elems]
    Eretv = gen.parent()(0)
    #print target
    Vtarget = VEC(local_residue_class(target))
    #print Vtarget

    while true:
        print Vtarget,"|",Vimgs
        (lnz, vidx) = index_with_last_nonzero(Vimgs)
        if lnz < 0:
            break
        Epivot = elems[vidx]
        Vpivot = Vimgs[vidx]
        del elems[vidx]
        del Vimgs[vidx]
        for i in range(len(Vimgs)):
            if not Vimgs[i][lnz].is_zero():
                fact = (Vimgs[i][lnz] / Vpivot[lnz])
                Vimgs[i] -= Vpivot * fact
                elems[i] -= Epivot * fact
        if not Vtarget[lnz].is_zero():
            fact = (Vtarget[lnz] / Vpivot[lnz])
            Vtarget -= Vpivot * fact
            Eretv -= Epivot * fact
    print Eretv, elems
    return lift_local_residue(target, Eretv), elems
#sp = side_polynomial(ram_data, 1)
#Ktheta = local_residue_class(theta)
#KF = Ktheta.parent().vector_space()
#for i in range(0,4):
#    print KF(Ktheta^i),"->",KF(sp(Ktheta^i))

