
load("main.sage")

p = 3
e = 1 # absolutely unramified, at the moment
f = 4

# this is an unramified ext of Z_p with inertia = f, theta generates the residue extension
O_K.<theta> = Zq(p^f, prec = 15, print_mode = 'val-unit');

# I want theta to generate the residue field
if valuation(theta) > 0:
    theta = O_K(1)

#O_K.<theta> = Zp(p, prec = 15, print_mode = 'val-unit')
pi = O_K.uniformizer()                 
pi2 = O_K.uniformizer_pow(2)               
pi3 = O_K.uniformizer_pow(3)

assert(valuation(pi) == 1)

# [P-adic rings memo]
#   O_K.zeta(opt_n)      - generator of the group of roots of 1, or an n-th root of 1
#   O_K.zeta_order(x)    - multiplicative order at z
#   O_K.prime()
#   O_K.frobenius_endomorphism()
#   O_K.residue_field()  - or residue_class_field()
#   O_K.teichmuller(x)
#   O_K.precision_cap()
#
#   x.add_bigoh(prec)      - reduces the precision of x
#   x.is_zero(prec)        - if is zero up to some prec
#   x.precision_absolute() - we know x up to pi^i
#   x.precision_relative() - we know the unit part of x up to pi^i
#   x.list()               - power series in some simple reps
#   x.teichmuller_list()   - power series in teichmuller reps
#   x.unit_part()          - x divided by some pi^k
#   x.val_unit()           - valuation and unit part


k_K = O_K.residue_field()

# test local residue class
assert(local_residue_class(theta) == k_K.gen())
print("Local residue class: PASSED")

# we will work with polynomials in x,y over O_K
O_K_x.<x> = PolynomialRing(O_K);
k_K_x.<kx> = PolynomialRing(k_K);