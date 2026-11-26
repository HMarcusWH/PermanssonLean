"""Exact arithmetic audit for selected published inequalities and table sums.
No external packages required. Run without Python -O (assertions are checks).
"""
from fractions import Fraction as Q

K = 3 * 2**56
# 1 + ln K < 59 < 64 and K > 2**56 imply sqrt((1+ln K)/K) < 2**-25.
E_upper = Q(6, 2**24) + Q(360, 2**30) + Q(450, 64**20) + Q(16600, K) + Q(600, 2**25)
E_paper = 2 * Q(1, 2**21) + Q(1, 2**111) + Q(1, 2**43) + Q(1, 2**15)
assert E_upper < E_paper < Q(1, 2**14) < Q(1, 3000)
assert Q(297, 400) < 1
assert Q(1, 3000) - Q(1, 2**14) == Q(1673, 6144000)
assert Q(-366815683, 2**40) < -Q(1, 3000)
assert Q(-367371220, 2**40) < -Q(1, 3000)
print('Reduction error rational upper bound:', E_upper, float(E_upper))

# Tables 4, 5, 6(A), 6(B), and 7: independently sum all 46 displayed
# final numerical columns. This does not check each precursor bound.
rows = [(-666,162,147,-357),(-666,52,147,-467),(-800,217,147,-436),(-800,136,147,-517),(-800,544,147,-109),(-666,68,136,-462),(-666,131,136,-399),(-860,373,90,-397),(-369,33,88,-248),(-369,213,98,-58),(-463,237,101,-125),(-592,432,108,-52),(-1043,554,136,-353),(-739,366,196,-177),(-739,326,272,-141),(-747,460,93,-194),(-522,385,93,-44),(-829,574,186,-69),(-369,193,93,-83),(-700,68,136,-496),(-700,411,136,-153),(-700,547,114,-39),(-762,554,136,-72),(-700,521,136,-43),(-700,544,114,-42),(-762,588,136,-38),(-778,15+549,92,-122),(-700,43+486,98,-73),(-700,71+454,102,-73),(-720,101+444,106,-69),(-762,155+432,114,-61),(-762,200+377,136,-49),(-400,68,136,-196),(-400,0,136,-264),(-580,121,96,-363),(-400,48,136,-216),(-580,179,104,-297),(-580,179,96,-305),(-800,614,95,-91),(-400,0,136,-264),(-580,108,96,-376),(-400,249,114,-37),(-400,104,136,-160),(-580,123,104,-353),(-800,518,95,-187),(-580,433,104,-43)]
double_units = {13,14,17}
for i, (g,h,e,s) in enumerate(rows):
    assert g+h+e == s
    assert Q(s, 200000 if i in double_units else 100000) < -Q(1,3000)
print('Final table sums verified:',len(rows))

# Endpoint error, p. 33, Lemma 5.4, 2(c), second left-fiber bullet.
z = Q(21,20)
f = (4*z+1)/5
c2 = f*z
d = c2-z
a1, a2 = 2-c2/f, c2/f
lam = f/128 * (1+4*d)
assert 0 < d <= Q(1,16) and a1 < z == a2
assert lam == Q(949,100000) > 0 > -3*f/512 == -Q(39,6400)
# At u_M=0, K'_kink(z^-) = 0 and the smooth derivative cancels.
# Thus h_tilde'(0+) = lambda, contradicting the literal negative estimate.
print('Boundary derivative counterexample:',lam,'>',-3*f/512)
