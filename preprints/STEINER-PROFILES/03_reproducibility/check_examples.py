"""Finite arithmetic checks for the illustrations and proof transcription."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb

def check():
    cases = [(3,18),(4,32),(5,50)]
    for q,n in cases:
        den=q*(q-1)*(n-q)*(n-q-1)
        u=[F(q*(q-1)*n*n-q*(7*q-9)*n+4*(3*q*q-5*q+1),den),
           -F((q-2)*(q*n-4*q+2),den), F(2*(q-2),q*(n-q)*(n-q-1))]
        s=[1,F(q-2,n-2),F((q-2)*(q-3),(n-2)*(n-3))]
        edges=[set(e) for e in combinations(range(n),2)]
        for j,h in enumerate([{0,1},{0,2},{2,3}]):
            assert sum(s[2-len(e & {0,1})]*u[2-len(e & h)] for e in edges)==int(j==0)
        assert abs(u[0])+2*(n-2)*abs(u[1])+comb(n-2,2)*abs(u[2])<=4
    # Four groups over F_5. The switch moves the blocks and fixes the colors.
    red = {(group, 0) for group in range(3)}
    covered = Counter(((i, x), (j, y)) for i, j in combinations(range(4), 2)
                      for x, y in product(range(5), repeat=2))
    for switch, expected in ((False, [12, 12, 0, 1, 0]), (True, [13, 9, 3, 0, 0])):
        pairs = Counter()
        histogram = Counter()
        for x, y in product(range(5), repeat=2):
            block = [(group, (x + group * y) % 5) for group in range(4)]
            if switch and x in (0, 1):
                block[0] = (0, 1 - x)
            pairs.update(combinations(block, 2))
            histogram[len(red.intersection(block))] += 1
        assert pairs == covered
        assert [histogram[i] for i in range(5)] == expected
    for q,den in ((3,57),(4,163),(5,353)):
        r=comb(q,2);z=F(1,den);a=(2*q-1)*z
        assert (4*r-1)*a+2*z==1
    for x,y in ((0,0),(F(1,6),0),(F(1,8),F(1,8)),(0,F(1,6)),(F(1,16),F(1,16)),(F(1,32),F(1,32))):
        v=(x,F(1,2)-3*x-y,3*(x+y),F(1,2)-x-3*y,y)
        assert min(v)>=0 and sum(v)==1
        assert sum(i*t for i,t in enumerate(v))==2
        assert sum(comb(i,2)*t for i,t in enumerate(v))==F(3,2)
    for r in (3,4,6):
        for ds in product((F(1,3),F(1),F(3)),repeat=r):
            x=[d-1 for d in ds]
            assert sum(t*t for t in x)-2*sum(x)**2 <= (2*r-1)*sum(t*t/d for t,d in zip(x,ds))
    print('PASS exact Johnson products, norm samples, four-point trade, exponents, profile slice and signed energy samples')

if __name__=='__main__':check()
