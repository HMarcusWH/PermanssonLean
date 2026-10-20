"""Independent Fraction regression for native physical-world occupation."""
from fractions import Fraction as Q
import unittest
from itertools import product
S=tuple(product(range(3),(False,True)))
START=(0,False)
def step(s,a):return ((s[0]+1)%3,bool(a))
def phase(s):return s[0]!=2
def blind(f):return lambda s:f[int(s[1])]
def orbit(policy):
    visited={};seen=[];x=START
    while x not in visited:
        visited[x]=len(seen);seen.append(x)
        x=step(x,policy(x))
    return seen[:visited[x]],seen[visited[x]:]
def score(c):
    m=sum(Q(x[1]) for x in c)/len(c)
    return Q(1)-abs(m-Q(2,3))
class Checks(unittest.TestCase):
    def test_native_phase_cycle(self):
        transient,cycle=orbit(phase)
        self.assertEqual(transient,[])
        self.assertEqual(cycle,[(0,False),(1,True),(2,True)])
        self.assertEqual(score(cycle),Q(1))
    def test_four_deterministic_blind_policies(self):
        values={}
        for f in product((False,True),repeat=2):
            tr,cl=orbit(blind(f))
            values[f]=score(cl)
        self.assertEqual(values,{(False,False):Q(1,3),
             (False,True):Q(1,3),(True,False):Q(5,6),(True,True):Q(2,3)})
    def test_class_average_not_barycenter(self):
        F=lambda p:Q(1)-abs(p-Q(2,3))
        self.assertEqual((F(Q(0))+F(Q(1)))/2,Q(1,2))
        self.assertEqual(F(Q(1,2)),Q(5,6))
    def test_randomized_tie(self):
        self.assertEqual(Q(1)-abs(Q(2,3)-Q(2,3)),Q(1))
    def test_no_joint_state_physical_world_reencoding(self):
        self.assertEqual(len(S),6)
        self.assertEqual(len({x for _,x in S}),2)
if __name__=="__main__":unittest.main()
