"""C10 executable exact-Fraction arithmetic and independent-checker adversaries.

The reference producer and separate Python checker are deliberately not
considered Lean verification of the numerical/path-law correspondence.
"""
import copy
import itertools
import json
import unittest
from fractions import Fraction as F
from c10_exact_execution import InputError, checked_matrix, check_input, execute, bottom_classes, transitive_reach, class_values
from c10_verify_receipt import ReceiptError, verify_receipt

Q=F(0)
BASE=[['0','1','0','0','0','0'],
      ['0','1/2','1/6','0','1/3','0'],
      ['0','0','0','1','0','0'],
      ['0','0','1','0','0','0'],
      ['0','0','0','0','1/2','1/2'],
      ['0','0','0','0','1/4','3/4']]
OBS=[False,False,True,True,True,True]

def matrix_with_edits(edits):
    m=copy.deepcopy(BASE)
    for i,row in edits.items():
        m[i]=list(row)
    return m

FULL=matrix_with_edits({1:['0','1','0','0','0','0'],2:['0','1','0','0','0','0']})
UONLY=matrix_with_edits({1:['0','1','0','0','0','0']})
BONLY=matrix_with_edits({1:['0','0','0','0','1','0'],2:['0','0','0','0','1','0']})

def SOFT(p):
    p=F(p)
    return matrix_with_edits({1:['0','1','0','0','0','0'],2:['0',str(p),'0','0',str(1-p),'0']})

HALF=SOFT(F(1,2))
TINY=SOFT(F(1,1000))
TINY35=SOFT(F(1,10**35))

def inp(members,base=BASE,descriptor=OBS,comparison=(1,2)):
    return {'n':len(base),'baseline':copy.deepcopy(base),'descriptor':list(descriptor),
            'comparison':list(comparison),
            'menu':[{'id':n,'matrix':copy.deepcopy(m)} for n,m in members]}


def receipt_of(raw):
    return execute(check_input(raw))


class C10FixedCases(unittest.TestCase):
    def test_001_original_menu(self):
        r=receipt_of(inp([('full',FULL),('half',HALF),('tiny',TINY)]))
        self.assertTrue(verify_receipt(r))
        self.assertEqual([x['margin'] for x in r['members']],['1','1/2','1/1000'])
        self.assertEqual((r['selected'],r['optimum']),('full','1'))
    def test_002_identity_only(self):
        r=receipt_of(inp([('identity',BASE)]));self.assertTrue(verify_receipt(r))
        self.assertEqual(r['numerical_status'],'LISTED_NO_UNIFORM_PR_BY_ZERO_MARGIN')
    def test_003_one_row(self):
        r=receipt_of(inp([('u',UONLY)]));self.assertTrue(verify_receipt(r))
        self.assertEqual(r['members'][0]['effects'],['1','0'])
        self.assertEqual(r['members'][0]['worst_start'],2)
    def test_004_b_only(self):
        r=receipt_of(inp([('b',BONLY)]));self.assertTrue(verify_receipt(r))
        self.assertEqual(r['members'][0]['margin'],'0')
    def test_005_half_tiny_same_support(self):
        m=tuple(tuple(F(x) for x in row) for row in HALF)
        t=tuple(tuple(F(x) for x in row) for row in TINY)
        self.assertEqual(transitive_reach(m),transitive_reach(t))
        r=receipt_of(inp([('half',HALF),('tiny',TINY)]))
        self.assertEqual([x['margin'] for x in r['members']],['1/2','1/1000'])
    def test_006_tiny35(self):
        r=receipt_of(inp([('tiny35',TINY35)]));self.assertTrue(verify_receipt(r))
        self.assertEqual(r['members'][0]['margin'],'1/100000000000000000000000000000000000')
    def test_007_d0_reverse_ranking(self):
        self.assertGreater(F(TINY[2][4]),F(HALF[2][4]))
        self.assertGreater(F('1/2'),F('1/1000'))
    def test_008_all_recurrent_identity(self):
        r=receipt_of(inp([('identity',[['1','0'],['0','1']])],base=[['1','0'],['0','1']],descriptor=[True,False],comparison=[0,1]))
        self.assertTrue(verify_receipt(r));self.assertEqual(r['baseline']['classes'],[[0],[1]])
    def test_009_period_two_mixed(self):
        mat=[['0','1'],['1','0']]
        r=receipt_of(inp([('identity',mat)],base=mat,descriptor=[True,False],comparison=[0,1]))
        self.assertTrue(verify_receipt(r));self.assertEqual(r['baseline']['event'],['0','0'])
    def test_010_period_two_all_true(self):
        mat=[['0','1'],['1','0']]
        r=receipt_of(inp([('identity',mat)],base=mat,descriptor=[True,True],comparison=[0,1]))
        self.assertTrue(verify_receipt(r));self.assertEqual(r['baseline']['event'],['1','1'])
    def test_011_transient_false(self):
        mat=[['0','1'],['0','1']]
        r=receipt_of(inp([('identity',mat)],base=mat,descriptor=[False,True],comparison=[0,1]))
        self.assertTrue(verify_receipt(r));self.assertEqual(r['baseline']['event'],['1','1'])
    def test_012_n1(self):
        self.assertTrue(verify_receipt(receipt_of(inp([('x',[['1']])],base=[['1']],descriptor=[False],comparison=[0]))))
    def test_013_n0_rejected(self):
        with self.assertRaises(InputError):check_input(inp([('x',[])],base=[],descriptor=[],comparison=[]))
    def test_014_empty_menu(self):
        with self.assertRaises(InputError):check_input(inp([]))
    def test_015_empty_comparison(self):
        with self.assertRaises(InputError):check_input(inp([('x',BASE)],comparison=[]))
    def test_016_bad_comparison(self):
        with self.assertRaises(InputError):check_input(inp([('x',BASE)],comparison=[6]))
    def test_017_comparison_bool(self):
        with self.assertRaises(InputError):check_input(inp([('x',BASE)],comparison=[True]))
    def test_018_comparison_dedup(self):
        r=receipt_of(inp([('x',BASE)],comparison=[2,1,2,1]))
        self.assertEqual(r['normalized_input']['comparison'],[1,2])
    def test_019_duplicate_same_id(self):
        r=receipt_of(inp([('x',HALF),('x',HALF)]))
        self.assertEqual(len(r['members']),1)
    def test_020_duplicate_conflict(self):
        with self.assertRaises(InputError):check_input(inp([('x',HALF),('x',TINY)]))
    def test_021_distinct_same_kernel(self):
        r=receipt_of(inp([('a',HALF),('b',HALF)]))
        self.assertEqual(r['ties'],['a','b'])
    def test_022_tie_first_order(self):
        r=receipt_of(inp([('b',HALF),('a',HALF)]))
        self.assertEqual(r['selected'],'b')
    def test_023_matrix_rows_wrong(self):
        with self.assertRaises(InputError):check_input(inp([('x',BASE[:-1])]))
    def test_024_matrix_not_stochastic(self):
        bad=copy.deepcopy(BASE);bad[0][1]='1/2'
        with self.assertRaises(InputError):check_input(inp([('x',bad)]))
    def test_025_float_rejected(self):
        bad=copy.deepcopy(BASE);bad[0][1]=1.0
        with self.assertRaises(InputError):check_input(inp([('x',bad)]))
    def test_026_negative_prob(self):
        bad=copy.deepcopy(BASE);bad[0][0]='-1'
        with self.assertRaises(InputError):check_input(inp([('x',bad)]))
    def test_027_noncanonical_prob(self):
        bad=copy.deepcopy(BASE);bad[1][1]='2/4'
        with self.assertRaises(InputError):check_input(inp([('x',bad)]))
    def test_028_nonnumeric_prob(self):
        bad=copy.deepcopy(BASE);bad[1][1]='nan'
        with self.assertRaises(InputError):check_input(inp([('x',bad)]))
    def test_029_zero_denominator(self):
        bad=copy.deepcopy(BASE);bad[1][1]='1/0'
        with self.assertRaises(InputError):check_input(inp([('x',bad)]))
    def test_030_wrong_descriptor(self):
        with self.assertRaises(InputError):check_input(inp([('x',BASE)],descriptor=[False]))
    def test_031_bad_descriptor_types(self):
        with self.assertRaises(InputError):check_input(inp([('x',BASE)],descriptor=[0]*6))
    def test_032_undeclared_extra_keys(self):
        bad=inp([('x',BASE)]);bad['custom_basis']='overwrite'
        with self.assertRaises(InputError):check_input(bad)
    def test_033_matched_baseline_path(self):
        r=receipt_of(inp([('full',FULL)]))
        self.assertEqual([r['baseline']['event'][i] for i in (1,2)],['1','1'])
    def test_034_baseline_transient_t(self):
        r=receipt_of(inp([('full',FULL)]));self.assertEqual(r['baseline']['event'][0],'1')
    def test_035_initial_bad_class_full(self):
        r=receipt_of(inp([('full',FULL)]));self.assertIn([1],r['members'][0]['geometry']['classes'])
    def test_036_wrong_B1_minimizer(self):
        r=receipt_of(inp([('one',UONLY)]));self.assertEqual(r['members'][0]['worst_start'],2)
    def test_037_change_B1_changes_valid_numerical_query(self):
        r=receipt_of(inp([('one',UONLY)],comparison=[1]));self.assertEqual(r['members'][0]['margin'],'1')
        # Numeric query is valid but a singleton set cannot be silently identified with original C6 B1.
    def test_038_wrong_optimum_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['optimum']='1/2'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_039_wrong_first_tie_rejected(self):
        r=receipt_of(inp([('a',HALF),('b',HALF)]));r['selected']='b'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_040_wrong_tie_set_rejected(self):
        r=receipt_of(inp([('a',HALF),('b',HALF)]));r['ties']=['b']
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_041_wrong_B1_effect_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['members'][0]['effects'][0]='0'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_042_wrong_class_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['members'][0]['geometry']['classes']=[[1]]
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_043_wrong_boundary_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['members'][0]['geometry']['absorption'][0][1]='0'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_044_wrong_harmonic_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['baseline']['absorption'][0][1]='0'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_045_wrong_status_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['numerical_status']='CERTIFIED_PR'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_046_wrong_input_sha_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['input_sha256']='f'*64
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_047_wrong_input_metadata_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['normalized_input']['comparison']=[1]
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_048_wrong_label_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['members'][0]['geometry']['good'][0]=True
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_049_wrong_event_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['members'][0]['geometry']['event'][1]='1'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_050_renamed_member_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['members'][0]['id']='fake'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_051_repeated_missing_class_rejected(self):
        r=receipt_of(inp([('full',FULL)]));r['baseline']['classes']=r['baseline']['classes'][:-1]
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_052_wrong_worst_rejected(self):
        r=receipt_of(inp([('half',HALF)]));r['members'][0]['worst_start']=0
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_053_wrong_geometry_bad_label(self):
        r=receipt_of(inp([('half',HALF)]));r['members'][0]['geometry']['good']=[True]
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_054_multiple_negative_menu(self):
        r=receipt_of(inp([('id',BASE),('u',UONLY)]));self.assertTrue(verify_receipt(r))
        self.assertEqual(r['optimum'],'0')
    def test_055_complementary_partial_interventions(self):
        # Both choices help one state only; selection may not depend on x.
        rev=matrix_with_edits({2:['1','0','0','0','0','0']})
        # a0->t->u and u baseline -> eventual good; this does not change u.
        r=receipt_of(inp([('u',UONLY),('other',rev)]));self.assertTrue(verify_receipt(r))
        self.assertEqual(r['selected'],'u')
    def test_056_sorted_baseline_classes(self):
        r=receipt_of(inp([('full',FULL)]));self.assertEqual(r['baseline']['classes'],[[2,3],[4,5]])
    def test_057_3cycle_mixed(self):
        m=[['0','1','0'],['0','0','1'],['1','0','0']]
        r=receipt_of(inp([('same',m)],base=m,descriptor=[True,True,False],comparison=[0,1,2]))
        self.assertTrue(verify_receipt(r));self.assertEqual(r['baseline']['event'],['0']*3)
    def test_058_3cycle_all_true(self):
        m=[['0','1','0'],['0','0','1'],['1','0','0']]
        r=receipt_of(inp([('same',m)],base=m,descriptor=[True]*3,comparison=[0,1,2]))
        self.assertTrue(verify_receipt(r));self.assertEqual(r['baseline']['event'],['1']*3)
    def test_059_two_absorbers_split(self):
        m=[['0','1/2','1/2'],['0','1','0'],['0','0','1']]
        r=receipt_of(inp([('same',m)],base=m,descriptor=[False,True,False],comparison=[0,1]))
        self.assertTrue(verify_receipt(r));self.assertEqual(r['baseline']['event'],['1/2','1','0'])
    def test_060_concurrent_transient_cycles(self):
        m=[['1/3','1/3','1/3'],['1/3','1/3','1/3'],['0','0','1']]
        r=receipt_of(inp([('same',m)],base=m,descriptor=[True,False,True],comparison=[0,1]))
        self.assertTrue(verify_receipt(r));self.assertEqual(r['baseline']['event'],['1']*3)
    def test_061_strict_noncanonical_zero(self):
        bad=copy.deepcopy(BASE);bad[1][0]='-0'
        with self.assertRaises(InputError):check_input(inp([('x',bad)]))
    def test_062_signed_plus_rejected(self):
        bad=copy.deepcopy(BASE);bad[1][0]='+0'
        with self.assertRaises(InputError):check_input(inp([('x',bad)]))
    def test_063_string_bool_rejected(self):
        with self.assertRaises(InputError):check_input(inp([('x',BASE)],descriptor=['true']*6))
    def test_064_id_whitespace(self):
        with self.assertRaises(InputError):check_input(inp([(' x',BASE)]))
    def test_065_n_bool(self):
        r=inp([('x',BASE)]);r['n']=True
        with self.assertRaises(InputError):check_input(r)
    def test_066_out_of_range_neg(self):
        with self.assertRaises(InputError):check_input(inp([('x',BASE)],comparison=[-1]))
    def test_067_unknown_input_key(self):
        r=inp([('x',BASE)]);r['target']='posthoc'
        with self.assertRaises(InputError):check_input(r)
    def test_068_corrupt_absorption_fraction(self):
        r=receipt_of(inp([('full',FULL)]));r['baseline']['absorption'][0][1]='2/4'
        with self.assertRaises((ReceiptError,InputError)):verify_receipt(r)
    def test_069_wrong_claim_boundary(self):
        r=receipt_of(inp([('full',FULL)]));r['claim_boundary']='Lean proved everything'
        with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_070_zero_edge_vs_tiny_edge(self):
        eps=F(1,10**35)
        a=tuple(tuple(F(x) for x in row) for row in TINY35)
        self.assertGreater(a[2][1],0)
        self.assertEqual(F(HALF[2][1]),F(1,2))

# Distinct exact finite matrix instances; the result is independently checked for
# each, not a repeated invocation of an identical fixture.

def add_generated_case(name, base, labels):
    def test(self):
        instance=inp([('identity',base)],base=base,descriptor=labels,comparison=list(range(len(base))))
        r=receipt_of(instance)
        self.assertTrue(verify_receipt(r))
        self.assertEqual(r['optimum'],'0')
        self.assertEqual(len(r['baseline']['event']),len(base))
    setattr(C10FixedCases, name, test)

# 64 two-state stochastic chains, each with distinct probabilities/labels.
values=(F(0),F(1,3),F(1,2),F(1))
for ix,(a,b) in enumerate(itertools.product(values,repeat=2)):
    base=[[str(a),str(1-a)],[str(b),str(1-b)]]
    for mask in range(4):
        add_generated_case(f'test_1{ix:02d}_{mask}_two_state_exact',base,[bool(mask&1),bool(mask&2)])

# 27 distinct three-state deterministic machines, with one frozen mixed
# descriptor per machine to exercise SCC closure/periodicity asymmetry.
for ix,targets in enumerate(itertools.product(range(3),repeat=3)):
    base=[[('1' if j==targets[i] else '0') for j in range(3)] for i in range(3)]
    add_generated_case(f'test_2{ix:02d}_three_state_deterministic',base,[True,False,True])

if __name__=='__main__':
    unittest.main()