import numpy as np
from common import ck, write_result
checks=[]
psi=lambda K: float(K[0,1])
K=np.array([[.8,.2],[.4,.6]])
Jalpha=np.array([[.3,.7],[.4,.6]])
JU=np.array([[.9,.1],[.4,.6]])
A={'baseline':K,'alpha_cut':Jalpha,'U_cut':JU}
B={'baseline':K.copy(),'alpha_alt':Jalpha.copy(),'U_alt':JU.copy()}
typeA={'alpha_cut':'alpha','U_cut':'U'}; typeB={'alpha_alt':'alpha','U_alt':'U'}
phi={'alpha_cut':'alpha_alt','U_cut':'U_alt'}
for lab in phi:
    matched_kernel=np.allclose(A[lab],B[phi[lab]])
    matched_type=typeA[lab]==typeB[phi[lab]]
    statA=abs(psi(K)-psi(A[lab]))>0; statB=abs(psi(K)-psi(B[phi[lab]]))>0
    ck(checks,f'good_typed_matching_{lab}',matched_kernel and matched_type and statA==statB)
Jdup=Jalpha.copy()
indexed=[('alpha_cut',Jalpha),('alpha_cut_duplicate',Jdup)]
ck(checks,'indexed_family_preserves_duplicate_labels',len(indexed)==2 and np.allclose(indexed[0][1],indexed[1][1]))
kernel_bytes={arr.tobytes() for _,arr in indexed}
ck(checks,'set_signature_would_collapse_duplicate_kernels',len(kernel_bytes)==1 and len(indexed)==2)
Bbad={'baseline':K.copy(),'alpha_alt':JU.copy(),'U_alt':Jalpha.copy()}
bad_phi={'alpha_cut':'U_alt','U_cut':'alpha_alt'}
bad_types={'alpha_alt':'alpha','U_alt':'U'}
all_kernel_match=all(np.allclose(A[l],Bbad[bad_phi[l]]) for l in bad_phi)
type_preserving=all(typeA[l]==bad_types[bad_phi[l]] for l in bad_phi)
ck(checks,'equal_kernels_do_not_override_type_grammar',all_kernel_match and not type_preserving)
family1=['alpha_cut','U_cut']; family2=['alpha_alt']
ck(checks,'non_bijective_family_rejected',len(family1)!=len(family2))
M1={'base':K,'J1':Jalpha,'J2':JU}
M2={'base':K.copy(),'J1':Jalpha.copy(),'J2':K.copy()}
partial_equal=np.allclose(M1['base'],M2['base']) and np.allclose(M1['J1'],M2['J1'])
full_equal=partial_equal and np.allclose(M1['J2'],M2['J2'])
status1=abs(psi(K)-psi(M1['J2']))>0; status2=abs(psi(K)-psi(M2['J2']))>0
ck(checks,'partial_signature_equal',partial_equal and not full_equal)
ck(checks,'omitted_label_changes_pr_status',status1!=status2)
effects=[abs(psi(K)-psi(J)) for J in [Jalpha,JU,K]]
predeclared_all=all(e>0 for e in effects)
posthoc=[e for e in effects if e>0]
ck(checks,'posthoc_family_selection_attack',not predeclared_all and all(e>0 for e in posthoc))
write_result('23','Indexed typed intervention-family signature equivalence and omissions',checks,{'effects':effects})
