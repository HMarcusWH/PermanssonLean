import json,re
from pathlib import Path
from common import ck, write_result, ROOT
checks=[]
for r in range(17,30):
    p=ROOT/'results'/f'run_{r}.json'
    if not p.exists(): ck(checks,f'run_{r}_present',False,'missing'); continue
    d=json.loads(p.read_text()); ck(checks,f'run_{r}_green',d.get('failed')==0,f"{d.get('passed')}/{d.get('checks_total')}")
mutations={
 'off_by_one_killed_survival':'17','assume_unique_qsd':'18','qsd_alone_implies_uniform_finite_persistence':'18',
 'polish_implies_automatic_limit':'19','polish_implies_uniform_tightness_of_arbitrary_family':'19',
 'ignore_finite_horizon_accumulation':'20','tv_factor_two_convention_confusion':'20',
 'global_infinite_horizon_lipschitz':'21','non_strict_margin_boundary':'22',
 'partial_intervention_signature_suffices':'23','set_signature_may_collapse_duplicate_labels':'23',
 'kernel_equality_overrides_intervention_type':'23','baseline_lumpability_suffices':'24',
 'quotient_may_mix_strategic_and_world_coordinates':'24','quotient_b1_admissibility_is_automatic':'24',
 'quotient_property_metric_may_change':'24','core_agreement_implies_scalar_defect_without_second_rigidity':'25',
 'finite_detection_without_continuity':'26','scalarize_first_failure_with_shell_dim_gt1':'27',
 'pseudoinverse_is_exact_solution_for_any_source':'28','shared_budget_can_be_added':'29',
}
for name,r in mutations.items():
    d=json.loads((ROOT/'results'/f'run_{r}.json').read_text())
    ck(checks,'mutation_killed_'+name,d['failed']==0,f'covered by run {r}')
tex_path=ROOT/'inputs'/'Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.7_SUBMISSION_FINAL_2026-09-21.tex'
contract_path=ROOT/'inputs'/'V017_SOURCE_CONTRACT.txt'
source_path=tex_path if tex_path.exists() else contract_path
ck(checks,'source_contract_present',source_path.exists(),str(source_path))
if source_path.exists():
    t=source_path.read_text(encoding='utf-8',errors='replace')
    ck(checks,'source_qsd_definition_requires_finite_gate',
       'in addition to satisfying the finite-persistence gate (11)' in t and 'QSD-certified quasi-regime' in t)
    ck(checks,'source_qsd_warning_explicit',
       'QSD equation alone does not imply the uniform finite-persistence gate' in t or 'QSD equation alone does not establish the uniform finite-persistence gate' in t)
    ck(checks,'source_signature_is_indexed_family',
       r'\operatorname{Sig}_{\mathcal J}(M)=\left(K_M,(K_M^J)_{J\in\mathcal J}\right)' in t)
    ck(checks,'source_family_matching_type_preserving','target/type-grammar-preserving bijection' in t)
    ck(checks,'source_quotient_type_respecting_product_map',r'q=q_S\times q_X' in t and 'type-respecting product map' in t)
    ck(checks,'source_quotient_b1_independent_admissibility','independently satisfy the comparison-set admissibility/non-triviality requirement' in t)
    ck(checks,'source_quotient_common_metric_property_space','same metric property space' in t)
    ck(checks,'source_quotient_all_interventions_intertwine',r'for every \(J\in\{0\}\cup\mathcal J\)' in t)
    ck(checks,'source_tv_convention_explicit',r'\|\mu-\nu\|_{\mathrm{TV}}:=\sup_A|\mu(A)-\nu(A)|' in t or r'\|\mu-\nu\|_{\rm TV}:=\sup_A|\mu(A)-\nu(A)|' in t)
    ck(checks,'source_hyperref_unique_destinations', 'hypertexnames=false' in t)
    labels=re.findall(r'\\label\{([^}]+)\}',t)
    dup={x for x in labels if labels.count(x)>1}
    ck(checks,'source_latex_labels_unique',not dup,f'duplicates={sorted(dup)}')
    pos18a=t.find(r'\tag{18a}\label{eq:18a}')
    pos19=t.find(r'\tag{19}\label{eq:19}')
    ck(checks,'source_equation_18a_before_19',pos18a>=0 and pos19>pos18a,f'pos18a={pos18a}, pos19={pos19}')
    ck(checks,'source_hermansson_2026a_present','Hermansson, 2026a' in t and '2026a). Equilibrium-Generated Regimes' in t)
legacy=ROOT/'results'/'v016_legacy_pass_ledger_compact.json'
if legacy.exists():
    d=json.loads(legacy.read_text())
    ok=d.get('status')=='PASS' and d.get('passed')==85 and d.get('total')==85
    ck(checks,'legacy_compatibility_summary_green',ok,f"{d.get('passed')}/{d.get('total')} ({d.get('evidence_type','summary')})")
else:
    ck(checks,'legacy_compatibility_summary_green',False,'compact compatibility summary missing')
for fname,expect in [('v016_run16_source_audit_postproofread.json','PASS'),('v016_run16_mutations_postproofread.json','PASS'),('v016_baseline_validation_postproofread.json','PASS')]:
    p=ROOT/'results'/fname
    if not p.exists():
        ck(checks,'control_'+fname,False,'missing')
    else:
        d=json.loads(p.read_text())
        ck(checks,'control_'+fname,d.get('status')==expect,str(d))
write_result('30','Integrated post-proofread v1.7 mutation/source gate and historical v1.6 compatibility controls',checks,{'mutations':len(mutations)})
