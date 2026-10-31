"""Permansson application successor: bounded numeric and exact-certificate profiles.

This executable is not an empirical GR/PR identifier or a mathematical release gate.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
from .capabilities import registry
from .errors import AppError
from .package_data import export_resources,export_extended_resources,NAMES
from .runner import execute


def _write_json(path:Path,data):
    path.write_bytes((json.dumps(data,sort_keys=True,indent=2,ensure_ascii=False,allow_nan=False)+'\n').encode('utf-8'))


def _new_output(path:Path):
    from .budget import child_output,in_child
    if in_child():
        # The budgeted child writes into its private staging directory; the
        # parent publishes it at `path` only if every limit held.
        out=child_output()
        out.mkdir(parents=False,exist_ok=False)
        return out
    out=path.absolute()
    if out.exists() or out.is_symlink() or any(p.is_symlink() for p in (out.parent,*out.parent.parents)):
        raise AppError('OUTPUT_SCOPE','output must be new and must not pass through a symlink')
    out.mkdir(parents=True,exist_ok=False)
    return out


# Every exact additive profile command runs under one whole-run budget
# (permansson_app.budget). Native C10/C11 `run` has its own bounded runner;
# lean-emit/lean-recheck are development tools outside the release scope.
BUDGETED_COMMANDS=frozenset({
    'finite-kernel','finite-occupation','finite-exit','lp-propose','lp-check','finite-survival',
    'finite-perturbation','finite-safety','finite-bellman','frozen-menu','finite-residence',
    'nonlinear-stationary','finite-grammar','finite-quotient','finite-adaptive-grammar',
    'finite-robust-nature','finite-private-stage','one-step-risk','one-step-risk-infeasibility',
    'one-step-belief','finite-belief-tree','finite-cq1','finite-cq1-transport','finite-metric',
    'finite-algebra','finite-multiagent'})


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    sub=p.add_subparsers(dest='command',required=True)
    sub.add_parser('capabilities')
    sub.add_parser('about',help='where this permansson_app is imported from, its distribution version and Python')
    resources=sub.add_parser('resources')
    resources.add_argument('--output',type=Path)
    resources.add_argument('--full',action='store_true',help='include versioned finite/LP schemas')
    run=sub.add_parser('run')
    run.add_argument('request',type=Path)
    run.add_argument('--source-root',type=Path,required=True)
    run.add_argument('--output',type=Path,required=True)
    finite=sub.add_parser('finite-kernel')
    finite.add_argument('model',type=Path)
    finite.add_argument('--output',type=Path,required=True)
    survival=sub.add_parser('finite-survival')
    survival.add_argument('comparison',type=Path)
    survival.add_argument('--output',type=Path,required=True)
    perturb=sub.add_parser('finite-perturbation')
    perturb.add_argument('problem',type=Path)
    perturb.add_argument('--output',type=Path,required=True)
    safe=sub.add_parser('finite-safety')
    safe.add_argument('problem',type=Path)
    safe.add_argument('--output',type=Path,required=True)
    nonlinear=sub.add_parser('nonlinear-stationary')
    nonlinear.add_argument('request',type=Path)
    nonlinear.add_argument('--output',type=Path,required=True)
    residence=sub.add_parser('finite-residence')
    residence.add_argument('request',type=Path)
    residence.add_argument('--output',type=Path,required=True)
    tree=sub.add_parser('finite-belief-tree')
    tree.add_argument('request',type=Path)
    tree.add_argument('--output',type=Path,required=True)
    belief=sub.add_parser('one-step-belief')
    belief.add_argument('request',type=Path)
    belief.add_argument('--output',type=Path,required=True)
    risk=sub.add_parser('one-step-risk')
    risk.add_argument('request',type=Path)
    risk.add_argument('--output',type=Path,required=True)
    for name,help_text in (('lean-emit','emit a source-bound Lean candidate for a checked receipt; Lean is not run'),
                           ('lean-recheck','recheck candidate bytes against the original request and receipt')):
        lean=sub.add_parser(name,help=help_text)
        lean.add_argument('--family',required=True)
        lean.add_argument('request',type=Path)
        lean.add_argument('receipt',type=Path,nargs='?')
        lean.add_argument('--region',type=Path)
        if name=='lean-emit':lean.add_argument('--output',type=Path,required=True)
        else:lean.add_argument('--candidate',type=Path,required=True)
    transport=sub.add_parser('finite-cq1-transport')
    transport.add_argument('request',type=Path)
    transport.add_argument('--output',type=Path,required=True)
    infeasible=sub.add_parser('one-step-risk-infeasibility')
    infeasible.add_argument('request',type=Path)
    infeasible.add_argument('--output',type=Path,required=True)
    adaptive=sub.add_parser('finite-adaptive-grammar')
    adaptive.add_argument('request',type=Path)
    adaptive.add_argument('--output',type=Path,required=True)
    private_stage=sub.add_parser('finite-private-stage')
    private_stage.add_argument('request',type=Path)
    private_stage.add_argument('--output',type=Path,required=True)
    multiagent=sub.add_parser('finite-multiagent')
    multiagent.add_argument('request',type=Path)
    multiagent.add_argument('--output',type=Path,required=True)
    algebra=sub.add_parser('finite-algebra')
    algebra.add_argument('request',type=Path)
    algebra.add_argument('--output',type=Path,required=True)
    metric=sub.add_parser('finite-metric')
    metric.add_argument('request',type=Path)
    metric.add_argument('--output',type=Path,required=True)
    cq1=sub.add_parser('finite-cq1')
    cq1.add_argument('request',type=Path)
    cq1.add_argument('--output',type=Path,required=True)
    nature=sub.add_parser('finite-robust-nature')
    nature.add_argument('request',type=Path)
    nature.add_argument('--output',type=Path,required=True)
    for name in ('finite-grammar','finite-quotient'):
        staged=sub.add_parser(name)
        staged.add_argument('request',type=Path)
        staged.add_argument('--output',type=Path,required=True)
    bellman=sub.add_parser('finite-bellman')
    bellman.add_argument('problem',type=Path)
    bellman.add_argument('--output',type=Path,required=True)
    occ=sub.add_parser('finite-occupation')
    occ.add_argument('model',type=Path)
    occ.add_argument('--output',type=Path,required=True)
    exit_cmd=sub.add_parser('finite-exit')
    exit_cmd.add_argument('model',type=Path)
    exit_cmd.add_argument('region',type=Path)
    exit_cmd.add_argument('--output',type=Path,required=True)
    menu=sub.add_parser('frozen-menu')
    menu.add_argument('request',type=Path)
    menu.add_argument('--output',type=Path,required=True)
    lp=sub.add_parser('lp-propose')
    lp.add_argument('model',type=Path)
    lp.add_argument('--output',type=Path,required=True)
    lpcheck=sub.add_parser('lp-check')
    lpcheck.add_argument('model',type=Path)
    lpcheck.add_argument('receipt',type=Path)
    lpcheck.add_argument('--output',type=Path,required=True)
    bundle=sub.add_parser('bundle-verify')
    bundle.add_argument('root',type=Path)
    bundle.add_argument('manifest',type=Path)
    bundle.add_argument('--expected-manifest-sha256')
    bundle.add_argument('--output',type=Path,required=True)
    inventory=sub.add_parser('bundle-inventory')
    inventory.add_argument('root',type=Path)
    inventory.add_argument('--scope',required=True)
    inventory.add_argument('--source-commit',required=True)
    inventory.add_argument('--source-tree',required=True)
    inventory.add_argument('--output',type=Path,required=True)
    domain=sub.add_parser('domain-validate')
    domain.add_argument('evidence',type=Path)
    domain.add_argument('--output',type=Path,required=True)
    legacy=sub.add_parser('legacy-validate')
    legacy.add_argument('application_json',type=Path)
    legacy.add_argument('--source-root',type=Path,required=True)
    legacy.add_argument('--output',type=Path,required=True)
    args=p.parse_args(argv)
    try:
        if args.command in BUDGETED_COMMANDS:
            from .budget import enter_child,in_child,run_budgeted
            if not in_child():
                return run_budgeted(list(sys.argv[1:] if argv is None else argv),args.output)
            enter_child()
        if args.command=='capabilities':
            print(json.dumps(registry(),indent=2,sort_keys=True))
        elif args.command=='about':
            from importlib import metadata
            try:version=metadata.version('permansson-application-successor-recovery')
            except metadata.PackageNotFoundError:version=None
            print(json.dumps({'package':'permansson_app','location':str(Path(__file__).resolve().parent),
                              'distribution_version':version,'python':sys.version.split()[0],
                              'lean_status':'NOT_EXECUTED'},sort_keys=True))
        elif args.command=='resources':
            result=(export_extended_resources if args.full else export_resources)(args.output) if args.output else list(NAMES)
            print(json.dumps(result,indent=2,sort_keys=True))
        elif args.command=='run':
            result=execute(args.request,args.source_root,args.output)
            print(json.dumps({'ok':True,'numeric_status':result['numeric_status'],
                              'lean_status':result['lean_status'],
                              'result_file':str(args.output/'application_result.json')},sort_keys=True))
        elif args.command=='bundle-inventory':
            from .bundle import create_detached_manifest
            manifest=create_detached_manifest(args.root,scope=args.scope,
                        source_commit=args.source_commit,source_tree=args.source_tree)
            out=_new_output(args.output)
            _write_json(out/'detached_manifest.json',manifest)
            print(json.dumps({'ok':True,'files':len(manifest['files']),'output':str(out)},sort_keys=True))
        elif args.command=='bundle-verify':
            from .bundle import verify_detached_bundle
            from .strict_json import strict_read
            _,manifest=strict_read(args.manifest)
            check=verify_detached_bundle(args.root,manifest,
                 expected_manifest_sha256=args.expected_manifest_sha256)
            out=_new_output(args.output)
            _write_json(out/'bundle_check.json',check)
            print(json.dumps({'ok':True,'status':check['status'],
                 'origin_authenticated':False,'output':str(out)},sort_keys=True))
        elif args.command=='domain-validate':
            from .domain_evidence import validate_domain_evidence
            from .strict_json import strict_read
            _,doc=strict_read(args.evidence)
            check=validate_domain_evidence(doc)
            out=_new_output(args.output)
            _write_json(out/'domain_evidence_check.json',check)
            print(json.dumps({'ok':True,'status':check['status'],
                 'scientific_claims_verified':False,'output':str(out)},sort_keys=True))
        elif args.command=='legacy-validate':
            from .legacy import validate_legacy
            result=validate_legacy(args.application_json,args.source_root,args.output)
            _write_json(args.output/'legacy_import.json',result)
            print(json.dumps({'ok':True,'contract_valid':result['original_result']['contract_valid'],
                              'scientific_claims_verified':False},sort_keys=True))
        elif args.command in ('nonlinear-stationary','finite-residence'):
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            if args.command=='nonlinear-stationary':
                from .engines.nonlinear import propose_nonlinear
                from .receipts.nonlinear import check_nonlinear
                schema='schemas/nonlinear.v1.schema.json'
                validate_packaged_schema(schema,raw)
                receipt=propose_nonlinear(raw)
                checker=check_nonlinear(raw,receipt)
                capability='finite.nonlinear_classwise_stationary.numeric.v1'
                receipt_name='nonlinear_receipt.json'
            else:
                from .engines.residence import solve_residence
                from .receipts.residence import check_residence
                schema='schemas/residence.v1.schema.json'
                validate_packaged_schema(schema,raw)
                receipt=solve_residence(raw)
                checker=check_residence(raw,receipt)
                capability='finite.residence_monitor.numeric.v1'
                receipt_name='residence_receipt.json'
            report=numeric_application_report(capability=capability,
                   model_semantic_identity=receipt['problem_semantic_identity'] if 'problem_semantic_identity' in receipt else receipt['request_identity'],
                   computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in ((receipt_name,receipt),('independent_check.json',checker),('scientific_report.json',report)):
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-belief-tree':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.belief_tree import propose_belief_tree
            from .receipts.belief_tree import check_belief_tree
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/belief_tree.v1.schema.json',raw)
            receipt=propose_belief_tree(raw)
            checker=check_belief_tree(raw,receipt)
            report=numeric_application_report(capability='finite.observation_history_tree.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('belief_tree_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='one-step-belief':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.belief import propose_belief
            from .receipts.belief import check_belief
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/belief.v1.schema.json',raw)
            receipt=propose_belief(raw)
            checker=check_belief(raw,receipt)
            report=numeric_application_report(capability='finite.one_step_observation_belief.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('belief_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='one-step-risk':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.risk_occupancy import propose_risk
            from .receipts.risk_occupancy import check_risk
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/risk_occupancy.v1.schema.json',raw)
            receipt=propose_risk(raw)
            checker=check_risk(raw,receipt)
            report=numeric_application_report(capability='finite.one_step_risk_occupancy.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('occupancy_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command in ('lean-emit','lean-recheck'):
            from .proof.lean_candidates import emit,recheck
            if args.command=='lean-emit':
                result=emit(args.family,args.request,args.receipt,args.output,args.region)
            else:
                result=recheck(args.family,args.request,args.receipt,args.candidate,args.region)
            print(json.dumps({'ok':True,'family':args.family,'result':result},sort_keys=True))
        elif args.command=='finite-cq1-transport':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.cq1_transport import propose_cq1_transport
            from .receipts.cq1_transport import check_cq1_transport
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/cq1_transport.v1.schema.json',raw)
            receipt=propose_cq1_transport(raw)
            checker=check_cq1_transport(raw,receipt)
            report=numeric_application_report(capability='finite.cq1_certificate_transport.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('cq1_transport_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'transport_status':receipt['transport_status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='one-step-risk-infeasibility':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.risk_infeasibility import propose_risk_infeasibility
            from .receipts.risk_infeasibility import check_risk_infeasibility
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/risk_occupancy.v1.schema.json',raw)
            receipt=propose_risk_infeasibility(raw)
            checker=check_risk_infeasibility(raw,receipt)
            report=numeric_application_report(capability='finite.one_step_risk_infeasibility.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('infeasibility_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-adaptive-grammar':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.adaptive import propose_adaptive
            from .receipts.adaptive import check_adaptive
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/adaptive.v1.schema.json',raw)
            receipt=propose_adaptive(raw)
            checker=check_adaptive(raw,receipt)
            report=numeric_application_report(capability='finite.adaptive_block_control.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('adaptive_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-private-stage':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.private_stage import propose_private_stage
            from .receipts.private_stage import check_private_stage
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/private_stage.v1.schema.json',raw)
            receipt=propose_private_stage(raw)
            checker=check_private_stage(raw,receipt)
            report=numeric_application_report(capability='finite.private_control_stage_saddle.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('private_stage_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-multiagent':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.multiagent import propose_multiagent
            from .receipts.multiagent import check_multiagent
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/multiagent.v1.schema.json',raw)
            receipt=propose_multiagent(raw)
            checker=check_multiagent(raw,receipt)
            report=numeric_application_report(capability='finite.two_player_protocol.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('multiagent_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-algebra':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.algebra import propose_algebra
            from .receipts.algebra import check_algebra
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/algebra.v1.schema.json',raw)
            receipt=propose_algebra(raw)
            checker=check_algebra(raw,receipt)
            report=numeric_application_report(capability='finite.rational_algebra_witness.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('algebra_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-metric':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.metric import propose_metric
            from .receipts.metric import check_metric
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/metric.v1.schema.json',raw)
            receipt=propose_metric(raw)
            checker=check_metric(raw,receipt)
            report=numeric_application_report(capability='finite.metric_contraction_perturbation.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('metric_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-cq1':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.cq1 import propose_cq1
            from .receipts.cq1 import check_cq1
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/cq1.v1.schema.json',raw)
            receipt=propose_cq1(raw)
            checker=check_cq1(raw,receipt)
            report=numeric_application_report(capability='finite.cq1_constitutive_certificate.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('cq1_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-robust-nature':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.robust_nature import propose_nature
            from .receipts.robust_nature import check_nature
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/robust_nature.v1.schema.json',raw)
            receipt=propose_nature(raw)
            checker=check_nature(raw,receipt)
            report=numeric_application_report(capability='finite.rectangular_vs_committed_nature.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('nature_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command in ('finite-grammar','finite-quotient'):
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            if args.command=='finite-grammar':
                from .engines.grammar import propose_grammar
                from .receipts.grammar import check_grammar
                schema='schemas/grammar.v1.schema.json'
                capability='finite.patch_grammar.numeric.v1'
                compute,check=propose_grammar,check_grammar
                filename='grammar_receipt.json'
            else:
                from .engines.quotients import propose_quotient
                from .receipts.quotients import check_quotient
                schema='schemas/quotient.v1.schema.json'
                capability='finite.typed_quotient.numeric.v1'
                compute,check=propose_quotient,check_quotient
                filename='quotient_receipt.json'
            validate_packaged_schema(schema,raw)
            receipt=compute(raw)
            checker=check(raw,receipt)
            report=numeric_application_report(capability=capability,
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [(filename,receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='frozen-menu':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.menu import propose_menu
            from .receipts.menu import check_menu
            from .report import numeric_application_report
            _,raw=strict_read(args.request)
            validate_packaged_schema('schemas/finite_menu.v1.schema.json',raw)
            receipt=propose_menu(raw)
            checker=check_menu(raw,receipt)
            report=numeric_application_report(capability='finite.frozen_menu.numeric.v1',
                 model_semantic_identity=receipt['request_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('menu_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-perturbation':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.robustness import parse_perturbation,propose_perturbation
            from .receipts.robustness import check_perturbation
            from .report import numeric_application_report
            _,raw=strict_read(args.problem)
            validate_packaged_schema('schemas/finite_perturbation.v1.schema.json',raw)
            problem=parse_perturbation(raw)
            receipt=propose_perturbation(problem)
            checker=check_perturbation(problem,receipt)
            report=numeric_application_report(capability='finite.path_perturbation_tv.numeric.v1',
                model_semantic_identity=problem.identity,
                computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('perturbation_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':'FINITE_PATH_TV_BOUND_VERIFIED',
                'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-safety':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.safety import parse_safety_problem,propose_safety_core
            from .receipts.safety import check_safety_core
            from .report import numeric_application_report
            _,raw=strict_read(args.problem)
            validate_packaged_schema('schemas/finite_safety.v1.schema.json',raw)
            problem=parse_safety_problem(raw)
            receipt=propose_safety_core(problem)
            checker=check_safety_core(problem,receipt)
            report=numeric_application_report(capability='finite.almost_sure_safety_core.numeric.v1',
                 model_semantic_identity=problem.identity,
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('safety_core_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':'EXACT_ALMOST_SURE_SAFETY_CORE_VERIFIED',
                 'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-bellman':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.hitting import parse_hitting_problem,propose_bellman
            from .receipts.control import check_bellman
            from .report import numeric_application_report
            _, raw=strict_read(args.problem)
            validate_packaged_schema('schemas/control_hitting.v1.schema.json',raw)
            problem=parse_hitting_problem(raw)
            receipt=propose_bellman(problem)
            checker=check_bellman(problem,receipt)
            report=numeric_application_report(capability='finite.hitting_bellman.numeric.v1',
                 model_semantic_identity={'model':problem.world.semantic_id(),'objective':problem.semantic_id},
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('bellman_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':'EXACT_FINITE_BELLMAN_CHECKED',
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command=='finite-survival':
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .engines.finite_survival import propose_finite_survival
            from .receipts.finite_survival import check_survival_receipt
            from .report import numeric_application_report
            _, raw=strict_read(args.comparison)
            validate_packaged_schema('schemas/finite_survival.v1.schema.json',raw)
            receipt=propose_finite_survival(raw)
            checker=check_survival_receipt(raw,receipt)
            report=numeric_application_report(capability='finite.killed_kernel.survival.numeric.v1',
                 model_semantic_identity=receipt['comparison_identity'],
                 computation_receipt=receipt,independent_check=checker)
            out=_new_output(args.output)
            for name,value in [('finite_survival_receipt.json',receipt),('independent_check.json',checker),
                               ('scientific_report.json',report)]:
                _write_json(out/name,value)
            print(json.dumps({'ok':True,'numeric_status':checker['status'],
                              'lean_status':'NOT_EXECUTED','output':str(out)},sort_keys=True))
        elif args.command in ('finite-kernel','finite-occupation','finite-exit','lp-propose','lp-check'):
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .report import numeric_application_report
            _, raw=strict_read(args.model)
            if args.command in ('finite-kernel','finite-occupation','finite-exit'):
                from .finite_world import parse_finite_world
                from .receipts.finite_world import emit_finite_receipt,check_finite_receipt
                validate_packaged_schema('schemas/finite_world.v1.schema.json',raw)
                model=parse_finite_world(raw)
                if args.command=='finite-kernel':
                    receipt=emit_finite_receipt(model)
                    checker=check_finite_receipt(model,receipt)
                    cap='finite.alpha_P_U.induced_kernel.numeric.v1'
                    output_name='induced_kernel_receipt.json'
                    identity=model.semantic_id()
                elif args.command=='finite-occupation':
                    from .engines.occupation import compute_occupation
                    from .receipts.occupation import check_occupation
                    receipt=compute_occupation(model)
                    checker=check_occupation(model,receipt)
                    cap='finite.random_occupation.numeric.v1'
                    output_name='occupation_receipt.json'
                    identity=model.semantic_id()
                else:
                    from .engines.exit import parse_region,compute_exit
                    from .receipts.exit import check_exit
                    _,region_raw=strict_read(args.region)
                    validate_packaged_schema('schemas/finite_region.v1.schema.json',region_raw)
                    region=parse_region(region_raw,model)
                    receipt=compute_exit(model,region)
                    checker=check_exit(model,region,receipt)
                    cap='finite.first_exit_and_survival.numeric.v1'
                    output_name='exit_receipt.json'
                    identity={'model':model.semantic_id(),'region':region.semantic_id}
                report=numeric_application_report(capability=cap,
                       model_semantic_identity=identity,computation_receipt=receipt,independent_check=checker)
                out=_new_output(args.output)
                for name,value in [(output_name,receipt),('independent_check.json',checker),('scientific_report.json',report)]:
                    _write_json(out/name,value)
                print(json.dumps({'ok':True,'numeric_status':'EXACT_RATIONAL_VERIFIED','lean_status':'NOT_EXECUTED',
                                  'output':str(out)},sort_keys=True))
            else:
                from .engines.lp_types import parse_lp
                validate_packaged_schema('schemas/lp.v1.schema.json',raw)
                model=parse_lp(raw)
                out=None
                if args.command=='lp-propose':
                    from .engines.lp import propose_lp_optimum
                    result=propose_lp_optimum(model)
                    out=_new_output(args.output)
                    _write_json(out/'proposal.json',result)
                    if result['status']=='CHECKED_OPTIMAL_CANDIDATE':
                        from .receipts.lp import check_lp_certificate
                        checker=check_lp_certificate(model,result['receipt'])
                        report=numeric_application_report(capability='lp.exact_rational.optimality.numeric.v1',
                             model_semantic_identity=model.semantic_id(),computation_receipt=result['receipt'],independent_check=checker)
                        _write_json(out/'independent_check.json',checker)
                        _write_json(out/'scientific_report.json',report)
                    print(json.dumps({'ok':True,'status':result['status'],'output':str(out)},sort_keys=True))
                else:
                    from .receipts.lp import check_lp_certificate,check_farkas_certificate,OPTIMAL,INFEASIBLE
                    from .strict_json import read_result
                    _,receipt=read_result(args.receipt)
                    if type(receipt) is not dict:raise AppError('LP_CERT','certificate must be object')
                    if receipt.get('format')==OPTIMAL:
                        checker=check_lp_certificate(model,receipt)
                    elif receipt.get('format')==INFEASIBLE:
                        checker=check_farkas_certificate(model,receipt)
                    else:raise AppError('LP_CERT','unknown certificate family')
                    report=numeric_application_report(capability='lp.exact_rational.independent_verification.v1',
                          model_semantic_identity=model.semantic_id(),computation_receipt=receipt,independent_check=checker)
                    out=_new_output(args.output)
                    _write_json(out/'independent_check.json',checker)
                    _write_json(out/'scientific_report.json',report)
                    print(json.dumps({'ok':True,'status':checker['status'],'output':str(out)},sort_keys=True))
        else:raise AssertionError('unreachable command')
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2
    except OSError as exc:
        import errno
        if exc.errno==errno.ENOMEM:
            from .budget import MEMORY_EXIT
            print(json.dumps({'ok':False,'error':{'code':'BUDGET_MEMORY','message':'memory budget exhausted'}},
                             sort_keys=True),file=sys.stderr)
            return MEMORY_EXIT
        if exc.errno!=errno.EFBIG:
            raise
        from .budget import OUTPUT_EXIT
        print(json.dumps({'ok':False,'error':{'code':'BUDGET_OUTPUT','message':'output budget exhausted'}},
                         sort_keys=True),file=sys.stderr)
        return OUTPUT_EXIT
    except (MemoryError,ImportError) as exc:
        from .budget import MEMORY_EXIT,is_memory_failure
        if not is_memory_failure(exc):
            raise
        print(json.dumps({'ok':False,'error':{'code':'BUDGET_MEMORY','message':'memory budget exhausted'}},
                         sort_keys=True),file=sys.stderr)
        return MEMORY_EXIT

if __name__=='__main__':raise SystemExit(main())
