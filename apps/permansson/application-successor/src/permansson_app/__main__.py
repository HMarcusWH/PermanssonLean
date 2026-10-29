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
    out=path.absolute()
    if out.exists() or out.is_symlink() or any(p.is_symlink() for p in (out.parent,*out.parent.parents)):
        raise AppError('OUTPUT_SCOPE','output must be new and must not pass through a symlink')
    out.mkdir(parents=True,exist_ok=False)
    return out


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    sub=p.add_subparsers(dest='command',required=True)
    sub.add_parser('capabilities')
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
        if args.command=='capabilities':
            print(json.dumps(registry(),indent=2,sort_keys=True))
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
        elif args.command in ('finite-kernel','lp-propose','lp-check'):
            from .strict_json import strict_read
            from .schema_validate import validate_packaged_schema
            from .report import numeric_application_report
            _, raw=strict_read(args.model)
            if args.command=='finite-kernel':
                from .finite_world import parse_finite_world
                from .receipts.finite_world import emit_finite_receipt,check_finite_receipt
                validate_packaged_schema('schemas/finite_world.v1.schema.json',raw)
                model=parse_finite_world(raw)
                receipt=emit_finite_receipt(model)
                checker=check_finite_receipt(model,receipt)
                report=numeric_application_report(capability='finite.alpha_P_U.induced_kernel.numeric.v1',
                       model_semantic_identity=model.semantic_id(),computation_receipt=receipt,independent_check=checker)
                out=_new_output(args.output)
                for name,value in [('induced_kernel_receipt.json',receipt),('independent_check.json',checker),('scientific_report.json',report)]:
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
                    _,receipt=strict_read(args.receipt)
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

if __name__=='__main__':raise SystemExit(main())
