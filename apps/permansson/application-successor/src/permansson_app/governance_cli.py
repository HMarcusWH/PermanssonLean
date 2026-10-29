"""Read-only source, claim, domain and evidence assessment CLI.

This command does not execute evidence-bundle scripts, invoke Lean on arbitrary
input, authenticate the origin of supplied evidence, or approve a release.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
from importlib.resources import files
from datetime import datetime
from .errors import AppError
from .strict_json import strict_read
from .provenance import check_provenance
from .acceptance import AcceptanceTarget,AcceptancePolicy,assess_acceptance
from .evidence import EvidenceSet
from .replay import ReplayTarget,evaluate_replay
from .claims import ClaimRegistry
from .domain.bundle import open_bundle
from .domain.importer import import_domain
from .domain.registry import PROFILES


def _new_output(destination:Path)->Path:
    p=destination.absolute()
    if p.exists() or p.is_symlink() or any(a.is_symlink() for a in p.parents):
        raise AppError('OUTPUT_SCOPE','destination must be new and have no symlink ancestors')
    p.mkdir(parents=True,exist_ok=False)
    return p


def _write(directory:Path,name:str,obj:dict):
    (directory/name).write_text(json.dumps(obj,sort_keys=True,indent=2,ensure_ascii=False,allow_nan=False)+'\n',encoding='utf-8')


def _read(path:Path):
    return strict_read(path,max_bytes=2_000_000)[1]


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    commands=parser.add_subparsers(dest='command',required=True)
    claims=commands.add_parser('claims-list')
    claims.add_argument('--output',type=Path,required=True)
    provenance=commands.add_parser('provenance-check')
    provenance.add_argument('graph',type=Path)
    provenance.add_argument('--output',type=Path,required=True)
    case=commands.add_parser('domain-import')
    case.add_argument('bundle',type=Path)
    case.add_argument('--case',required=True,choices=sorted(PROFILES))
    case.add_argument('--cutoff',help='ISO8601 offset-aware available-information cutoff')
    case.add_argument('--output',type=Path,required=True)
    assessment=commands.add_parser('release-assess')
    assessment.add_argument('target',type=Path)
    assessment.add_argument('evidence',type=Path)
    assessment.add_argument('external_pins',type=Path)
    assessment.add_argument('policy',type=Path)
    assessment.add_argument('--output',type=Path,required=True)
    replay=commands.add_parser('replay-assess')
    replay.add_argument('target',type=Path)
    replay.add_argument('transcript',type=Path)
    replay.add_argument('evidence',type=Path)
    replay.add_argument('external_pins',type=Path)
    replay.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    try:
        if args.command=='claims-list':
            raw=json.loads(files('permansson_app').joinpath('data/claim_registry.json').read_text())
            registry=ClaimRegistry.parse(raw)
            result={'format':'Permansson.App.ClaimsSnapshot.v1','original_cases':sum(c.classification=='historical_case' for c in registry.claims),
                    'later_claims':sum(c.classification=='later_claim' for c in registry.claims),
                    'source_status':'HISTORICAL_UNREVIEWED_CANDIDATE_SOURCE_MAP',
                    'ids':[c.claim_id for c in registry.claims],
                    'mathematical_certification':False,'release_authorized':False}
            filename='claim_snapshot.json'
        elif args.command=='provenance-check':
            raw=_read(args.graph)
            if type(raw) is not dict or set(raw)!={'format','nodes','cutoff','evaluation_start'} or raw['format']!='Permansson.App.ProvenanceGraph.v1':
                raise AppError('PROVENANCE_FORMAT','unsupported graph object')
            result=check_provenance(raw['nodes'],cutoff=raw['cutoff'],evaluation_start=raw['evaluation_start'])
            filename='provenance_check.json'
        elif args.command=='domain-import':
            cutoff=None
            if args.cutoff is not None:
                from .provenance import instant
                cutoff=instant(args.cutoff,'cutoff')
            result=import_domain(open_bundle(args.bundle),args.case,cutoff=cutoff).to_dict()
            filename='domain_import.json'
        elif args.command=='release-assess':
            raw=_read(args.evidence);pins=_read(args.external_pins)
            ev=EvidenceSet.from_external_hashes(raw,trusted_expected_digests=pins)
            result=assess_acceptance(AcceptanceTarget.parse(_read(args.target)),ev,
                       AcceptancePolicy.parse(_read(args.policy))).to_dict()
            filename='acceptance_assessment.json'
        else:
            ev=EvidenceSet.from_external_hashes(_read(args.evidence),
                    trusted_expected_digests=_read(args.external_pins))
            result=evaluate_replay(ReplayTarget.parse(_read(args.target)),_read(args.transcript),ev)
            filename='replay_assessment.json'
        out=_new_output(args.output)
        _write(out,filename,result)
        print(json.dumps({'ok':True,'status':result.get('status','REPORT_GENERATED'),
                          'output':str(out),'authorization_granted':False},sort_keys=True))
        return 0
    except AppError as error:
        print(json.dumps({'ok':False,'error':{'code':error.code,'message':str(error)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
