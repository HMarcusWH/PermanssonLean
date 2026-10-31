"""Read-only execution of the untouched Application Standard 0.1.0 validator.

The legacy implementation, source digest and results are not altered. A valid
report contract can report scientific INVALID or unresolved status.
"""
from __future__ import annotations
from hashlib import sha256
import json
from pathlib import Path
import sys
from .errors import AppError
from .process import RunBudget,run_bounded
from .strict_json import strict_loads

VALIDATOR_SHA256='55d2ad768c34edd613200de911d8d3894b607b42d0a7e8513cced3e49545c475'


def validate_legacy(bundle:Path,source_root:Path,output:Path)->dict:
    source_root=source_root.resolve()
    # The validator runs with the source root as its working directory, so pass it
    # the absolute path of the file checked and hashed here (not resolved: the
    # symlink checks below still see the path as given).
    bundle=bundle.absolute()
    validator=source_root/'application/validator/validate_application.py'
    version=source_root/'application/VERSION.json'
    if validator.is_symlink() or not validator.is_file() or sha256(validator.read_bytes()).hexdigest()!=VALIDATOR_SHA256:
        raise AppError('LEGACY_SOURCE','legacy validator bytes do not match historical source')
    if version.is_symlink() or not version.is_file():
        raise AppError('LEGACY_SOURCE','legacy version unavailable')
    ver=json.loads(version.read_bytes())
    if ver.get('version')!='0.1.0' or ver.get('compatible_theory')!='0.1.8' or ver.get('status')!='DRAFT':
        raise AppError('LEGACY_SOURCE','legacy contract version mismatch')
    if bundle.is_symlink() or bundle.name!='application.json' or not bundle.is_file():
        raise AppError('LEGACY_INPUT','pass a regular legacy application.json')
    parent=output.absolute().parent
    if any(v.is_symlink() for v in (parent,*parent.parents)):
        raise AppError('OUTPUT_SCOPE','output ancestor symlink')
    if source_root==parent.resolve() or source_root in parent.resolve().parents:
        raise AppError('OUTPUT_SCOPE','output inside source')
    if output.exists():raise AppError('OUTPUT_SCOPE','output must be new')
    input_hash=sha256(bundle.read_bytes()).hexdigest()
    output.mkdir(parents=True,exist_ok=False)
    log=output/'legacy.json'
    info=run_bounded([sys.executable,'-I','-B',str(validator),str(bundle),'--json'],
                     source_root,log,budget=RunBudget.start(seconds=60),allowed_exit_codes=(0,1,2))
    value=strict_loads(log.read_bytes(),max_bytes=131072)
    if type(value) is not dict or type(value.get('contract_valid')) is not bool or value.get('scientific_claims_verified') is not False or type(value.get('errors')) is not list or type(value.get('notice')) is not str:
        raise AppError('LEGACY_RESULT','invalid historical report envelope')
    if info['exit_code']==0 and not value['contract_valid'] or info['exit_code']==1 and value['contract_valid']:
        raise AppError('LEGACY_RESULT','legacy exit and contract status disagree')
    if sha256(bundle.read_bytes()).hexdigest()!=input_hash:
        raise AppError('LEGACY_SOURCE','input changed during validation')
    return {'format':'Permansson.App.LegacyImport.v1',
            'legacy_standard':'0.1.0','compatible_theory':'0.1.8',
            'original_application_sha256':input_hash,'legacy_validator_sha256':VALIDATOR_SHA256,
            'legacy_exit_code':info['exit_code'],'original_result':value,
            'scientific_claims_verified':False,'independent_acceptance':'NOT_ASSESSED'}
