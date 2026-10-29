"""Offline Draft 2020-12 schema gate, no remote schema retrieval."""
from __future__ import annotations
import json
from functools import lru_cache
from .errors import AppError
from .package_data import resource_bytes, SCHEMA_RESOURCES

@lru_cache(maxsize=1)
def _validators():
    try:
        from jsonschema import Draft202012Validator
        from referencing import Registry, Resource
        from referencing.exceptions import NoSuchResource
    except ImportError as exc:
        raise AppError('SCHEMA_DEPENDENCY', 'Install validated jsonschema extra for full Draft 2020-12 checking') from exc
    def deny(uri): raise NoSuchResource(ref=uri)
    registry=Registry(retrieve=deny)
    loaded={}
    for name in SCHEMA_RESOURCES:
        data=json.loads(resource_bytes(name))
        Draft202012Validator.check_schema(data)
        if data['$id'] in loaded:
            raise AppError('SCHEMA_INVALID','duplicate packaged schema identifier')
        loaded[data['$id']]=Resource.from_contents(data)
    registry=registry.with_resources(loaded.items())
    return {name:Draft202012Validator(json.loads(resource_bytes(name)),registry=registry) for name in SCHEMA_RESOURCES}

def validate_packaged_schema(name:str, instance:object)->dict:
    try:validator=_validators()[name]
    except KeyError as exc:raise AppError('SCHEMA_SCOPE','unregistered schema') from exc
    errors=list(validator.iter_errors(instance))
    if errors:
        err=sorted(errors,key=lambda e:(list(map(str,e.absolute_path)),e.message))[0]
        raise AppError('SCHEMA_INVALID',f'{name}: {err.message}')
    return {'format':'Permansson.App.SchemaCheck.v1','schema':name,'status':'PASS'}
