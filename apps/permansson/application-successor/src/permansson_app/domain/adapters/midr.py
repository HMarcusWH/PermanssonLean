"""Read-only midr companion artifact importer; results remain unverified evidence."""
from ..importer import import_domain
from ..registry import resolve_profile

def parse(bundle,profile=None,*,cutoff=None):
    return import_domain(bundle,profile or resolve_profile('midr'),cutoff=cutoff)
