"""Resource access works in an installed wheel without the source tree."""
from importlib.resources import files
from pathlib import Path
from .errors import AppError

NAMES = ("schemas/request.v1.schema.json", "schemas/result.v1.schema.json",
         "schemas/c10.native.schema.json", "schemas/c11.native.schema.json",
         "examples/c10.request.json", "examples/c10.model.json",
         "examples/c11.periodic.request.json", "examples/c11.periodic.model.json",
         "examples/c11.multiclass.request.json", "examples/c11.multiclass.model.json")


def resource_bytes(name: str) -> bytes:
    if name not in NAMES and name != "capabilities.json":
        raise AppError("RESOURCE_SCOPE", "unregistered package resource")
    return files("permansson_app").joinpath("data", *name.split("/")).read_bytes()


def export_resources(directory: Path):
    if directory.exists():
        raise AppError("OUTPUT_SCOPE", "resource export destination must not exist")
    directory.mkdir(parents=True, exist_ok=False)
    results = {}
    from hashlib import sha256
    for name in NAMES:
        data = resource_bytes(name)
        output = directory / name
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(data)
        results[name] = sha256(data).hexdigest()
    return results
