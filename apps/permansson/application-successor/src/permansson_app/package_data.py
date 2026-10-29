"""Resource access works in an installed wheel without the source tree."""
from importlib.resources import files
from pathlib import Path
from .errors import AppError

NAMES = ("schemas/request.v1.schema.json", "schemas/result.v1.schema.json",
         "schemas/c10.native.schema.json", "schemas/c11.native.schema.json",
         "examples/c10.request.json", "examples/c10.model.json",
         "examples/c11.periodic.request.json", "examples/c11.periodic.model.json",
         "examples/c11.multiclass.request.json", "examples/c11.multiclass.model.json")


SCHEMA_RESOURCES = ("schemas/finite_world.v1.schema.json", "schemas/lp.v1.schema.json", "schemas/finite_survival.v1.schema.json", "schemas/finite_region.v1.schema.json", "schemas/finite_menu.v1.schema.json", "schemas/control_hitting.v1.schema.json", "schemas/grammar.v1.schema.json", "schemas/quotient.v1.schema.json", "schemas/finite_safety.v1.schema.json", "schemas/finite_perturbation.v1.schema.json", "schemas/residence.v1.schema.json", "schemas/nonlinear.v1.schema.json")
EXTENDED_EXAMPLES = ("examples/finite_world.v1.model.json", "examples/lp.v1.model.json", "examples/finite_survival.v1.json", "examples/finite_region.v1.json", "examples/finite_menu.v1.json", "examples/control_hitting.v1.json", "examples/grammar.v1.json", "examples/quotient.v1.json", "examples/finite_safety.v1.json", "examples/finite_perturbation.v1.json", "examples/residence.v1.json", "examples/nonlinear.v1.json")


def resource_bytes(name: str) -> bytes:
    if name not in NAMES and name not in SCHEMA_RESOURCES and name not in EXTENDED_EXAMPLES and name != "capabilities.json":
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


def export_extended_resources(directory: Path):
    """Export both legacy recovered examples and successor schema contracts."""
    if directory.exists():
        raise AppError("OUTPUT_SCOPE", "destination already exists")
    directory.mkdir(parents=True,exist_ok=False)
    from hashlib import sha256
    result={}
    for name in (*NAMES,*SCHEMA_RESOURCES,*EXTENDED_EXAMPLES):
        data=resource_bytes(name)
        out=directory / name
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_bytes(data)
        result[name]=sha256(data).hexdigest()
    return result
