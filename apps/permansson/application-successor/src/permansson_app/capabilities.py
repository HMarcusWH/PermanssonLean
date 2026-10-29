"""Closed two-capability registry with source-byte pins."""
import json
from .package_data import resource_bytes
from .errors import AppError


def registry():
    data = json.loads(resource_bytes("capabilities.json"))
    caps = data.get("capabilities")
    if not isinstance(caps, dict) or set(caps) != {"c10.fixed_six_state.numeric.v1", "c11.stationary_1_to_6.numeric.v1"}:
        raise AppError("REGISTRY", "invalid registry capability set")
    return data


def selected(key: str):
    c = registry()["capabilities"].get(key)
    if c is None:
        raise AppError("UNSUPPORTED_CAPABILITY", "not a supported numeric capability")
    return c
