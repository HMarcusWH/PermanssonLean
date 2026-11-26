"""Closed, bounded research input contracts. Fractions only, no solver flags."""
from __future__ import annotations

from fractions import Fraction as Q
from hashlib import sha256
import json
from math import lcm
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
APP = ROOT / "apps/permansson/application-successor/src"
if str(APP) not in sys.path:
    sys.path.insert(0, str(APP))

from permansson_app.finite_world import exact_ratio, exact_result, MAX_RESULT_BITS
from permansson_app.strict_json import strict_read, read_result

FORMAT = "Permansson.Research.ApproxEquilibrium.v1"
RECEIPT = "Permansson.Research.ApproxEquilibriumReceipt.v1"
MAX_ACTIONS = 16
MAX_STATES = 6
MAX_HORIZON = 16
# All admitted inputs share a bounded denominator. The finite recurrence
# uses products of at most three primitive probabilities per step, so this
# preflight also prevents pathological denominator growth before formatting.
MAX_COMMON_DENOMINATOR_BITS = 192
MAX_RECEIPT_BYTES = 1024 * 1024

class Invalid(ValueError):
    pass

def require(condition, message):
    if not condition:
        raise Invalid(message)

def keys(obj, expected):
    require(type(obj) is dict and set(obj) == set(expected), "missing or extra fields")

def seq(obj, length):
    require(type(obj) is list and len(obj) == length, "incomplete domain")
    return obj

def ratio(obj, probability=False):
    value = exact_ratio(obj, probability=probability)
    require(str(value) == obj, "non-reduced or noncanonical rational input")
    return value

def bounded_problem(d):
    """Conservative arithmetic preflight, not an OS-level whole-run budget."""
    common = 1
    def visit(obj):
        nonlocal common
        if isinstance(obj, Q):
            common = lcm(common, obj.denominator)
            require(common.bit_length() <= MAX_COMMON_DENOMINATOR_BITS,
                    "common denominator exceeds research arithmetic budget")
        elif isinstance(obj, (list, tuple)):
            for a in obj: visit(a)
        elif isinstance(obj, dict):
            for a in obj.values(): visit(a)
    visit(d)
    return d

def row(obj, n):
    r = tuple(ratio(x, True) for x in seq(obj, n))
    require(sum(r, Q(0)) == 1, "probability row is not normalized")
    return r

def matrix(obj, m, n, bounded):
    return tuple(tuple(ratio(v, bounded) for v in seq(r, n)) for r in seq(obj, m))

def integer(obj, lo, hi):
    require(type(obj) is int and lo <= obj <= hi, "integer outside supported scope")
    return obj

def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
                      allow_nan=False).encode("ascii")

def identity(raw):
    return sha256(canonical(raw)).hexdigest()

def pack(obj):
    """Serialize exact results under the existing separate result-size bound."""
    if isinstance(obj, Q):
        require(max(obj.numerator.bit_length(), obj.denominator.bit_length())
                <= MAX_RESULT_BITS, "result rational exceeds research arithmetic budget")
        s = str(obj)
        exact_result(s)
        return s
    if isinstance(obj, (list, tuple)):
        return [pack(v) for v in obj]
    if isinstance(obj, dict):
        return {k: pack(v) for k, v in obj.items()}
    return obj

def parse(raw):
    require(type(raw) is dict and raw.get("format") == FORMAT, "wrong input format")
    kind = raw.get("kind")
    if kind in ("regret", "kite"):
        keys(raw, ("format", "kind", "R", "C", "x", "y", "epsilon"))
        require(type(raw["x"]) is list and type(raw["y"]) is list, "invalid strategies")
        m = integer(len(raw["x"]), 1, MAX_ACTIONS)
        n = integer(len(raw["y"]), 1, MAX_ACTIONS)
        epsilon = ratio(raw["epsilon"], True)
        if kind == "kite":
            require(0 < epsilon < Q(1, 2), "kite threshold must be in (0,1/2)")
        return bounded_problem(dict(kind=kind, R=matrix(raw["R"],m,n,True),
                    C=matrix(raw["C"],m,n,True), x=row(raw["x"],m),
                    y=row(raw["y"],n), epsilon=epsilon))
    if kind == "discounted":
        keys(raw, ("format", "kind", "states", "R", "C", "P", "x", "y",
                   "discount", "values"))
        n = integer(raw["states"], 1, MAX_STATES)
        R = tuple(matrix(a,2,2,False) for a in seq(raw["R"],n))
        C = tuple(matrix(a,2,2,False) for a in seq(raw["C"],n))
        P = physical(raw["P"],n)
        x,y = (tuple(row(a,2) for a in seq(raw[k],n)) for k in ("x","y"))
        beta = tuple(ratio(a,True) for a in seq(raw["discount"],2))
        require(all(a < 1 for a in beta), "discount must be strictly below one")
        V = tuple(tuple(ratio(a) for a in seq(v,n)) for v in seq(raw["values"],2))
        return bounded_problem(dict(kind=kind,R=R,C=C,P=P,x=x,y=y,beta=beta,V=V,n=n))
    if kind == "transport":
        keys(raw, ("format","kind","states","P","x","y","x_tilde","y_tilde",
                   "region","comparison","intervention","horizon"))
        n = integer(raw["states"],2,MAX_STATES)
        policies = {k:tuple(row(a,2) for a in seq(raw[k],n))
                    for k in ("x","y","x_tilde","y_tilde")}
        region = domain(raw["region"],n)
        comparison = domain(raw["comparison"],n)
        require(len(comparison)>=2 and set(comparison)<=set(region),
                "comparison requires at least two distinct region states")
        a,b = (integer(v,0,1) for v in seq(raw["intervention"],2))
        return bounded_problem(dict(kind=kind,n=n,P=physical(raw["P"],n),region=region,
                    comparison=comparison,intervention=(a,b),
                    horizon=integer(raw["horizon"],0,MAX_HORIZON),**policies))
    raise Invalid("unsupported research kind")

def domain(raw,n):
    require(type(raw) is list and 1<=len(raw)<=n,"empty or oversized domain")
    a=tuple(integer(i,0,n-1) for i in raw)
    require(tuple(sorted(set(a)))==a,"declared domain must be ordered and unique")
    return a

def physical(raw,n):
    return tuple(tuple(tuple(row(p,n) for p in seq(a,2)) for a in seq(s,2))
                 for s in seq(raw,n))
