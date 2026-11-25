"""Research CLI. Run from repository root; no public application registration."""
import argparse
import json
import sys
from pathlib import Path

from .contract import (parse, pack, identity, RECEIPT, require, strict_read,
                       read_result, MAX_RECEIPT_BYTES)
from permansson_app.errors import AppError
from . import regret, kite, discounted, transport, checker

def candidate(raw):
    d=parse(raw)
    producers={"regret":regret.produce,"kite":kite.produce,
               "discounted":discounted.produce,"transport":transport.produce}
    return {"format":RECEIPT,"input_sha256":identity(raw),"kind":d["kind"],
            "result":pack(producers[d["kind"]](d))}

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("command",choices=("regret","kite","discounted","transport","check"))
    p.add_argument("input",type=Path)
    p.add_argument("receipt",nargs="?",type=Path)
    args=p.parse_args(argv)
    try:
        _,raw=strict_read(args.input)
        if args.command=="check":
            require(args.receipt is not None,"receipt required")
            require(args.receipt.stat().st_size <= MAX_RECEIPT_BYTES, "receipt byte budget exceeded")
            _,receipt=read_result(args.receipt)
            out=checker.check(raw,receipt)
        else:
            require(args.receipt is None and type(raw) is dict and raw.get("kind")==args.command,"command/input mismatch")
            receipt=candidate(raw)
            out={"receipt":receipt,"verification":checker.check(raw,receipt)}
        encoded=json.dumps(out,sort_keys=True,indent=2)
        require(len(encoded.encode("utf-8"))<=MAX_RECEIPT_BYTES,"output byte budget exceeded")
        print(encoded)
        return 0
    except (ValueError,TypeError,KeyError,ArithmeticError,OSError,AppError,
            MemoryError,RecursionError) as e:
        print("INVALID: "+str(e),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
