"""Reproducible original-six-state C10 exact-rational numerical receipt.

This executable intentionally does NOT claim a kernel-checked Lean receipt:
it creates independent Python numerical evidence for the planned bridge.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import json
import tempfile
from c10_exact_execution import check_input, execute
from c10_verify_receipt import verify_receipt

BASE = [['0','1','0','0','0','0'],
        ['0','1/2','1/6','0','1/3','0'],
        ['0','0','0','1','0','0'],
        ['0','0','1','0','0','0'],
        ['0','0','0','0','1/2','1/2'],
        ['0','0','0','0','1/4','3/4']]


def row_map(changes):
    return [list(changes.get(i, row)) for i,row in enumerate(BASE)]


def six_input():
    full = row_map({1:['0','1','0','0','0','0'],2:['0','1','0','0','0','0']})
    half = row_map({1:['0','1','0','0','0','0'],2:['0','1/2','0','0','1/2','0']})
    tiny = row_map({1:['0','1','0','0','0','0'],2:['0','1/1000','0','0','999/1000','0']})
    uonly = row_map({1:['0','1','0','0','0','0']})
    bonly = row_map({1:['0','0','0','0','1','0'],2:['0','0','0','0','1','0']})
    return {'n':6,'baseline':BASE,'descriptor':[False,False,True,True,True,True],
            'comparison':[1,2],
            'menu':[{'id':k,'matrix':v} for k,v in (
                ('full',full),('half',half),('tiny',tiny),('identity',BASE),
                ('u-only',uonly),('b-only',bonly))]}


def create_golden(folder):
    folder=Path(folder)
    folder.mkdir(parents=True,exist_ok=True)
    raw=six_input()
    receipt=execute(check_input(raw))
    assert verify_receipt(receipt)
    assert [v['margin'] for v in receipt['members']]==['1','1/2','1/1000','0','0','0']
    assert receipt['selected']=='full' and receipt['ties']==['full']
    for name,obj in [('input.json',raw),('receipt.json',receipt)]:
        (folder/name).write_text(json.dumps(obj,sort_keys=True,indent=2)+'\n',encoding='utf-8')
    return receipt


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('folder')
    args=p.parse_args(argv)
    receipt=create_golden(args.folder)
    print(f"C10 six-state rational golden verified: optimum {receipt['optimum']} / input_sha256={receipt['input_sha256']} (not Lean-proved)")

if __name__=='__main__':
    main()