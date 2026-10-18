from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[1]
chapters=sorted((R/'chapters').glob('*.md'))
text='\n\n\\newpage\n\n'.join(p.read_text()for p in chapters)
# Citation anchors map each chapter to exact recorded sources; details in the source register.
source=json.load(open(R/'sources/source_register.json'))['sources'];index={r['path']:r['id']for r in source}
source_groups={
'00_scope':['docs/V020_IMPLEMENTATION_INDEX.md'],
'01_x1':['PermanssonResearch/X1/Parameters.lean','PermanssonResearch/X1/TypedModels.lean','PermanssonResearch/X1/Comparison.lean','PermanssonResearch/X1/FiniteOutputs.lean'],
'02_strategies':['PermanssonResearch/X1/MPECertificate.lean'],
'03_autonomy':['PermanssonResearch/MultiAgent/Protocols.lean','PermanssonResearch/MultiAgent/ProductGame.lean','PermanssonResearch/MultiAgent/ProtocolWitnesses.lean'],
'04_robustness':['PermanssonLean/Probability/CommonPartKernel.lean','PermanssonResearch/Quotient/ApproxPrefix.lean','PermanssonResearch/Quotient/ApproxMargin.lean'],
'05_long_run':['PermanssonResearch/Perturbation/ContractiveOccupation.lean','PermanssonResearch/Probability/KantorovichDual.lean','PermanssonResearch/Probability/KantorovichTV.lean'],
'06_solver':['PermanssonResearch/ReverseSolver/ResidenceEvent.lean','PermanssonResearch/ReverseSolver/ResidenceValue.lean','PermanssonResearch/ReverseSolver/ResidenceContracts.lean'],
'07_stationary_families':['PermanssonResearch/ReverseSolver/C11ClassStationaryCertificate.lean','PermanssonResearch/ReverseSolver/C11StationaryFamily.lean','PermanssonResearch/MultipleLimit/FiniteClassInvariantMeasure.lean'],
'08_grammar_economic':['docs/V020_IMPLEMENTATION_INDEX.md'],
'09_specialized':[r['path']for r in source if r['path'].endswith('.pdf')]
}
parts=[]
for p in chapters:
    s=p.read_text();lines=s.split('\n'); group=source_groups.get(p.stem,[])
    if group:
        lines=lines[:2]+['**Source basis:** '+', '.join(index[x] for x in group)+'. Exact references and canonical hashes are in the source register; theorem IDs in this chapter denote the new paper derivations.','']+lines[2:]
    parts.append('\n'.join(lines))
# Short source register in paper, full hash/URL metadata separately.
refs=['# Source references','',
'All repository references below are pinned to `39279799834ae536bda715dedecdc11a32bf6c82`. Full URLs and byte hashes are in `sources/source_register.json` and `SOURCE_REGISTER.md`. These sources establish the pre-existing interfaces and limits. New paper derivations are not attributed to an old source merely because they reuse its definitions.','']
for r in source:
    name=r['path'].replace('PermanssonResearch/','Research / ').replace('PermanssonLean/','Core / ').replace('paper/supporting/specialized_theory/','Specialized source / ')
    # Soft breaks at path separators/underscores for the PDF, preserve literal full path in JSON.
    refs.append('**'+r['id']+'** — '+name.replace('_','\\_')+'\n')
refs+=['','**Analytic background:** Martin Hairer, *Convergence of Markov Processes* (26 May 2021); official mathlib kernel Radon–Nikodym and matrix adjugate documentation. Online documentation is not a substitute for checking the pinned library. Full references are in the companion source register.']
text='\n\n\\newpage\n\n'.join(parts+['\n'.join(refs)])
(R/'MATHEMATICAL_BUILD_SPEC.md').write_text(text)
print('words',len(text.split()),'chapters',len(chapters))
