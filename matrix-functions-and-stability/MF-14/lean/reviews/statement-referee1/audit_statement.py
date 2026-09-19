"""Independent bounded statement/data-source audit; invokes no Lean/compiler."""
from pathlib import Path
import ast,datetime,hashlib,json,re

O=Path(__file__).resolve().parent
D=O.parents[1]
P=D/'development/MF14-degree44-statements-v1'
R=D/'publication/PF03/references/webb-mf14-degree44-2026-09-17'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
handoff=json.loads((P/'STAGING-HANDOFF.json').read_text())
for p,h in handoff['files_sha256'].items():
    assert sha(P/p)==h,p
inputs=json.loads((P/'SOURCE-INPUTS.json').read_text())
for p,h in inputs['inputs_sha256'].items():
    assert sha(D.parent/p)==h,p
assert sha(P/'NLA/MF14/Definitions.lean')==sha(D/'local-lean/NLA/MF14/Definitions.lean')
challenge=(P/'Challenge.lean').read_text()
names=re.findall(r'^theorem (\w+)',challenge,re.M)
config=json.loads((P/'comparator.json').read_text())
assert len(names)==25 and len(set(names))==25
assert config['theorem_names']==['NLA.MF14Degree44.'+n for n in names]
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert len(re.findall(r'^  sorry$',challenge,re.M))==25
assert not (P/'Solution.lean').exists()
lean_paths=sorted(P.rglob('*.lean'))
for p in lean_paths:
    t=p.read_text()
    if p.name!='Challenge.lean':
        assert not re.search(r'^\s*(theorem|lemma|axiom)\s',t,re.M),p
        assert not re.search(r'\bsorry\b|\badmit\b|native_decide|implemented_by',t),p
    assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',t),p

# Literal scalar cofactors were copied faithfully; no JSON verdict is consumed.
deg=(P/'NLA/MF14Degree44/Degeneration.lean').read_text()
symbolic=json.loads((R/'verification/symbolic_certificate.json').read_text())
scalar_defs=[]
for k in range(1,6):
    m=re.search(r'def syzygyCoefficient'+str(k)+r' \([^\n]*\) : ℂ :=\n(.*?)(?=\n\ndef)',deg,re.S)
    assert m,k
    actual=re.sub(r'\s+','',m.group(1))
    expected=re.sub(r'\s+','',symbolic['E_s_cofactors'][k-1])
    assert actual==expected,k
    scalar_defs.append(hashlib.sha256(actual.encode()).hexdigest())

# Evaluate the compact INTEGER polynomial table exactly from its transparent
# source text; this is data correspondence, not the fderiv proof obligation.
def add(a,b):
    out=a.copy()
    for k,v in b.items():out[k]=out.get(k,0)+v
    return {k:v for k,v in out.items() if v}
def mul(a,b):
    out={}
    for i,u in a.items():
        for j,v in b.items():out[i+j]=out.get(i+j,0)+u*v
    return {k:v for k,v in out.items() if v}
env={'X':{1:1}}
def expr(s):
    def ev(n):
        if isinstance(n,ast.Constant) and isinstance(n.value,int):return {0:n.value} if n.value else {}
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {k:-v for k,v in ev(n.operand).items()}
        if isinstance(n,ast.BinOp):
            a=ev(n.left)
            if isinstance(n.op,ast.Pow):
                assert isinstance(n.right,ast.Constant) and isinstance(n.right.value,int) and n.right.value>=0
                out={0:1}
                for _ in range(n.right.value):out=mul(out,a)
                return out
            b=ev(n.right)
            if isinstance(n.op,ast.Add):return add(a,b)
            if isinstance(n.op,ast.Sub):return add(a,{k:-v for k,v in b.items()})
            if isinstance(n.op,ast.Mult):return mul(a,b)
        raise AssertionError(ast.dump(n))
    return ev(ast.parse(s.strip().replace('^','**'),mode='eval').body)
family=(P/'NLA/MF14Degree44/Family.lean').read_text()
body=family.split('def integerDerivativeColumns',1)[1].split('\ndef integerJacobian',1)[0]
for name,term in re.findall(r'  let (\w+)(?: : Polynomial ℤ)? := ([^\n]+)',body):env[name]=expr(term)
literal=body.split('![',1)[1].rsplit(']',1)[0]
cols=[expr(s) for s in literal.split(',')]
assert len(cols)==45 and max(max(p,default=0) for p in cols)<=44
table=[[cols[j].get(i,0) for j in range(45)] for i in range(45)]
certificate=json.loads((R/'verification/independent-degree44-certificate.json').read_text())
assert table==certificate['integer_jacobian']
point_text=family.split('def basePoint',1)[1].split('/--',1)[0]
ones=sorted(int(n) for n in re.findall(r'i = (\d+)',point_text))
assert ones==[0,22,32,34,35,44]
assert [1 if i in ones else 0 for i in range(45)]==certificate['parameter_point']
assert len(certificate['parameter_order'])==45
assert re.findall(r'parameterIndex (\d+) \(by decide\)',family)==['9','13','16','21','24','30','36','2']

report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewer':'/root/pf03_final_referee2','scope':'Independent statement/source correspondence; no proof or compiler execution',
 'verdict':'Static checks PASS; final statement approval awaits root exact-header receipt',
 'packet_sha256':handoff['files_sha256'],'handoff_sha256':sha(P/'STAGING-HANDOFF.json'),
 'source_inputs_sha256':inputs['inputs_sha256'],'theorem_contracts':names,
 'original_definitions_match_shared':True,'all_five_literal_cofactors_match_source':True,
 'normalized_cofactor_sha256':scalar_defs,'integer_derivative_table_entries_matched':2025,
 'integer_table_degree_bound_checked':44,'actual_derivative_proved_by_this_audit':False,
 'base_point_one_indices':ones,'stored_parameter_order':certificate['parameter_order'],
 'no_implementation_or_solution':True,'no_compiler_run_by_reviewer':True,
 'exact_maximum47_not_approved_as_completed':True,
 'pinned_review_protocol_sha256':sha(D/'publication/PF03/docs/lean/REVIEW.md')}
(O/'STATIC-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'static_audit':'PASS','contracts':len(names),'matched_table_entries':2025,'cofactors':5,
 'audit_sha256':sha(O/'STATIC-AUDIT.json'),'handoff_sha256':sha(P/'STAGING-HANDOFF.json')},indent=2))
