"""Read-only exact-v2/header evidence audit; no compiler invocation."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
O=Path(__file__).resolve().parent;D=O.parents[1]
V1=D/'development/MF14-degree44-statements-v1'
V2=D/'development/MF14-degree44-statements-v2'
L=D/'local-lean';A=D/'development/MF14-degree44-api-plan-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
seal=json.loads((V2/'STAGING-HANDOFF.json').read_text())
assert sha(V2/'STAGING-HANDOFF.json')=='08bf0681f405454e4725e7dfaaaae279a1582abd1c698c2e7bc6e377cc5db3d1'
for p,h in seal['files_sha256'].items():assert sha(V2/p)==h,p
old=json.loads((V1/'STAGING-HANDOFF.json').read_text())
changed=[]
for p,h in old['files_sha256'].items():
    if sha(V2/p)!=h:changed.append(p)
assert changed==['NLA/MF14Degree44/Definitions.lean']
rel=changed[0];v2=(V2/rel).read_text();v1=(V1/rel).read_text()
extra='import Mathlib.Analysis.InnerProductSpace.Defs\n'
assert v2.count(extra)==1 and v2.replace(extra,'',1)==v1
header=json.loads((V2/'HEADER-CHECK.json').read_text())
rp=Path(header['receipt']);assert sha(rp)==header['receipt_sha256']=='820ceae2ddc164184dcc45b3253002eca3a4489d730dcc4149352764accbfb5c'
r=json.loads(rp.read_text())
assert r['completed_modules']==5 and r['failed_modules']==[] and r['blocked_modules']==[]
assert r['threads']==1 and r['memory_cap_mib']==4096 and r['max_compiler_processes']==1
records=[];receipts={};origins=[]
def load(path):
    path=Path(path)
    if str(path) not in receipts:receipts[str(path)]=json.loads(path.read_text())
    return receipts[str(path)]
def actual_origin(path,mod,source_hash,output_hash):
    path=Path(path);record=next(c for c in load(path)['commands'] if c['module']==mod)
    assert record['source_sha256']==source_hash and record['output_sha256']==output_hash
    if record.get('status')=='reused_exact_successful_local_output':
        prior=Path(record['prior_receipt']);assert sha(prior)==record['prior_receipt_sha256']
        return actual_origin(prior,mod,source_hash,output_hash)
    assert record['exit_code']==0
    log=path.parent/(mod+'.log');assert sha(log)==record['log_sha256']
    return {'receipt':str(path),'receipt_sha256':sha(path),'command':record,'log_sha256':sha(log)}
output_by_mod={c['module']:c['output_sha256'] for c in r['commands']}
for c in r['commands']:
    mod=c['module'];rel=mod.replace('.','/')+'.lean'
    project_rel='Challenge.lean' if mod=='MF14Degree44Challenge' else rel
    assert c['source_sha256']==header['source_sha256'][project_rel]==sha(V2/project_rel)==sha(L/rel)
    assert r['source_inputs'][rel]==c['source_sha256']
    output=L/'.lake/build/lib/lean'/(mod.replace('.','/')+'.olean')
    assert sha(output)==c['output_sha256']
    if c.get('status')=='reused_exact_successful_local_output':
        origins.append(actual_origin(rp,mod,c['source_sha256'],c['output_sha256']))
    else:
        assert c['exit_code']==0 and '--threads=1' in c['argv'] and '--memory=4096' in c['argv']
        assert c['argv'][-1]==rel
        log=rp.parent/(mod+'.log');assert sha(log)==c['log_sha256']
        t=log.read_text()
        if mod=='MF14Degree44Challenge':
            assert len(re.findall('warning: declaration uses `sorry`',t))==25
            assert len(t.splitlines())==25
        else:assert t==''
        for dep,h in c['dependency_olean_sha256'].items():assert output_by_mod[dep]==h
    records.append(c)

api=json.loads((A/'MANIFEST.json').read_text())
for p,h in api['files_sha256'].items():assert sha(A/p)==h
for p,h in api['inspected_source_files_sha256'].items():assert sha(Path(p))==h
roots=[(Path('/Users/georgestepaniants/Research/project/lean-verification/.lake/packages/mathlib'),api['pinned_mathlib']),
       (Path('/Users/georgestepaniants/Research/project/lean-verification/.lake/packages/LeanCert'),api['pinned_leancert'])]
pin_records=[]
for root,pin in roots:
    for s,h in api['inspected_source_files_sha256'].items():
        p=Path(s)
        if p.is_relative_to(root):
            rel=str(p.relative_to(root))
            b=subprocess.check_output(['git','show',pin+':'+rel],cwd=root)
            assert hashlib.sha256(b).hexdigest()==h
            pin_records.append({'source':rel,'commit':pin,'sha256':h})
primary=[];W=D/'publication/PF03';ref='e7519c46fd249a6a033bfe5d11c66bf47f7f8885'
for p in ['matrix-functions-and-stability/MF-14/README.md','references/webb-mf14-degree44-2026-09-17/proof.tex']:
    b=subprocess.check_output(['git','show',ref+':'+p],cwd=W)
    assert b==(W/p).read_bytes()
    primary.append({'path':p,'commit':ref,'sha256':hashlib.sha256(b).hexdigest()})
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/pf03_final_referee2',
 'verdict':'APPROVE exact-v2 statements; no mathematical proof acceptance',
 'v2_handoff_sha256':sha(V2/'STAGING-HANDOFF.json'),'v2_file_sha256':seal['files_sha256'],
 'v1_to_v2_only_source_delta':extra.strip(),'header_receipt_sha256':sha(rp),'header_check_sha256':sha(V2/'HEADER-CHECK.json'),
 'actual_commands':records,'reused_original_definition_actual_origins':origins,
 'new_source_compiler_processes_observed':4,'shared_exact_source_output_reused':1,'intentional_challenge_placeholders':25,
 'reviewer_compiler_invocations':0,'api_plan_manifest_sha256':sha(A/'MANIFEST.json'),
 'api_plan_file_sha256':api['files_sha256'],'pinned_source_files_matched':pin_records,
 'canonical_and_primary_git_binding':primary,'github_comparator':'NOT_RUN','count_change':0}
(O/'V2-HEADER-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'verdict':'APPROVE statement gate','audit_sha256':sha(O/'V2-HEADER-AUDIT.json'),
 'fresh_header_compiles':4,'exact_original_dependency_reused':1,'source_import_only_delta':True,
 'primary_and_canonical_git_blobs_match':True,'pinned_api_source_files':len(pin_records)},indent=2))
