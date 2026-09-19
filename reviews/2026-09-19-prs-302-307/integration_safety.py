from pathlib import Path
from collections import Counter
import contextlib,hashlib,importlib.util,io,json,re,subprocess,sys

OUT=Path(__file__).parent
ROOT=(OUT.parent/'integration').resolve()
BASE='7e05bfbf'
def sha(b): return hashlib.sha256(b).hexdigest()
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
def old(ref,p): return git('show',f'{ref}:{p}')
def files(ref,p): return [s for s in git('ls-tree','-r','--name-only',ref,'--',p).decode().splitlines()]
def sections(t):
    heads=list(re.finditer(r'^## (.+)$',t,re.M));result={}
    for i,m in enumerate(heads):
        name=m[1]
        if name in {'Context and notation','Problem statement','Original problem statement','Question','Conjecture'}:
            result[name]=t[m.start():(heads[i+1].start() if i+1<len(heads) else len(t))]
    return result
head=git('rev-parse','HEAD').decode().strip()
registry=json.loads((ROOT/'problem_ids.json').read_text())
assert registry==json.loads(old(BASE,'problem_ids.json'))
canonical=[];counts=Counter()
for pid,p in registry.items():
    b=old(BASE,p).decode();c=(ROOT/p).read_text()
    assert b.splitlines()[0]==c.splitlines()[0],pid
    identical=b==c
    target=sections(b)
    if not identical:
        assert target,('changed page without recognized target',pid)
        cs=sections(c)
        for name,value in target.items(): assert cs.get(name)==value,(pid,name)
    status=re.search(r'^\*\*Status:\*\* (.+?)\s*$',c,re.M)[1]
    counts[status]+=1
    canonical.append({'id':pid,'path':p,'unchanged_page':identical,'target_sections':list(target),'target_unchanged':True,'status':status})
proofs=[]
for pid,ref in [('PF-03','origin/pr-audit-303'),('NR-04','origin/pr-audit-304'),('MI-27','origin/pr-audit-306')]:
    p=str(Path(registry[pid]).parent/'lean')
    tracked=files(ref,p)
    selected=[f for f in tracked if f.endswith('.lean') or Path(f).name in {'comparator.json','lakefile.toml','lake-manifest.json','lean-toolchain','STATEMENT-FREEZE.json','IMPLEMENTATION-MAP.json','NUMERICAL_TARGETS.md'}]
    checked={}
    for f in selected:
        v=(ROOT/f).read_bytes();assert v==old(ref,f),f
        checked[f]=sha(v)
    actual={str(f.relative_to(ROOT)) for f in (ROOT/p).rglob('*.lean')}
    assert actual=={f for f in tracked if f.endswith('.lean')},pid
    proofs.append({'id':pid,'pr_ref':ref,'ref_head':git('rev-parse',ref).decode().strip(),'source_contract_pin_file_count':len(selected),'files_sha256':checked,'all_match':True})
trusted=[]
for p in ['tools/lean','docs/lean','.github/workflows','tools/validate_problem_ids.py','tools/update_catalog.py','problem_ids.json','AGENTS.md']:
    for f in files(BASE,p):
        assert (ROOT/f).read_bytes()==old(BASE,f),f
        trusted.append(f)
    assert set(files(BASE,p))==set(files('HEAD',p)),p
spec=importlib.util.spec_from_file_location('integration_update_catalog',ROOT/'tools/update_catalog.py')
mod=importlib.util.module_from_spec(spec)
sys.path.insert(0,str(ROOT/'tools'));spec.loader.exec_module(mod)
captured={};original=Path.write_text;original_argv=sys.argv
def no_write(path,data,*args,**kwargs):
    captured[str(path.relative_to(ROOT))]=data
    return len(data)
log=io.StringIO()
try:
    Path.write_text=no_write
    sys.argv=['update_catalog.py','--base-ref',BASE]
    with contextlib.redirect_stdout(log): mod.main()
finally:
    Path.write_text=original;sys.argv=original_argv
for p,s in captured.items(): assert (ROOT/p).read_text()==s,('catalog drift',p)
status=git('status','--short').decode()
assert head==git('rev-parse','HEAD').decode().strip(),'HEAD changed during audit'
result={'integration_head':head,'base':BASE,'git_status':status,'registry_entries':len(registry),'registry_unchanged':True,'canonical_pages':canonical,'counts':dict(sorted(counts.items())),'open_targets':counts['Open']+counts['Partially resolved'],'proof_projects':proofs,'trusted_files_unchanged':trusted,'generated_indexes_exact':list(captured),'generator_dry_run_log':log.getvalue(),'no_integration_file_writes':True,'scope':'Read-only identity, mathematical target preservation, source/contract/pin correspondence, unchanged trust infrastructure and exact dry-run catalog checks. Separate PR audits establish mathematical and execution correctness.'}
documentation=set(captured)|{'RESOLVED.md','tools/render_problems.py'}
for x in canonical:
    if not x['unchanged_page']:
        p=Path(x['path']);documentation|={str(p),str(p.parent/'problem.tex'),str(p.parent/'problem.pdf')}
result['documentation_and_generated_sha256']={p:sha((ROOT/p).read_bytes()) for p in sorted(documentation)}
(OUT/'integration-safety.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',head,'IDs:',len(registry),'counts:',dict(counts),'catalogs:',len(captured),'trusted files:',len(trusted))
