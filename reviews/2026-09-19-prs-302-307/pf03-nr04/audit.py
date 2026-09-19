from pathlib import Path
import hashlib, json, re, subprocess, zipfile

ROOT=Path(__file__).parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(b): return hashlib.sha256(b).hexdigest()
def git(w,*args): return subprocess.check_output(['git',*args],cwd=w)
def uncomment(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1; i+=2
        elif depth and s[i:i+2]=='-/': depth-=1; i+=2
        elif depth: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i); i=len(s) if j<0 else j
        else: out.append(s[i]); i+=1
    assert depth==0
    return ''.join(out)
results=[]
for tag,pid,proof in [('pf03','PF-03','9625a76780183040186664100e24e0e90d8fcc7d'),('nr04','NR-04','f488b0cfe2175e5e50d439c5a4115accc4b07b6d')]:
    w=ROOT/tag; rel=Path('nonnegative-and-positive-factorizations')/pid/'lean'; p=w/rel
    cfg=json.loads((p/'comparator.json').read_text()); meta=json.loads((p/'formalization.yaml').read_text())
    head=git(w,'rev-parse','HEAD').decode().strip()
    paths=list((p/'NLA').rglob('*.lean'))+[p/'Solution.lean',p/'Challenge.lean']
    modules={str(f.relative_to(p)).removesuffix('.lean').replace('/','.'):f for f in paths}
    closure=set(); stack=['Solution']; external=set(); forbidden=[]; tactics=[]
    while stack:
        mod=stack.pop()
        if mod in closure: continue
        if mod not in modules: external.add(mod); continue
        closure.add(mod); f=modules[mod]; s=uncomment(f.read_text())
        for m in re.findall(r'^import\s+(\S+)',s,re.M): stack.append(m)
        for pat in [r'\bsorry\b',r'\badmit\b',r'^\s*axiom\b',r'\bnative_decide\b',r'\bunsafe\b',r'\bimplemented_by\b',r'\bextern\b']:
            for mt in re.finditer(pat,s,re.M): forbidden.append([mod,pat,s[:mt.start()].count('\n')+1])
        if 'run_tac' in s: tactics.append(mod)
    assert 'Challenge' not in closure
    assert not forbidden,forbidden
    assert cfg['definition_names']==[]
    assert set(cfg['permitted_axioms'])<=ALLOWED
    assert set(cfg['theorem_names'])=={r['declaration'] for r in meta['status']['main_results']}
    for f in paths+[p/'comparator.json',p/'lake-manifest.json',p/'lakefile.toml',p/'lean-toolchain']:
        assert f.read_bytes()==git(w,'show',f'{proof}:{f.relative_to(w)}'),f
    canon=(p.parent/'README.md').relative_to(w)
    old=git(w,'show',f'origin/main:{canon}').decode()
    cur=(w/canon).read_text()
    assert old[old.index('## Context and notation'):]==cur[cur.index('## Context and notation'):]
    runs=[]
    for rr in sorted((ROOT.parent/'ci'/tag).glob('verify-*/result.json')):
        d=json.loads(rr.read_text()); assert d['config']==cfg; assert d['result']=='comparator-accepted'
        missing=[]; mismatches=[]
        for k,v in d['input_sha256'].items():
            f=p/k
            if not f.is_file(): missing.append(k)
            elif sha(f.read_bytes())!=v: mismatches.append(k)
        assert not missing and not mismatches,(missing,mismatches)
        assert d['source_lock_sha256']==sha((w/'tools/lean/source-lock.json').read_bytes())
        log=(rr.parent/'comparator.log').read_text()
        assert 'Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log
        assert log.rstrip().endswith('EXIT_STATUS=0')
        axreports={n:set(a.split(', ')) if a else set() for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)}
        assert all(n in axreports and axreports[n]<=ALLOWED for n in cfg['theorem_names'])
        for fname in ['kernel-controls.log','comparator-controls.log','sandbox.log']:
            assert (rr.parent/fname).read_text().rstrip().endswith('EXIT_STATUS=0'),fname
        assert "Illegal axiom detected: 'sorryAx'" in (rr.parent/'negative-sorry.log').read_text()
        assert 'Illegal axiom detected:' in (rr.parent/'negative-native.log').read_text()
        assert 'native_decide' in (rr.parent/'negative-native.log').read_text()
        runs.append({'result':str(rr),'repository_commit':d['repository_commit'],'input_count':len(d['input_sha256']),'all_inputs_match':True,'source_lock_matches':True,'selected_axiom_reports':len(cfg['theorem_names']),'logs_controls_acceptance':True})
    archives=[]
    for rr in sorted((p/'verification/linux-2026-09-19').glob('*/artifact/*/result.json')):
        d=json.loads(rr.read_text()); assert d['config']==cfg
        changes=[]
        for k,v in d['input_sha256'].items():
            assert sha(git(w,'show',f'{proof}:{rel}/{k}'))==v,k
            if sha((p/k).read_bytes())!=v: changes.append(k)
        side=rr.parents[2]; prov=json.loads((side/'GITHUB-PROVENANCE.json').read_text()); z=side/f'lean-{pid}.zip'
        art=[a for a in prov['artifacts']['artifacts'] if a['name']==f'lean-{pid}']
        assert len(art)==1
        assert art[0]['digest']=='sha256:'+sha(z.read_bytes())
        with zipfile.ZipFile(z) as zf:
            zipnames=[]
            for zi in zf.infolist():
                if zi.is_dir(): continue
                f=side/'artifact'/zi.filename
                assert f.read_bytes()==zf.read(zi),f
                zipnames.append(zi.filename)
        archives.append({'side':side.name,'inputs_bound_to_immutable_proof':len(d['input_sha256']),'current_changed_inputs':changes,'zip_digest_matches_provenance':True,'zip_entries_match_extracted':len(zipnames)})
    results.append({'id':pid,'head':head,'immutable_proof':proof,'canonical_context_statement_unchanged':True,'proof_contract_dependency_sources_unchanged':len(paths)+4,'solution_local_module_closure':sorted(closure),'external_imports':sorted(external),'forbidden_source_matches':forbidden,'metaprogramming_modules_for_manual_review':tactics,'current_ci':runs,'archived_ci':archives})
(ROOT/'audit.json').write_text(json.dumps(results,indent=2)+'\n')
for r in results: print(r['id'],r['head'],'PASS',len(r['solution_local_module_closure']),'local modules;',r['current_ci'][0]['input_count'],'current CI inputs matched')
