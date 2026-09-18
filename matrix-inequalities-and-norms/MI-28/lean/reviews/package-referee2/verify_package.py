#!/usr/bin/env python3
"""Read-only nonauthor package/relocation audit; no external commands or Lean."""
from pathlib import Path, PurePosixPath
from hashlib import sha256
import json, re, gzip, tarfile, io
import jsonschema
B=Path('/private/tmp/nla-lean-next-20260915')
P=B/'MI28-canonical-package-local365'
D=B/'MI28-publication-docs-draft'
S=B/'MI28-local365-source-snapshot'
C=S/'candidate'
EXPECTED='5d0e6ef2afe59b57f0d3185fdf5685343a9db2d59ba5b1a97ecdeab01b160ea5'
reads={}
scan_texts={}
def Hbytes(x): return sha256(x).hexdigest()
def R(p):
 b=p.read_bytes();reads[str(p)]=Hbytes(b);return b

def J(p): return json.loads(R(p))
def H(p): return Hbytes(R(p))
assert H(P/'PACKAGE-MANIFEST.json')==EXPECTED
manifest=J(P/'PACKAGE-MANIFEST.json')
assert len(manifest['files'])==264
for name,digest in manifest['files'].items():
 assert H(P/name)==digest,name
 assert not (P/name).is_symlink(),name
 if not name.endswith('.gz'):scan_texts[name]=R(P/name)
assert {str(x.relative_to(P)) for x in P.rglob('*') if x.is_file()}==set(manifest['files'])|{'PACKAGE-MANIFEST.json'}

im=J(P/'IMPLEMENTATION-MAP.json')
proofs=im['proof_sources_sha256']
assert len(proofs)==52
for n,h in proofs.items():assert H(P/n)==H(C/n)==h,n
assert J(P/'ACTIVE-SOURCE-MANIFEST.json')['source_sha256']==proofs
freeze=J(P/'STATEMENT-FREEZE.json')
for n,h in freeze['frozen_files'].items():assert H(P/n)==h,n
for n in ['HEADERS.json','LICENSE','REUSE-MI24-FURUTA.json']:assert R(P/n)==R(C/n),n
assert len(list(P.rglob('*.lean')))==53
# The actual publication import graph contains precisely the reviewed closure.
graph={}
for n in proofs:
 graph[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+(NLA\.[\w.]+)\s*$',R(P/n).decode(),re.M)]
 for target in graph[n]:assert target in proofs,(n,target)
 assert not re.search(r'^import\s+Challenge\b',R(P/n).decode(),re.M),n
seen=set();todo=['Solution.lean']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(graph[n])
assert seen==set(proofs),(set(proofs)-seen)

# All twenty bindings, source hashes and frozen headers are unchanged from the
# independently checked draft; no new proof or statement edit is accepted here.
assert R(P/'IMPLEMENTATION-MAP.json')==R(D/'IMPLEMENTATION-MAP.json')
assert R(P/'comparator.json')==R(C/'comparator.json')
headers=J(P/'HEADERS.json')
assert len(headers)==len(im['contracts'])==20
for row in im['contracts']:
 assert headers[row['declaration']]['header'] in R(P/row['file']).decode()
 assert H(P/row['file'])==row['source_sha256']
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']:assert R(P/n)==R(D/n),n
integration=J(D/'INTEGRATION-REQUIREMENTS.json')
for x in integration['archive_historical_records']:
 assert H(P/x['destination'])==x['sha256']==H(C/x['source'])
assert not (P/'IMPLEMENTATION-PLAN.md').exists()

f=J(P/'formalization.yaml');df=J(D/'formalization.yaml')
schema=J(P/'source-inputs/standards/v0.4.schema.json')
jsonschema.validators.validator_for(schema)(schema).validate(f)
assert f['status']['whole_problem_verified'] is False
assert f['status']['completed_original_targets']==0
assert f['verification']['count_change']==0
assert f['verification']['GitHub_Comparator']=={'status':'not run for MI28'}
assert f['verification']['local_Lean']==df['status']['local_proof']
assert f['verification']['local_diagnostic']==df['status']['local_type_diagnostic']
assert f['verification']['independent_reviews']=={'statement':2,'final':2,'record':'reviews/INDEX.json'}
x=json.loads(json.dumps(f));del x['verification'];del x['status']['whole_problem_verified'];del x['status']['completed_original_targets']
assert x==df
state=J(P/'STATE.json');old_state=J(D/'STATE.json')
state_deltas={k for k in set(state)|set(old_state) if state.get(k)!=old_state.get(k)}
assert state_deltas=={'publication_documentation','publication','prepared_at'}
assert state['GitHub_Comparator']=='NOT RUN'
assert state['GitHub_default_kernel_sandbox_negative_controls']=='NOT RUN'
assert state['standalone_Lake_execution']=='NOT RUN'
assert state['accepted_Lean_verification_count_change']==state['new_mathematical_resolution_count_change']==0

relocations=J(P/'verification/RETAINED-PATHS.json')
assert len(relocations)==251
source_map={r['source']:r for r in relocations}
assert len(source_map)==len(relocations)
derived=[]
for r in relocations:
 payload=R(P/r['destination']);assert Hbytes(payload)==r['sha256']
 if r['encoding']=='gzip':
  payload=gzip.decompress(payload);scan_texts[r['destination']+' [decoded]']=payload
 else:assert r['encoding']=='identity'
 assert Hbytes(payload)==r['decoded_sha256']
 assert H(Path(r['source']))==r['source_sha256']
 if r.get('derived_current_status_update'):
  derived.append(r['destination']);assert r['original_destination_sha256']==r['source_sha256']
 else:assert payload==R(Path(r['source'])),r['destination']
assert set(derived)=={'README.md','formalization.yaml','STATE.json'}
local=J(P/'verification/local365/LOCAL-COMPLETE.json')
assert H(P/'verification/local365/LOCAL-COMPLETE.json')=='94a60f882bd02a9333db7e92a15b7045404b8ed43222dab744610abe60e01f39'
assert local['sources']==proofs
for source,digest in local['retained_original_evidence'].items():
 assert source in source_map and source_map[source]['source_sha256']==digest,source
comparison=J(P/'verification/type-diagnostics-366/COMPARISON.json')
assert H(P/'verification/type-diagnostics-366/COMPARISON.json')=='54cbbfe2497939fe78fbff9dd499b99c961316f6a22e36a98ba0fa7cc0256d45'
assert comparison['Comparator_executed'] is False

archive_entries=J(P/'reviews/INDEX.json')+J(P/'verification/history/INDEX.json')
assert len(archive_entries)==7
archive_payload_count=0
for row in archive_entries:
 assert H(P/row['archive'])==row['archive_sha256']
 with tarfile.open(fileobj=io.BytesIO(R(P/row['archive'])),mode='r:gz') as t:
  observed={}
  for member in t.getmembers():
   assert member.isfile() and not member.issym() and not member.islnk()
   rel=PurePosixPath(member.name);assert not rel.is_absolute() and '..' not in rel.parts
   assert member.name not in observed
   payload=t.extractfile(member).read();observed[member.name]=Hbytes(payload)
   assert Hbytes(payload)==H(Path(row['source_directory'])/member.name)
   assert not member.name.endswith(('.olean','.ilean','.pdf','.so','.o','.a','.zip'))
   scan_texts[row['archive']+'!'+member.name]=payload
  assert observed==row['payload_sha256'],row['archive']
  archive_payload_count+=len(observed)
# No extraction or archive copies are made by this audit.

# The compact fresh-public-query file is a derived projection, not falsely
# represented as the untouched raw record. Recreate every retained field.
original=B/'MI28-PREPUBLICATION-REFRESH-20260918.json'
raw=J(original);compact=J(P/'verification/public-scope/PREPUBLICATION-REFRESH.json')
expected_compact={
 'time':raw['time'],'original_record_sha256':H(original),
 'main':json.loads(raw['observations'][0]['stdout'])['sha'],
 'canonical_blob':json.loads(raw['observations'][1]['stdout'])['sha'],
 'target_PRs':json.loads(raw['observations'][2]['stdout']),
 'head_PRs':json.loads(raw['observations'][3]['stdout']),
 'commands':[{'argv':r['argv'],'exit_code':r['exit_code']} for r in raw['observations']],
 'scope':'Exact main/canonical/PR observations; unrelated commit metadata and redundant canonical bytes omitted.'}
assert compact==expected_compact
pub=J(P/'PUBLIC-SCOPE.json')
assert compact['original_record_sha256']==pub['origin_sha256']
assert compact['main']==pub['upstream_main']
assert compact['target_PRs']==pub['targeted_all_state_MI28_PR_results']
assert compact['head_PRs']==pub['targeted_formalization_head_results']

# Check current human-facing Markdown links; sealed historic excerpts retain
# their own former roots and are explicitly classified as history.
current_md=['README.md','NUMERICAL_TARGETS.md','REVIEW-INDEX.md','PROOF-REVIEWER-MAP.md','verification/README.md']
links=[]
for name in current_md:
 text=R(P/name).decode()
 for link in re.findall(r'\[[^\]]+\]\(([^)]+)\)',text):
  if re.match(r'^[A-Za-z][A-Za-z0-9+.-]*:',link) or link.startswith('#'):continue
  target=link.split('#')[0]
  assert (P/name).parent.joinpath(target).exists(),(name,link)
  links.append((name,link))
# Current metadata's local file bindings are tested explicitly. Historical
# absolute command paths are authenticated using the relocation table above.
for row in f['status']['main_results']:assert (P/row['file']).is_file()
for row in J(P/'REVIEW-INDEX.json')['statement_reviews']+J(P/'REVIEW-INDEX.json')['final_source_reviews']:
 assert H(P/row['manifest'])==row['manifest_sha256']
 if 'report' in row:assert (P/row['report']).is_file()
for section in ['local_proof','local_type_diagnostic']:
 row=f['status'][section];key='complete_record' if section=='local_proof' else 'record'
 assert H(P/row[key])==row[key+'_sha256']
# Scan all public plain/decoded/archive bytes for email-shaped identifiers.
email=re.compile(rb'(?<![A-Za-z0-9_.+%-])[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
email_locations=[]
for name,payload in scan_texts.items():
 if email.search(payload):email_locations.append(name)
assert not email_locations,email_locations

print(json.dumps({
 'verdict':'PASS','scope':'Independent nonauthor read-only canonical package integrity/schema/relocation review; no Lean, Lake, kernel, Comparator, Git or network run.',
 'package_manifest_sha256':EXPECTED,'payload_files':len(manifest['files']),
 'proof_modules_unchanged':len(proofs),'reachable_proof_import_closure':len(seen),
 'frozen_contracts_unchanged':20,'source_relocations_authenticated':len(relocations),
 'retained_local365_original_evidence_files':len(local['retained_original_evidence']),
 'archive_packets_authenticated_in_memory':len(archive_entries),'archived_members_authenticated':archive_payload_count,
 'derived_metadata_files':derived,'derived_public_refresh':'Exact retained-field projection authenticated; raw record not represented as co-located.',
 'current_markdown_links_resolved':len(links),'email_scan':'No email-shaped identifier in plain, gzip-decoded or archived public payloads',
 'compiler_and_Comparator_executions':0,'proof_mutations':0,'count_change':0,
 'pending':['Root canonical entrypoint execution','Final GitHub Linux Comparator/kernel/sandbox/negative controls and exact commit/run binding'],
 'files_hashed':len(reads)
},indent=2))
