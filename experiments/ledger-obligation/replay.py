"""Source-pinned native ledger versus actual Bash/Python observations. No product efficacy claim."""
from pathlib import Path
import subprocess, json, hashlib, os, urllib.request
ROOT=Path.cwd(); OUT=ROOT/'results';OUT.mkdir(exist_ok=True)
REVISIONS={'old':'1775d7fea8474607ad003709df5d57f5db9de384','fixed':'ac1f42ed31bb9ab1861a5d2a18ca257c05fcfaa4','current':'219f133cc93172fea46b08d09edf9b3b6441c0a4'}
MARK='MG_GATE_ORACLE_EXECUTED'
cmd='python3 -c \'print("'+MARK+'")\''
cases=[('clean','printf \'clean\\n\'\n',False),('direct',cmd+'\n',True),('no_bytecode','python3 -B -c \'print("'+MARK+'")\'\n',True),('isolated','python3 -I -c \'print("'+MARK+'")\'\n',True),('warning_option','python3 -W ignore -c \'print("'+MARK+'")\'\n',True),('heredoc_data',"cat <<'EOF'\n"+cmd+"\nEOF\n",False),('literal_backslashes','echo '+chr(92)*2+'\n'+cmd+'\n',True)]
observations=[]
for name,text,expected in cases:
 p=subprocess.run(['bash','--noprofile','--norc','-c',text],capture_output=True,text=True,timeout=10)
 ran=MARK in p.stdout.splitlines();assert p.returncode==0,(name,p.stderr);assert ran==expected,(name,p.stdout)
 observations.append({'case':name,'script':text,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'python_executed':ran,'expected_execution':expected})
(OUT/'bash-oracle.json').write_text(json.dumps(observations,indent=2)+'\n')
# Test actual upstream pure scanner + gate in separate module trees.
results=[]
for label,rev in REVISIONS.items():
 work=ROOT/'work'/label;source=work/'Scripts/Ledger.lean';source.parent.mkdir(parents=True,exist_ok=True)
 data=urllib.request.urlopen(f'https://raw.githubusercontent.com/nasa-jpl/L4YAML/{rev}/Scripts/Ledger.lean').read();source.write_bytes(data)
 git_blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 expected_blob='86a97413e72ab0eec6cce98b690181b4b3163292' if label=='old' else '806659c367a5c62d42f316eb7214198d4a0d9b33'
 assert git_blob==expected_blob,(label,git_blob)
 (OUT/f'{label}-source-identity.json').write_text(json.dumps({'repo':'nasa-jpl/L4YAML','revision':rev,'path':'Scripts/Ledger.lean','git_blob':git_blob,'sha256':hashlib.sha256(data).hexdigest()},indent=2)+'\n')
 (OUT/f'{label}-Ledger.lean').write_bytes(data)
 lit=lambda s:json.dumps(s,ensure_ascii=False)
 lines=['import Scripts.Ledger','open Scripts.Ledger','def frozenLedger : Ledger := { pin := 0, rows := #[] }','def inspect (text : String) : Nat × Nat :=','  let inv : Inventory := { pyFiles := #[], sites := sitesOfText "scripts/probe.sh" text, exes := #[] }','  (inv.sites.size, (check frozenLedger inv).size)']
 for name,text,_ in cases:
  lines+=['#eval do',f'  let (sites, errors) := inspect {lit(text)}',f'  IO.println s!"MG_NATIVE\\t{name}\\t{{sites}}\\t{{errors}}"']
 (work/'Probe.lean').write_text('\n'.join(lines)+'\n');(OUT/f'{label}-Probe.lean').write_text('\n'.join(lines)+'\n')
 env=dict(os.environ);env['LEAN_PATH']=str(work)
 for name,args in [('source',['lean','-o','Scripts/Ledger.olean','Scripts/Ledger.lean']),('probe',['lean','Probe.lean'])]:
  p=subprocess.run(args,cwd=work,env=env,capture_output=True,text=True,timeout=180)
  log=p.stdout+p.stderr;(OUT/f'{label}-{name}.log').write_text(log);assert p.returncode==0,(label,name,log[-4000:])
 for line in log.splitlines():
  if not line.startswith('MG_NATIVE\t'):continue
  _,name,sites,errors=line.split('\t');obs=next(x for x in observations if x['case']==name)
  results.append({'revision_label':label,'revision':rev,'case':name,'detected_sites':int(sites),'gate_errors':int(errors),'native_gate_green':int(errors)==0,'oracle_python_executed':obs['python_executed'],'policy_violation_unlisted_inline':obs['python_executed'],'false_green':obs['python_executed'] and int(errors)==0,'false_refusal':not obs['python_executed'] and int(errors)>0})
 assert len([x for x in results if x['revision_label']==label])==len(cases)
# Full unchanged current CLI over real fixture directories (not just the pure API).
work=ROOT/'work/current';driver=work/'Scripts/Main/CheckScriptsLedger.lean';driver.parent.mkdir(parents=True,exist_ok=True)
data=urllib.request.urlopen(f"https://raw.githubusercontent.com/nasa-jpl/L4YAML/{REVISIONS['current']}/Scripts/Main/CheckScriptsLedger.lean").read()
assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()=='5fa82509224259019cb730575517b2f2b0cc5168'
driver.write_bytes(data);(OUT/'current-CheckScriptsLedger.lean').write_bytes(data)
cli=[]
for name,text,expected in cases:
 fixture=work/'fixtures'/name;(fixture/'scripts').mkdir(parents=True,exist_ok=True)
 (fixture/'scripts/probe.sh').write_text(text);(fixture/'scripts/scripts-ledger.txt').write_text('# open: 0\n');(fixture/'lakefile.lean').write_text('')
 p=subprocess.run(['lean','--run','Scripts/Main/CheckScriptsLedger.lean','-C',str(fixture)],cwd=work,env=env,capture_output=True,text=True,timeout=90)
 assert p.returncode in [0,1],(name,p.stdout,p.stderr)
 (OUT/f'cli-{name}.log').write_text(p.stdout+p.stderr)
 pure=next(x for x in results if x['revision_label']=='current' and x['case']==name)
 assert (p.returncode==0)==pure['native_gate_green'],name
 cli.append({'case':name,'exit':p.returncode,'native_gate_green':p.returncode==0,'python_executed':expected})
(OUT/'native-cli.json').write_text(json.dumps(cli,indent=2)+'\n')
# End-to-end unchanged gate on an exact checkout of the real repository.
upstream=ROOT/'upstream-current';upstream.mkdir(exist_ok=True)
for args in [['git','init','-q',str(upstream)],['git','-C',str(upstream),'fetch','--depth=1','--no-tags','https://github.com/nasa-jpl/L4YAML.git',REVISIONS['current']],['git','-C',str(upstream),'checkout','--detach','FETCH_HEAD']]:
 subprocess.run(args,check=True,capture_output=True,text=True,timeout=120)
assert (upstream/'Scripts/Ledger.lean').read_bytes()==(work/'Scripts/Ledger.lean').read_bytes()
assert (upstream/'Scripts/Main/CheckScriptsLedger.lean').read_bytes()==driver.read_bytes()
repo_runs=[];probe=upstream/'scripts/mathgraph_obligation_probe.sh';assert not probe.exists()
try:
 for name,text in [('baseline',None),('direct',cases[1][1]),('no_bytecode',cases[2][1]),('withdrawal',None)]:
  if text is None:
   if probe.exists():probe.unlink()
  else:probe.write_text(text)
  p=subprocess.run(['lean','--run','Scripts/Main/CheckScriptsLedger.lean','-C',str(upstream)],cwd=work,env=env,capture_output=True,text=True,timeout=90)
  (OUT/f'repository-{name}.log').write_text(p.stdout+p.stderr)
  repo_runs.append({'case':name,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
 assert [x['exit'] for x in repo_runs]==[0,1,0,0],repo_runs
finally:
 if probe.exists():probe.unlink()
assert subprocess.run(['git','-C',str(upstream),'status','--porcelain'],capture_output=True,text=True,check=True).stdout==''
(OUT/'repository-replay.json').write_text(json.dumps({'revision':REVISIONS['current'],'runs':repo_runs,'restored_clean':True,'native_library_oracle':'Pure module plus actual Bash execution','upstream_full_library_build':'NOT_RUN'},indent=2)+'\n')

for label in REVISIONS:
 arm={x['case']:x for x in results if x['revision_label']==label}
 assert arm['clean']['native_gate_green'];assert not arm['direct']['native_gate_green']
 assert all(arm[n]['false_green'] for n in ['no_bytecode','isolated','warning_option'])
 if label=='old': assert arm['literal_backslashes']['false_green'] and arm['heredoc_data']['false_refusal']
 else: assert not arm['literal_backslashes']['native_gate_green'] and arm['heredoc_data']['native_gate_green']
# Prototype independent Check verdict: a native-green gate cannot authorize the frozen
# zero-unlisted-inline obligation when independent execution contradicts it.
for x in results:
 x['independent_check']='FAIL' if x['false_green'] or x['false_refusal'] else 'PASS'
report={'design':'Known historical controls plus three newly constructed option-prefix controls; not a prospective Devin benchmark','obligation':'No unlisted inline Python executes; a frozen empty ledger has pin 0 and no rows','source_mutated':False,'real_repository_control_exit_codes':[x['exit'] for x in repo_runs],'native_cli_cases':cli,'native_arms':len(REVISIONS),'cases_per_arm':len(cases),'results':results,'current_false_greens':sum(x['false_green'] for x in results if x['revision_label']=='current'),'product_status':'Independent obligation-check prototype, not deployed MathGraph Check integration','boundary':'Finite Linux Bash/Python fixtures over actual upstream pure inventory+gate; full unchanged current CLI replayed on seven fixtures; actual full repository gate replayed, not full library/CI build or arbitrary shell equivalence'}
(OUT/'REPORT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'native_rows':len(results),'current_false_greens':report['current_false_greens'],'source_unchanged':True,'status':'BOUNDED_NATIVE_REPLAY_PASS'}))
with (OUT/'SHA256SUMS').open('w') as f:
 for p in sorted(OUT.iterdir()):
  if p.is_file() and p.name!='SHA256SUMS':f.write(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n')
