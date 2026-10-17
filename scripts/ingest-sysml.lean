import PropertyKindCalculus.Interchange
import PropertyKindCalculus.Iso80000
open Lean PropertyKindCalculus.Interchange

/-! Read PKC DSL models from OpenSysML's API element form and write each as a Lean module
the kernel re-checks. `PKC_INGEST` names the `.api.json` files (comma-separated; each as
`sysml -convert api-json sysml/PKC.sysml <model>.sysml` writes it); each becomes
`.lake/build/sysml/Generated/<Package>.lean` beside its `PkcModel` JSON, with the citations
the environment cannot honour reported (the script imports the ISO 80000 catalogue; import more
libraries here for models citing them). `scripts/ingest-sysml.sh` runs the whole path. -/

def ingest (path : String) : MetaM Unit := do
  let text ← IO.FS.readFile path
  match ApiJson.read text with
  | .error e => throwError "{path}: {e}"
  | .ok (m, warnings) =>
    for w in warnings do IO.eprintln s!"{path}: {w}"
    IO.FS.createDirAll ".lake/build/sysml/Generated"
    let lean := s!".lake/build/sysml/Generated/{EmitLean.ident m.packageName}.lean"
    IO.FS.writeFile lean (EmitLean.emit m)
    IO.FS.writeFile s!".lake/build/sysml/Generated/{EmitLean.ident m.packageName}.pkc.json" m.toJsonString
    let missing ← Harvest.unverifiedCitations m
    for x in missing do IO.eprintln s!"{path}: {x}"
    IO.println s!"wrote {lean}: {m.kinds.length} kind(s), {m.edges.length} edge(s), \
      {m.modules.length} module(s), {m.relations.length} relation(s), \
      {m.requirements.length} requirement(s), {m.tapes.length} tape(s), \
      {m.tapeMatches.length} match(es); {missing.length} unverified citation(s)"

run_meta do
  let some spec ← IO.getEnv "PKC_INGEST"
    | throwError "set PKC_INGEST to the api-json file(s) to ingest (comma-separated)"
  for p in spec.splitOn "," do
    unless p.isEmpty do ingest p
