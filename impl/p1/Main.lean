import Paralean

open Lean Paralean System

def usage : String := "usage:
  paralean capture  --store DIR --ws NAME --root DIR [--targets JSON] [--remote 1] FILE...
  paralean replay   --store DIR [--isolated 1] [--include-rejected 1] [--ws NAME]
  paralean export   --store DIR --out DIR [--mathlib DIR] [--ws a,b]
  paralean validate --store DIR                  (receipts; key in PARALEAN_RECEIPT_KEY)
  paralean stats | contract --names a,b | dump --decl ID | merge --into DIR --from DIR
  paralean fasync --file FAsync.lean --store DIR
  paralean copy-init --copy DIR --author NAME | copy-publish --copy DIR FILE... |
           copy-sync --copy DIR | copy-pull --copy DIR --from DIR | copy-hash --copy DIR FILE...
  paralean publish-all --store DIR --file F [--out PATH]
"

/-- `B/Part1.lean` ↦ `B.Part1`. -/
def moduleOfPath (rel : String) : Name :=
  let rel := if rel.endsWith ".lean" then (rel.dropEnd 5).toString else rel
  (rel.splitOn "/").foldl (fun n c => Name.mkStr n c) .anonymous

partial def parseFlags (args : List String) (acc : Std.HashMap String String := {}) (rest : Array String := #[]) :
    Std.HashMap String String × Array String :=
  match args with
  | k :: v :: tl => if k.startsWith "--" then parseFlags tl (acc.insert (k.drop 2).toString v) rest
                    else parseFlags (v :: tl) acc (rest.push k)
  | [k] => (acc, rest.push k)
  | [] => (acc, rest)

unsafe def main (args : List String) : IO UInt32 := do
  -- The base library must be the one this binary was built against: a different
  -- toolchain's `Init.olean` fails with "incompatible header" much later.
  let sysroot ← match ← IO.getEnv "PARALEAN_SYSROOT" with
    | some d => pure (FilePath.mk d)
    | none => findSysroot
  let leanBin := sysroot / "bin" / "lean"
  let gh ← try
      pure (← IO.Process.output { cmd := leanBin.toString, args := #["--githash"] }).stdout.trimAscii.toString
    catch _ => pure ""
  unless gh == Lean.githash do
    IO.eprintln s!"paralean: the Lean sysroot {sysroot} is commit '{gh}', but this binary was built \
      with {Lean.githash}. Put the pinned toolchain first (ELAN_TOOLCHAIN=leanprover/lean4-nightly:nightly-2026-10-03, \
      or source impl/p1/scripts/env.sh) or set PARALEAN_SYSROOT."
    return 2
  -- this library's own oleans (for `Paralean.Remote`, injected in transparent-workspace mode)
  let app ← IO.appPath
  let libDir : FilePath := match ← IO.getEnv "PARALEAN_LIB" with
    | some d => d
    | none => ((app.parent.bind (·.parent)).getD ".") / "lib" / "lean"
  initSearchPath sysroot [libDir]
  -- process-wide elaborator hooks (no import into user environments)
  if (← IO.getEnv "PARALEAN_NO_HOOKS").isNone then Hooks.install
  enableInitializersExecution
  match args with
  | "capture" :: rest =>
    let (flags, files) := parseFlags rest
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    let some ws := flags["ws"]? | IO.eprintln usage; return 2
    let root : FilePath := flags.getD "root" "."
    let store : Store := { root := storeDir }
    let targets : Array TargetContract ← match flags["targets"]? with
      | some p => do
        match Json.parse (← IO.FS.readFile p) >>= fromJson? with
        | .ok t => pure t
        | .error e => throw <| IO.userError s!"bad targets file: {e}"
      | none => pure #[]
    let mut bad := 0
    for f in files do
      IO.println s!"capture {ws}:{f}"
      let r ← captureFile store ws f (root / f) (moduleOfPath f) (log := IO.println) (targets := targets)
        (materialize? := some (materialize store)) (remote := flags["remote"]? == some "1")
      let rejects := r.diags.filter (·.severity == "reject")
      IO.println s!"  => {r.groups.size} groups, {r.skipped.size} skipped, {r.diags.size} diagnostics ({rejects.size} reject)"
      for d in r.diags do IO.println s!"  {d}"
      bad := bad + rejects.size
    return if bad == 0 then 0 else 1
  | "replay" :: rest =>
    let (flags, _) := parseFlags rest
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    let audit := flags["include-rejected"]? == some "1"
    let store : Store := { root := storeDir, auditRead := audit }
    let files ← store.currentFiles
    let files := match flags["ws"]? with
      | some w => files.filter (·.workspace == w)
      | none => files
    -- audit mode: also validate groups that capture rejected (never published)
    let files := if flags["include-rejected"]? == some "1" then
        files.map fun f => { f with groups := f.groups ++ f.rejected } else files
    let cat ← Catalog.load store files
    let gids := cat.order
    let imports := gids.foldl (fun acc g => (cat.get! g).capsule.imports.foldl
      (fun acc m => if acc.contains m then acc else acc.push m) acc) #[]
    let conservative := flags["conservative"]? == some "1"
    let t0 ← IO.monoMsNow
    let sr ← sourceReplay cat gids imports (conservative := conservative)
      (materialize? := some (materialize store))
    let t1 ← IO.monoMsNow
    let srOk := sr.results.filter (·.ok)
    let nMat := (sr.results.filter (·.materialized)).size
    if nMat > 0 then
      IO.println s!"materialized: {nMat} initializer groups imported as stock-built modules"
    IO.println s!"source replay: {srOk.size}/{gids.size} groups reproduce their declaration ID ({t1 - t0} ms)"
    for r in sr.results do
      for d in r.diags do IO.println s!"  {d}"
    let (kr, _) ← kernelReplay store cat gids sr
    let t2 ← IO.monoMsNow
    let krOk := kr.filter (·.ok)
    let nAdded := kr.foldl (· + ·.added) 0
    let nReal := kr.foldl (· + ·.realized) 0
    IO.println s!"kernel replay: {krOk.size}/{gids.size} groups accepted; {nAdded} declarations added, {nReal} reserved names re-realized ({t2 - t1} ms)"
    for r in kr do
      for d in r.diags do IO.println s!"  {d}"
    if flags["isolated"]? == some "1" then
      let mut nIso := 0
      let mut fails := #[]
      for gid in gids do
        let clo ← match cat.closure #[gid] with
          | .ok c => pure c
          | .error e => throw <| IO.userError e
        let sr ← sourceReplay cat clo imports (materialize? := some (materialize store))
        let r := sr.results.back!
        if r.ok then nIso := nIso + 1 else fails := fails.push (gid, r.diags)
      IO.println s!"isolated replay (exact deps only): {nIso}/{gids.size}"
      -- retry each failure with the maximal capsule: every earlier group of the same file
      let mut fixed := 0
      for (g, ds) in fails do
        let gr := cat.get! g
        let idx := (cat.order.idxOf? g).getD 0
        let prefix_ := (cat.order.extract 0 idx).filter fun h =>
          (cat.get! h).capsule.workspace == gr.capsule.workspace && (cat.get! h).capsule.file == gr.capsule.file
        let ok ← match cat.closure (prefix_.push g) with
          | .ok clo => do
            let sr ← sourceReplay cat clo imports (materialize? := some (materialize store))
            pure ((sr.results.find? (·.gid == g)).any (·.ok))
          | .error _ => pure false
        if ok then fixed := fixed + 1
        -- a root failure has no failing dependency; others cascade from one
        let isRoot := !(gr.deps ++ gr.feDeps).any fun d => fails.any (·.1 == d)
        IO.println s!"  needs larger capsule: {gr.capsule.file}:{gr.capsule.startLine} {g.take 8} \
          [{if isRoot then "root" else "cascade"}] (file-prefix capsule: {if ok then "fixes it" else "still fails"})"
        for d in ds.toList.take 2 do IO.println s!"    {d}"
      unless fails.isEmpty do
        IO.println s!"larger capsule (same-file prefix) fixes {fixed}/{fails.size} isolated failures"
    return 0
  | "dump" :: rest =>
    let (flags, _) := parseFlags rest
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    let store : Store := { root := storeDir }
    let some declId := flags["decl"]? | IO.eprintln usage; return 2
    let bytes ← store.getObject declId
    let nameOf (r : Ref) : Except String Name := pure (Name.mkSimple (toString r))
    let unwire : UnwireCtx := { selfLocal := fun i => some (Name.mkSimple s!"#{i}"),
                                 dep := fun id i => some ((id.take 12).toString, Name.mkSimple s!"#{i}") }
    match decodeGroup bytes unwire nameOf with
    | .error e => IO.eprintln e; return 1
    | .ok dg =>
      for (l, c, ci) in dg.members do
        if flags["member"]?.all (· == toString l) then
          IO.println s!"== {l} ({c})\n  type: {ci.type}\n  value: {ci.value?.getD (mkConst `none)}"
      return 0
  | "export" :: rest =>
    let (flags, _) := parseFlags rest
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    let some out := flags["out"]? | IO.eprintln usage; return 2
    let store : Store := { root := storeDir }
    let files ← store.currentFiles
    let files := match flags["ws"]? with
      | some w => files.filter fun f => (w.splitOn ",").contains f.workspace
      | none => files
    let cat ← Catalog.load store files
    let mathlib? := flags["mathlib"]?.map FilePath.mk
    -- rule 4 renames, if this store carries publication records (working copies)
    let recs ← store.pubs
    let ren := renamesOf (← metasFor store recs) recs
    -- the plan (conflict check, layout) sees the rendered names
    let cat := { cat with metas := cat.metas.fold (fun m k g => m.insert k (renamedGroup ren g)) {} }
    let (plan, bytes) ← writeExport cat cat.order out mathlib? ren
    IO.println s!"export: {plan.modules.size} modules, {cat.order.size} groups, {bytes} bytes of source"
    for m in plan.modules do
      IO.println s!"  {m.name}: {m.groups.size} groups; imports {m.imports}"
    for d in plan.diags do IO.println s!"  {d}"
    if plan.diags.any (·.severity == "reject") then return 1
    let (ok, log, ms) ← runBuild out
    IO.println s!"stock lake build: {if ok then "OK" else "FAILED"} ({ms} ms)"
    unless ok do IO.println log; return 1
    let (nv, ne, ds) ← verifyExport cat plan out ren
    let nd := cat.order.size - ne
    IO.println s!"verify: {nv}/{nd} declaration groups identical in the stock-built oleans; {ne} effect-only groups (build-checked)"
    for d in ds do IO.println s!"  {d}"
    return if nv == nd then 0 else 1
  | "stats" :: rest =>
    let (flags, _) := parseFlags rest
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    let store : Store := { root := storeDir }
    let files ← store.currentFiles
    let cat ← Catalog.load store files
    let mut caps : Array Nat := #[]
    let mut texts : Array Nat := #[]
    let mut encs : Array Nat := #[]
    let mut codes : Std.HashMap String Nat := {}
    let mut ratios : Array Float := #[]
    let mut big : Array String := #[]
    for gid in cat.order do
      let g := cat.get! gid
      let cb := (renderCapsule g (relocatedDepsOf cat g true)).utf8ByteSize
      caps := caps.push cb
      texts := texts.push g.capsule.text.utf8ByteSize
      encs := encs.push g.encSize
      let ratio := cb.toFloat / (max 1 g.capsule.text.utf8ByteSize).toFloat
      ratios := ratios.push ratio
      if ratio > 16 then
        big := big.push s!"{g.capsule.file}:{g.capsule.startLine} ratio {ratio.round} \
          ({cb} B capsule / {g.capsule.text.utf8ByteSize} B command; {g.capsule.scopeCmds.size} scope cmds, \
          {g.capsule.localEffects.size} local effects, {g.capsule.opens.size} opens)"
    for f in files do
      for d in f.diags do
        codes := codes.insert s!"{d.severity}:{d.code}" (codes.getD s!"{d.severity}:{d.code}" 0 + 1)
    let rejected := files.foldl (· + ·.rejected.size) 0
    let skipped := files.foldl (· + ·.skipped.size) 0
    let sorted (a : Array Nat) := a.qsort (· < ·)
    let med (a : Array Nat) := if a.isEmpty then 0 else (sorted a)[a.size / 2]!
    let p95 (a : Array Nat) := if a.isEmpty then 0 else (sorted a)[(a.size * 95) / 100]!
    let mx (a : Array Nat) := a.foldl max 0
    let sum (a : Array Nat) := a.foldl (· + ·) 0
    let j := Json.mkObj [
      ("groups", toJson cat.order.size), ("rejected", toJson rejected), ("skipped", toJson skipped),
      ("capsuleBytes", Json.mkObj [("sum", toJson (sum caps)), ("median", toJson (med caps)),
        ("p95", toJson (p95 caps)), ("max", toJson (mx caps))]),
      ("commandBytes", Json.mkObj [("sum", toJson (sum texts)), ("median", toJson (med texts)),
        ("max", toJson (mx texts))]),
      ("encodingBytes", Json.mkObj [("sum", toJson (sum encs)), ("median", toJson (med encs)),
        ("max", toJson (mx encs))]),
      ("ratio", let rs := ratios.qsort (· < ·)
        Json.mkObj [("p50", toJson (if rs.isEmpty then 0 else rs[rs.size / 2]!)),
                    ("p95", toJson (if rs.isEmpty then 0 else rs[(rs.size * 95) / 100]!))]),
      ("aboveP95Bound", toJson big),
      ("diagnostics", toJson (codes.toList.map fun (k, v) => (k, v)))]
    IO.println s!"STATS {j.compress}"
    return 0
  | "contract" :: rest =>
    let (flags, _) := parseFlags rest
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    let some names := flags["names"]? | IO.eprintln usage; return 2
    let store : Store := { root := storeDir }
    let cat ← Catalog.load store (← store.currentFiles)
    let mut out : Array TargetContract := #[]
    for n in names.splitOn "," do
      let nm := n.toName
      for gid in cat.order do
        for m in (cat.get! gid).members do
          if m.name == nm then out := out.push { name := nm, typeHash := m.typeHash }
    IO.println (toJson out).pretty
    return 0
  | "merge" :: rest =>
    -- union of two stores' immutable records (models anti-entropy after a partition)
    let (flags, _) := parseFlags rest
    let some into := flags["into"]? | IO.eprintln usage; return 2
    let some src := flags["from"]? | IO.eprintln usage; return 2
    let a : Store := { root := into }
    let b : Store := { root := src }
    a.init
    for e in ← (b.root / "objects").readDir do
      let bytes ← IO.FS.readBinFile e.path
      let _ ← a.putObject bytes
    for e in ← (b.root / "meta").readDir do
      IO.FS.writeFile (a.root / "meta" / e.fileName) (← IO.FS.readFile e.path)
    if ← (b.root / "audit").pathExists then
      a.audit.init
      for e in ← (b.root / "audit" / "objects").readDir do
        let _ ← a.audit.putObject (← IO.FS.readBinFile e.path)
      for e in ← (b.root / "audit" / "meta").readDir do
        IO.FS.writeFile (a.root / "audit" / "meta" / e.fileName) (← IO.FS.readFile e.path)
    for (_, r) in ← b.fileRecs do
      let _ ← a.putFileRec r
    for sub in ["receipts", "pubs"] do
      if ← (b.root / sub).pathExists then
        IO.FS.createDirAll (a.root / sub)
        for e in ← (b.root / sub).readDir do
          IO.FS.writeFile (a.root / sub / e.fileName) (← IO.FS.readFile e.path)
    return 0
  | "fasync" :: rest =>
    let (flags, _) := parseFlags rest
    let some file := flags["file"]? | IO.eprintln usage; return 2
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    for a in [true, false] do
      IO.println s!"observe Elab.async={a}:"
      let (rep, _) ← FAsync.observe file a
      for l in rep do IO.println l
    IO.println "forged publication, then validator:"
    for l in ← FAsync.forge file storeDir do IO.println l
    return 0
  | "validate" :: rest =>
    let (flags, _) := parseFlags rest
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    let key := (← IO.getEnv "PARALEAN_RECEIPT_KEY").getD ""
    let (n, refused) ← validateStore { root := storeDir } key (log := IO.println)
    IO.println s!"validate: {n} new receipts; {refused.size} refused"
    return 0
  | "copy-init" :: rest =>
    let (flags, _) := parseFlags rest
    let some dir := flags["copy"]? | IO.eprintln usage; return 2
    let some author := flags["author"]? | IO.eprintln usage; return 2
    copyInit dir author
    return 0
  | "copy-publish" :: rest =>
    let (flags, files) := parseFlags rest
    let some dir := flags["copy"]? | IO.eprintln usage; return 2
    for f in files do
      let ps ← copyPublish dir f (log := IO.println)
      IO.println s!"published {ps.size} group(s) from {f}"
    return 0
  | "copy-sync" :: rest =>
    let (flags, _) := parseFlags rest
    let some dir := flags["copy"]? | IO.eprintln usage; return 2
    let _ ← copySync dir (log := IO.println)
    return 0
  | "copy-pull" :: rest =>
    let (flags, _) := parseFlags rest
    let some dir := flags["copy"]? | IO.eprintln usage; return 2
    let some other := flags["from"]? | IO.eprintln usage; return 2
    let _ ← copyPull dir other (log := IO.println)
    return 0
  | "copy-hash" :: rest =>
    let (flags, files) := parseFlags rest
    let some dir := flags["copy"]? | IO.eprintln usage; return 2
    let store : Store := { root := FilePath.mk dir / "store" }
    for f in files do IO.println s!"{f} {← projectionHash store f}"
    return 0
  | "publish-all" :: rest =>
    -- measurement helper: publish every current group of a store as one file, in order
    let (flags, _) := parseFlags rest
    let some storeDir := flags["store"]? | IO.eprintln usage; return 2
    let some file := flags["file"]? | IO.eprintln usage; return 2
    let author := flags.getD "author" "publisher"
    let store : Store := { root := storeDir }
    let cat ← Catalog.load store (← store.currentFiles)
    let mut anchor := ""
    let mut t := 0
    for gid in cat.order do
      t := t + 1
      store.putPub { pid := gid, file, anchor, lamport := t, author }
      anchor := gid
    let recs ← store.pubs
    let metas ← metasFor store recs
    let out := flags.getD "out" (file)
    IO.FS.writeFile out (renderProjection metas recs file)
    IO.println s!"published {t} groups as {file}; projection written to {out}"
    return 0
  | _ => IO.eprintln usage; return 2
