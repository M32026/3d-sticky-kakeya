/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public meta import Lean.Elab.Command
public meta import Kakeya.Meta.NoDebt
public import Lean.Message

/-!
# `#check_debt`: current-file heartbeat measurements

`#check_debt` profiles declarations preceding the command in the current file.
It writes that prefix to a temporary file and runs Lean's trace profiler with
`trace.profiler=true` and `Elab.async=false`, warning about declarations whose
elaboration exceeds `debtThresholdHb`. Declarations tagged `@[no_debt]` are
exempt; the attribute is defined in `Kakeya.Meta.NoDebt`.

Each run elaborates the prefix in a subprocess. Results are cached by the
prefix's content hash, so repeated editor elaboration reuses the result until
the prefix changes. This module depends only on Lean and `Kakeya.Meta.NoDebt`.
-/

open Lean Elab Command

public meta section

namespace Kakeya.CheckDebt

/-- The raw heartbeat count above which `#check_debt` flags a declaration. -/
def debtThresholdHb : Nat := 10000000

/-- Compact heartbeat display: `28.4M`, `742k`, or `512`. -/
def fmtHb (n : Nat) : MessageData :=
  if n ≥ 1000000 then m!"{n / 1000000}.{n % 1000000 / 100000}M"
  else if n ≥ 1000 then m!"{n / 1000}k"
  else m!"{n}"

/-- Remove `/- … -/` block comments (including `/-- … -/` docstrings) from `text`, so a declaration
keyword that happens to appear in prose is not mistaken for the declaration head. Non-nested. -/
private partial def stripBlockComments (text : String) : String :=
  match text.splitOn "/-" with
  | [only] => only
  | before :: rest =>
    let afterOpen := String.intercalate "/-" rest
    match afterOpen.splitOn "-/" with
    | [_unterminated] => before
    | _comment :: after => stripBlockComments (before ++ " " ++ String.intercalate "-/" after)
    | [] => before
  | [] => ""

/-- The first identifier following `kw` in `text` (e.g. `kw = "theorem "`), or `none`. -/
private def identAfter (text kw : String) : Option Name :=
  match text.splitOn kw with
  | _ :: after :: _ =>
    let nm := (after.trimAsciiStart.toString.takeWhile
      (fun c => c.isAlphanum || c == '_' || c == '.' || c == '\'')).toString
    if nm.isEmpty then none else some nm.toName
  | _ => none

/-- The declaration's (as-written, possibly short) name from a pretty-printed command, e.g.
`theorem foo …` ↦ `foo`. Returns `none` for anonymous commands. Strips comments first so keywords
in docstrings/prose don't masquerade as the head. -/
private def extractDeclName (text : String) : Option Name :=
  let clean := stripBlockComments text
  ["theorem ", "lemma ", "abbrev ", "instance ", "def "].findSome? (identAfter clean)

/-- Parse `lake env lean … -Dtrace.profiler=true` output: each over-threshold command prints as
`[Elab.command] [<heartbeats>] <pretty-printed command text…>` (the text may wrap over lines). We
read the heartbeats and the declaration name from each such node. The name is the *as-written* one;
`#check_debt` resolves it to the full constant for display. -/
private def parseProfiler (out : String) : Array (Name × Nat) := Id.run do
  let mut results : Array (Name × Nat) := #[]
  let mut curHb : Option Nat := none      -- heartbeats of the command node being read
  let mut curText : String := ""          -- its pretty-printed source, accumulated
  for line in out.splitOn "\n" do
    if "[Elab.command]".isPrefixOf line then
      if let some hb := curHb then
        if let some nm := extractDeclName curText then results := results.push (nm, hb)
      let rest := (line.drop "[Elab.command]".length).trimAsciiStart.toString
      if "[".isPrefixOf rest then
        curHb := (((rest.drop 1).takeWhile (· != '.')).toString).toNat?
        curText := ((rest.dropWhile (· != ']')).drop 1).toString
      else
        curHb := none; curText := ""
    else if !line.isEmpty && line.front == '[' then
      -- another top-level trace node: the current command's text is complete.
      if let some hb := curHb then
        if let some nm := extractDeclName curText then results := results.push (nm, hb)
      curHb := none; curText := ""
    else if "[".isPrefixOf (line.trimAsciiStart.toString) then
      pure ()                             -- indented child trace node: skip
    else if curHb.isSome then
      curText := curText ++ " " ++ line   -- a wrapped line of the command's source
  if let some hb := curHb then
    if let some nm := extractDeclName curText then results := results.push (nm, hb)
  return results

/-- Profile a file `prefix` in a subprocess and return `(name, heartbeats)` for every command over
`debtThresholdHb`, along with the subprocess exit code and stderr (for diagnostics). The profiler
threshold is set to `debtThresholdHb` so only over-budget commands print, and `Elab.async=false`
keeps each proof's cost on its own command node. -/
def scanPrefix (src : String) : IO (Array (Name × Nat) × UInt32 × String) := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let tmp := System.FilePath.mk dir / s!"kakeya_check_debt_{hash src}.lean"
  IO.FS.writeFile tmp src
  let o ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", tmp.toString, "-DElab.async=false",
        "-Dtrace.profiler=true", "-Dtrace.profiler.useHeartbeats=true",
        s!"-Dtrace.profiler.threshold={debtThresholdHb}"] }
  try IO.FS.removeFile tmp catch _ => pure ()
  return (parseProfiler o.stdout, o.exitCode, o.stderr)

/-- Cache of the most recent scan, keyed by the hash of the profiled prefix, so re-elaborating the
file in the editor reuses the result unless something above `#check_debt` changed. -/
initialize checkDebtCache : IO.Ref (Option (UInt64 × Array (Name × Nat))) ← IO.mkRef none

/-- Run the profiler on `pre`, cache the result on success, and surface subprocess failures. -/
def rescanPrefix (pre : String) (key : UInt64) : CommandElabM (Array (Name × Nat)) := do
  let (results, ec, err) ← scanPrefix pre
  if ec != 0 && results.isEmpty then
    logWarning m!"#check_debt: `lake env lean` exited with code {ec} and produced no profile. \
                  stderr:\n{err}"
  else
    checkDebtCache.set (some (key, results))
  return results

/-- Profile the current file *above* this command and warn about every declaration whose
elaboration exceeds `debtThresholdHb` heartbeats, skipping any tagged `@[no_debt]`. Self-contained:
no `set_option` and no linter — it runs the trace profiler on a temporary copy of the prefix (see
the module docstring). -/
elab "#check_debt" : command => do
  let fm ← getFileMap
  let src := fm.source
  -- Everything in the file above this command. The profiler runs on just this prefix, so every
  -- Every measured declaration precedes `#check_debt`.
  let lineNo := match (← getRef).getPos? with
    | some pos => (fm.toPosition pos).line
    | none => (src.splitOn "\n").length + 1
  let pre := String.intercalate "\n" ((src.splitOn "\n").take (lineNo - 1))
  let key := hash pre
  -- Reuse the cached result for an unchanged prefix; otherwise rescan.
  let measured ←
    match (← checkDebtCache.get) with
    | some (h, r) => if h == key then pure r else rescanPrefix pre key
    | none => rescanPrefix pre key
  -- Resolve each profiler node's as-written (possibly short) name to a full, current-file constant
  -- for a hyperlinked display. Two wrinkles make this more than a lookup:
  --   • A dotted `theorem A.b` is elaborated as `namespace A; theorem b; …; theorem A.b`, so the
  --     profiler logs it twice — once as the short `b`, once as the full `A.b`.
  --   • Sibling declarations can share a final component (`commRing.ohno` and `commRing.commRing.ohno`
  --     are both logged as `ohno`) with pretty-printed text, so name alone can't tell
  --     them apart.
  -- The profiler emits nodes in source order, so resolve the k-th node carrying a given as-written
  -- name to the k-th constant of that name (by source line). A dotted declaration's short and full
  -- copies then both resolve to `A.b` and collapse in the exact-name dedup below. (Limitation: if two
  -- same-suffix siblings exist but only the *later* one is over budget, its lone node is attributed to
  -- the earlier sibling — the profiler text carries no position to disambiguate further.)
  let env ← getEnv
  let locals : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if (env.getModuleIdxFor? n).isNone then acc.push n else acc
  let mut localLine : Array (Name × Nat) := #[]
  for n in locals do
    localLine := localLine.push (n, ((← findDeclarationRanges? n).map (·.range.pos.line)).getD 0)
  let lineOf (n : Name) : Nat := ((localLine.find? (·.1 == n)).map (·.2)).getD 0
  let candsFor (s : Name) : Array Name :=
    (locals.filter fun c => c == s || c.toString.endsWith ("." ++ s.toString)).qsort
      fun a b => lineOf a < lineOf b
  -- Resolve names (k-th occurrence ↦ k-th candidate), dedup by exact name keeping the max heartbeats,
  -- drop anything tagged `@[no_debt]`, sort by cost.
  let mut found : Array (Name × Nat) := #[]
  let mut seen : Array (Name × Nat) := #[]   -- as-written name ↦ occurrences already resolved
  for (s, hb) in measured do
    let k := ((seen.find? (·.1 == s)).map (·.2)).getD 0
    seen := match seen.findIdx? (·.1 == s) with
      | some i => seen.set! i (s, k + 1)
      | none => seen.push (s, 1)
    let cands := candsFor s
    let nm := if k < cands.size then cands[k]! else s
    match found.findIdx? (·.1 == nm) with
    | some i => found := found.set! i (nm, Nat.max hb found[i]!.2)
    | none => found := found.push (nm, hb)
  found := (found.filter fun p => !noDebtAttr.hasTag env p.1).qsort (·.2 > ·.2)
  if found.isEmpty then
    logInfo m!"#check_debt: nothing above exceeds {fmtHb debtThresholdHb} hb."
  else
    let rows := found.toList.map fun (nm, hb) =>
      let label := if env.contains nm then MessageData.ofConstName nm else m!"{nm}"
      m!"• {fmtHb hb} hb  {label}"
    logWarning <|
      m!"#check_debt: {found.size} declaration(s) over {fmtHb debtThresholdHb} hb:\n" ++
        MessageData.joinSep rows "\n"

end Kakeya.CheckDebt
