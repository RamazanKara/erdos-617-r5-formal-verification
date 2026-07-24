import Mathlib.Tactic.Sat.FromLRAT

open Lean Elab Command
open Std (HashMap)
open Mathlib.Tactic.Sat

namespace Erdos617.LRATStage

namespace Parser

open Lean Std.Internal.Parsec String

def parseLRATStep : String.Parser LRATStep := do
  let step ← Mathlib.Tactic.Sat.Parser.parseNat <* ws
  if (← peek!) = 'd' then
    skip <* ws
    pure <| LRATStep.del (← Mathlib.Tactic.Sat.Parser.parseNats)
  else
    ws
    pure <| LRATStep.add step
      (← Mathlib.Tactic.Sat.Parser.parseInts)
      (← Mathlib.Tactic.Sat.Parser.parseInts)

def parseFrontier : String.Parser (Array (Nat × Array Int)) := many do
  let identifier ← Mathlib.Tactic.Sat.Parser.parseNat <* ws
  let literals ← Mathlib.Tactic.Sat.Parser.parseInts
  pure (identifier, literals)

end Parser

partial def buildAndType (types : Array Expr) (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => panic! "empty conjunction"
  | 1 => types[start]!
  | length =>
    let middle := start + length / 2
    mkApp2 (Lean.mkConst ``And)
      (buildAndType types start middle)
      (buildAndType types middle stop)

partial def buildAndProof (items : Array (Expr × Expr))
    (start stop : Nat) : Expr × Expr :=
  match stop - start with
  | 0 => panic! "empty conjunction"
  | 1 => items[start]!
  | length =>
    let middle := start + length / 2
    let left := buildAndProof items start middle
    let right := buildAndProof items middle stop
    (mkApp2 (Lean.mkConst ``And) left.1 right.1,
      mkApp4 (Lean.mkConst ``And.intro) left.1 right.1 left.2 right.2)

partial def collectAndRefs (types : Array Expr) (start stop : Nat)
    (proof : Expr) (refs : Array Expr := #[]) : Array Expr :=
  match stop - start with
  | 0 => refs
  | 1 => refs.push proof
  | length =>
    let middle := start + length / 2
    let leftType := buildAndType types start middle
    let rightType := buildAndType types middle stop
    let leftProof := mkApp3 (Lean.mkConst ``And.left) leftType rightType proof
    let rightProof := mkApp3 (Lean.mkConst ``And.right) leftType rightType proof
    let refs := collectAndRefs types start middle leftProof refs
    collectAndRefs types middle stop rightProof refs

structure FlushResult where
  db : HashMap Nat Clause
  serial : Nat

def flushClauses (ctx : Expr) (name : Name) (serial : Nat)
    (db : HashMap Nat Clause) (batch : Array (Nat × Clause)) : MetaM FlushResult := do
  if batch.isEmpty then throwError "cannot flush an empty clause batch"
  let mut items : Array (Expr × Expr) := #[]
  let mut types : Array Expr := #[]
  for (_, clause) in batch do
    let type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx clause.expr
    types := types.push type
    items := items.push (type, clause.proof)
  let conjunction := buildAndProof items 0 items.size
  let declName := Name.num (Name.str name "batch") serial
  addDecl <| Declaration.thmDecl {
    name := declName
    levelParams := []
    type := conjunction.1
    value := conjunction.2
  }
  let refs := collectAndRefs types 0 types.size (Lean.mkConst declName)
  let mut db := db
  for h : index in [:batch.size] do
    let (identifier, clause) := batch[index]
    db := db.insert identifier { clause with proof := refs[index]! }
  return { db, serial := serial + 1 }

def buildOriginalDb (clauses : Array (Array Int)) (ctx expandedCtx : Expr)
    (name : Name) : MetaM (HashMap Nat Clause) := do
  let subsumes := mkApp (Lean.mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db :=
    (Mathlib.Tactic.Sat.buildClauses clauses ctx 0 clauses.size expandedCtx subsumes default).2
  let mut batch : Array (Nat × Clause) := #[]
  let mut serial := 0
  for identifier in [1:clauses.size + 1] do
    let some clause := db[identifier]? | throwError "missing original clause"
    batch := batch.push (identifier, clause)
    if batch.size = 1000 then
      let flushed ← flushClauses ctx (name ++ `orig) serial db batch
      db := flushed.db
      serial := flushed.serial
      batch := #[]
  unless batch.isEmpty do
    let flushed ← flushClauses ctx (name ++ `orig) serial db batch
    db := flushed.db
  return db

structure LetBlockResult where
  iterator : Sigma String.Pos
  db : HashMap Nat Clause
  live : Array (Nat × Clause)
  proof : Expr
  finished : Bool
  exhausted : Bool
  finalId : Option Nat
  additions : Nat

def finishLetBlock (iterator : Sigma String.Pos) (db : HashMap Nat Clause)
    (blockIds : Array Nat) (finished exhausted : Bool) (finalId : Option Nat)
    (additions : Nat) : MetaM LetBlockResult := do
  let mut live : Array (Nat × Clause) := #[]
  let mut items : Array (Expr × Expr) := #[]
  for identifier in blockIds do
    if let some clause := db[identifier]? then
      live := live.push (identifier, clause)
      let type ← Meta.inferType clause.proof
      items := items.push (type, clause.proof)
  let proof :=
    if items.isEmpty then Lean.mkConst ``True.intro
    else (buildAndProof items 0 items.size).2
  return { iterator, db, live, proof, finished, exhausted, finalId, additions }

partial def processLetBlock (lrat : String) (iterator : Sigma String.Pos)
    (ctx : Expr) (db : HashMap Nat Clause) (blockIds : Array Nat)
    (remaining additions : Nat) : MetaM LetBlockResult := do
  if iterator.2.IsAtEnd then
    return ← finishLetBlock iterator db blockIds false true none additions
  match Parser.parseLRATStep iterator with
  | Std.Internal.Parsec.ParseResult.error _ error =>
    throwError m!"parse LRAT failed: {error}"
  | Std.Internal.Parsec.ParseResult.success next step =>
    match step with
    | LRATStep.del identifiers =>
      for identifier in identifiers do
        unless db.contains identifier do
          throwError m!"deletion of non-live clause {identifier}"
      processLetBlock lrat next ctx (identifiers.foldl (·.erase ·) db)
        blockIds remaining additions
    | LRATStep.add identifier literals hints =>
      if remaining = 0 then
        finishLetBlock iterator db blockIds false false none additions
      else
        if db.contains identifier then throwError m!"reused live clause identifier {identifier}"
        let expression := Mathlib.Tactic.Sat.buildClause literals
        match Mathlib.Tactic.Sat.buildProofStep db literals hints ctx expression with
        | Except.error message => throwError message
        | Except.ok proof =>
          let type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx expression
          Meta.withLetDecl (Name.num `rup identifier) type proof fun proofRef => do
            let clause : Clause := { lits := literals, expr := expression, proof := proofRef }
            let db := db.insert identifier clause
            let blockIds := blockIds.push identifier
            let additions := additions + 1
            let result ←
              if literals.isEmpty then
                if !next.2.IsAtEnd then throwError "records occur after the empty clause"
                finishLetBlock next db blockIds true false (some identifier) additions
              else
                processLetBlock lrat next ctx db blockIds (remaining - 1) additions
            let wrapped ← Meta.mkLetFVars #[proofRef] result.proof
              (usedLetOnly := true) (generalizeNondepLet := false)
            return { result with proof := wrapped }

structure StageResult where
  db : HashMap Nat Clause
  finalProof : Option Expr
  additions : Nat

partial def processBlocks (lrat : String) (iterator : Sigma String.Pos)
    (ctx : Expr) (name : Name) (db : HashMap Nat Clause)
    (serial additions : Nat) : MetaM StageResult := do
  let result ← processLetBlock lrat iterator ctx db #[] 1000 additions
  let mut db := result.db
  if result.live.isEmpty then
    if result.finished then throwError "empty final let block"
    if result.exhausted then return { db, finalProof := none, additions := result.additions }
    processBlocks lrat result.iterator ctx name db serial result.additions
  else
    let declName := Name.num (Name.str name "block") serial
    let type ← Meta.inferType result.proof
    addDecl <| Declaration.thmDecl {
      name := declName
      levelParams := []
      type
      value := result.proof
    }
    let mut types : Array Expr := #[]
    for (_, clause) in result.live do
      types := types.push <| mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx clause.expr
    let refs := collectAndRefs types 0 types.size (Lean.mkConst declName)
    for h : index in [:result.live.size] do
      let (identifier, clause) := result.live[index]
      db := db.insert identifier { clause with proof := refs[index]! }
    liftM <| IO.println s!"let-block LRAT additions: {result.additions}"
    if result.finished then
      let some finalId := result.finalId | throwError "missing final clause identifier"
      for h : index in [:result.live.size] do
        if result.live[index].1 = finalId then
          return { db, finalProof := some refs[index]!, additions := result.additions }
      throwError "final empty clause was not exported"
    if result.exhausted then return { db, finalProof := none, additions := result.additions }
    processBlocks lrat result.iterator ctx name db (serial + 1) result.additions

def parseDimacs (cnf : String) : MetaM (Array (Array Int)) := do
  match Mathlib.Tactic.Sat.Parser.parseDimacs ⟨cnf, cnf.startPos⟩ with
  | Std.Internal.Parsec.ParseResult.error _ error =>
    throwError m!"parse CNF failed: {error}"
  | Std.Internal.Parsec.ParseResult.success next (_, clauses) =>
    unless next.2.IsAtEnd do throwError "trailing CNF input"
    if clauses.isEmpty then throwError "empty CNF"
    return clauses

def parseFrontier (data : String) : MetaM (Array (Nat × Array Int)) := do
  match Parser.parseFrontier ⟨data, data.startPos⟩ with
  | Std.Internal.Parsec.ParseResult.error _ error =>
    throwError m!"parse frontier failed: {error}"
  | Std.Internal.Parsec.ParseResult.success next entries =>
    unless next.2.IsAtEnd do throwError "trailing frontier input"
    if entries.isEmpty then throwError "empty frontier"
    return entries

def defineContext (clauses : Array (Array Int)) (name : Name) : MetaM (Expr × Expr) := do
  let expanded := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
  let ctxName := Name.str name "ctx"
  addDecl <| Declaration.defnDecl {
    name := ctxName
    levelParams := []
    type := Lean.mkConst ``Sat.Fmla
    value := expanded
    hints := ReducibilityHints.regular 0
    safety := DefinitionSafety.safe
  }
  return (Lean.mkConst ctxName, expanded)

def loadFrontier (data : String) (ctx : Expr) (priorName : Name) : MetaM (HashMap Nat Clause) := do
  let entries ← parseFrontier data
  let mut seen : HashMap Nat Unit := {}
  let mut clauses : Array (Nat × Array Int × Expr) := #[]
  let mut types : Array Expr := #[]
  for (identifier, literals) in entries do
    if identifier = 0 then throwError "zero frontier identifier"
    if seen.contains identifier then throwError m!"duplicate frontier identifier {identifier}"
    seen := seen.insert identifier ()
    let expression := Mathlib.Tactic.Sat.buildClause literals
    clauses := clauses.push (identifier, literals, expression)
    types := types.push <| mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx expression
  let frontierName := Name.str priorName "frontier"
  let frontierProof := Lean.mkConst frontierName
  let actualType ← Meta.inferType frontierProof
  let expectedType := buildAndType types 0 types.size
  unless ← Meta.isDefEq actualType expectedType do
    throwError m!"frontier theorem type mismatch: {frontierName}"
  let refs := collectAndRefs types 0 types.size frontierProof
  let mut db : HashMap Nat Clause := {}
  for h : index in [:clauses.size] do
    let (identifier, literals, expression) := clauses[index]
    db := db.insert identifier { lits := literals, expr := expression, proof := refs[index]! }
  return db

def exportFrontier (data : String) (ctx : Expr) (name : Name)
    (db : HashMap Nat Clause) : MetaM Unit := do
  let entries ← parseFrontier data
  if entries.size != db.size then
    throwError m!"frontier size mismatch: expected {entries.size}, proved {db.size}"
  let mut seen : HashMap Nat Unit := {}
  let mut items : Array (Expr × Expr) := #[]
  for (identifier, literals) in entries do
    if seen.contains identifier then throwError m!"duplicate frontier identifier {identifier}"
    seen := seen.insert identifier ()
    let some clause := db[identifier]? |
      throwError m!"frontier is missing proved clause {identifier}"
    if clause.lits != literals then throwError m!"frontier clause mismatch at {identifier}"
    let type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx clause.expr
    items := items.push (type, clause.proof)
  let conjunction := buildAndProof items 0 items.size
  addDecl <| Declaration.thmDecl {
    name := Name.str name "frontier"
    levelParams := []
    type := conjunction.1
    value := conjunction.2
  }

def runInitial (cnf lrat : String) (name : Name) : MetaM (Expr × StageResult) := do
  let clauses ← parseDimacs cnf
  let (ctx, expanded) ← defineContext clauses name
  let db ← buildOriginalDb clauses ctx expanded name
  let result ← processBlocks lrat ⟨lrat, lrat.startPos⟩ ctx name db 0 0
  return (ctx, result)

def stageInitial (cnf lrat outputFrontier : String) (name : Name) : MetaM Unit := do
  let (ctx, result) ← runInitial cnf lrat name
  if result.finalProof.isSome then throwError "initial stage unexpectedly derived empty clause"
  exportFrontier outputFrontier ctx name result.db
  let additions := result.additions
  let frontier := result.db.size
  liftM <| IO.println
    s!"initial LRAT stage complete: additions={additions} frontier={frontier}"

def stageInitialFinal (cnf lrat : String) (name : Name) : MetaM Unit := do
  let (ctx, result) ← runInitial cnf lrat name
  let some proof := result.finalProof | throwError "single LRAT stage did not derive empty clause"
  let type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx
    (Mathlib.Tactic.Sat.buildClause #[])
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value := proof }
  liftM <| IO.println s!"single final LRAT stage complete: additions={result.additions}"

def stageContinue (inputFrontier lrat outputFrontier : String)
    (name ctxName priorName : Name) : MetaM Unit := do
  let ctx := Lean.mkConst ctxName
  let db ← loadFrontier inputFrontier ctx priorName
  let result ← processBlocks lrat ⟨lrat, lrat.startPos⟩ ctx name db 0 0
  if result.finalProof.isSome then throwError "continuation stage unexpectedly derived empty clause"
  exportFrontier outputFrontier ctx name result.db
  let additions := result.additions
  let frontier := result.db.size
  liftM <| IO.println
    s!"continuation LRAT stage complete: additions={additions} frontier={frontier}"

def stageFinal (inputFrontier lrat : String)
    (name ctxName priorName : Name) : MetaM Unit := do
  let ctx := Lean.mkConst ctxName
  let db ← loadFrontier inputFrontier ctx priorName
  let result ← processBlocks lrat ⟨lrat, lrat.startPos⟩ ctx name db 0 0
  let some proof := result.finalProof | throwError "final LRAT stage did not derive empty clause"
  let type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx
    (Mathlib.Tactic.Sat.buildClause #[])
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value := proof }
  liftM <| IO.println s!"final LRAT stage complete: additions={result.additions}"

end Erdos617.LRATStage

elab "lrat_stage_initial_file " n:ident ppSpace cnfPath:str ppSpace lratPath:str
    ppSpace frontierPath:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let cnf ← IO.FS.readFile cnfPath.getString
  let lrat ← IO.FS.readFile lratPath.getString
  let frontier ← IO.FS.readFile frontierPath.getString
  Command.liftTermElabM do
    Erdos617.LRATStage.stageInitial cnf lrat frontier name

elab "lrat_stage_initial_final_file " n:ident
    ppSpace cnfPath:str ppSpace lratPath:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let cnf ← IO.FS.readFile cnfPath.getString
  let lrat ← IO.FS.readFile lratPath.getString
  Command.liftTermElabM do
    Erdos617.LRATStage.stageInitialFinal cnf lrat name

elab "lrat_stage_continue_file " n:ident ppSpace ctx:ident ppSpace prior:ident
    ppSpace inputFrontierPath:str ppSpace lratPath:str
    ppSpace outputFrontierPath:str : command => do
  let currentNamespace ← getCurrNamespace
  let name := currentNamespace ++ n.getId
  let ctxName := currentNamespace ++ ctx.getId
  let priorName := currentNamespace ++ prior.getId
  let inputFrontier ← IO.FS.readFile inputFrontierPath.getString
  let lrat ← IO.FS.readFile lratPath.getString
  let outputFrontier ← IO.FS.readFile outputFrontierPath.getString
  Command.liftTermElabM do
    Erdos617.LRATStage.stageContinue inputFrontier lrat outputFrontier
      name ctxName priorName

elab "lrat_stage_final_file " n:ident ppSpace ctx:ident ppSpace prior:ident
    ppSpace inputFrontierPath:str ppSpace lratPath:str : command => do
  let currentNamespace ← getCurrNamespace
  let name := currentNamespace ++ n.getId
  let ctxName := currentNamespace ++ ctx.getId
  let priorName := currentNamespace ++ prior.getId
  let inputFrontier ← IO.FS.readFile inputFrontierPath.getString
  let lrat ← IO.FS.readFile lratPath.getString
  Command.liftTermElabM do
    Erdos617.LRATStage.stageFinal inputFrontier lrat name ctxName priorName
