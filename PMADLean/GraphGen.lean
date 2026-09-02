import Lean

open Lean

/-- Blacklists standard core library prefixes to isolate your project proofs -/
def isSystemName (n : Name) : Bool :=
  let root := n.getRoot
  root == `Lean || root == `Init || root == `Core || root == `IO || root == `Nat || root == `String || root == `Subtype

def getExprDeps (e : Expr) : NameSet :=
  e.foldConsts ∅ fun n acc => if !isSystemName n then acc.insert n else acc

def printTheoremGraph (env : Environment) : IO Unit := do
  IO.println "graph TD"
  let _ ← env.constants.fold (init := (pure () : IO Unit)) fun acc declName cinfo => do
    acc
    -- Catch everything that isn't a base system wrapper
    if !isSystemName declName then
      let mut deps := getExprDeps cinfo.type
      if let some val := cinfo.value? then
        deps := deps.union (getExprDeps val)

      for dep in deps do
        if dep != declName && !isSystemName dep then
          let src := declName.toString.replace "." "_"
          let tgt := dep.toString.replace "." "_"
          IO.println s!"    {src} --> {tgt}"
    return ()
