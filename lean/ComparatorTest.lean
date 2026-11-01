import Lean

/-!
`lake test` is the convenience entry point for checking our local development.
For an untrusted replacement proof, invoke `lake comparator --config=config.json
--paranoid` directly in a fresh trusted checkout, before building project code.
-/

def main : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["comparator", "--config=config.json", "--paranoid"]
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  child.wait
