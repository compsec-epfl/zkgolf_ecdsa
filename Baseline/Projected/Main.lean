import Baseline.Projected.Export

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--export" then
    let directory := System.FilePath.mk (args[1]?.getD "Baseline/Projected/generated")
    Baseline.Projected.Offset.Export.exportTo directory
    return 0
  Baseline.Projected.Offset.Check.run args
