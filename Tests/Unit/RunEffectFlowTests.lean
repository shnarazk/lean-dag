import Tests.Unit.EffectFlowPosition

def main : IO Unit := do
  IO.println "Effect Flow Position Tests"
  IO.println "=========================="
  Tests.Unit.EffectFlowPosition.runTests
  IO.println "\n  All effect flow position tests passed"
