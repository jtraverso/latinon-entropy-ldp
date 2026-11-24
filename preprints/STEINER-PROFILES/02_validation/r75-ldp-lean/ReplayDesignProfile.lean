import LeanChecker
open Lean

unsafe def replayDesignProfileModules : IO Unit := do
  initSearchPath (← findSysroot)
  for m in [`ProfileTypeLaw, `ProfileLDPPrinciple, `DesignProfileCounts,
      `DesignProfileRates, `DesignProfileLDP, `Reconstructed] do
    replayFromImports m
    IO.println s!"replaying {m}"

#eval replayDesignProfileModules
