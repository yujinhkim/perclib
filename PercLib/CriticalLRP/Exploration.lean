/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# BFS exploration of the actual infinite cluster

This is exploration infrastructure, not a high-temperature moment theorem.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Defs
public import PercLib.CriticalLRP.Exploration.BFS.Basic
public import PercLib.CriticalLRP.Exploration.BFS.History
public import PercLib.CriticalLRP.Exploration.BFS.Measurable
public import PercLib.CriticalLRP.Exploration.BFS.Counting
public import PercLib.CriticalLRP.Exploration.BFS.Limit
public import PercLib.CriticalLRP.Exploration.BFS.RevealData
public import PercLib.CriticalLRP.Exploration.BFS.BFSProduct
public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Scalar
public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Budget
public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Rows.Defs
public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Fresh.Defs
public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Limit
public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Assemble
public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Nonvacuous
public import PercLib.CriticalLRP.Exploration.BFS.Generation.History.Defs
public import PercLib.CriticalLRP.Exploration.BFS.Generation.RowCharge
public import PercLib.CriticalLRP.Exploration.BFS.Generation.Arithmetic
public import PercLib.CriticalLRP.Exploration.BFS.Generation.Fresh
public import PercLib.CriticalLRP.Exploration.BFS.Generation.Step
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.FiniteHorizon
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Defs
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Induction
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Cluster
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Natural

@[expose] public section
