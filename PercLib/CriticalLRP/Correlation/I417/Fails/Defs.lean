/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Fails.lean ; the two concrete
configurations were moved here so that definitions remain in a `Defs.lean` file.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Final

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

/-- The base configuration on `Fin 4`: only the edge `{2,3}` is open. -/
def baseCfg : Config (Fin 4) := {s(2, 3)}

/-- The fresh configuration on `Fin 4`: only the edge `{1,2}` is open. -/
def freshCfg : Config (Fin 4) := {s(1, 2)}

end PercLib.CriticalLRP.I417
