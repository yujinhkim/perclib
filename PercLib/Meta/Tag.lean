/-
Copyright (c) 2026 Tom Hutchcroft. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hutchcroft (with Codex assistance)
-/
module
public meta import Lean.Attributes
public meta import Lean.Elab.Command

public meta section
open Lean
namespace Lean.Parser.Attr

/-- Permanent wiki assertion identity. The compiled manifest validates cross-module uniqueness
and the one permitted duplicate: a statement definition and its proof (D-16). -/
syntax (name := tag) "tag " str : attr
end Lean.Parser.Attr
namespace PercLib.Meta

initialize tagAttribute : ParametricAttribute String ← registerParametricAttribute {
  name := `tag
  descr := "Permanent four-character wiki assertion tag"
  getParam := fun _ stx => do
    let some value := stx[1].isStrLit? | throwError "tag expects a string literal"
    unless value.length == 4 && value.toList.all (fun c => c.isDigit || ('A' ≤ c && c ≤ 'Z')) do
      throwError "tag must contain exactly four characters from 0-9A-Z"
    return value
}
end PercLib.Meta
