/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: Lean 4.35 compatibility uses stock linear_combination with abel.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
Compatibility spelling for the historical additive_combination tactic.
Mathlib 4.35 supports additive-group equalities in linear_combination;
its abel normalizer replaces the retired LinearCombinationPrime engine.
The original rectangle proof now calls the stock tactic directly.
-/
open Lean
open Mathlib.Tactic.LinearCombination

syntax (name := AdditiveCombination) "additive_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| additive_combination $[(norm := $tac)]? $[(exp := $n)]? $(e)?) => do
    let norm ← match tac with
      | some t => pure t
      | none => `(tactic| abel)
    `(tactic| linear_combination (norm := $norm) $[(exp := $n)]? $(e)?)

example {A : Type*} [AddCommGroup A] {a b c : A}
    (h : a + b = c) (hb : b = 0) : a = c := by
  additive_combination h - hb
