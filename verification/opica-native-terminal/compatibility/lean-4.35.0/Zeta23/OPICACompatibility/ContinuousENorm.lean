/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Historical continuous enorm on seminormed groups

The declaration and continuity proof come from Mathlib commit
`51e6992efd06126df61a496bebf8f49482a4e129`,
`Mathlib/Analysis/Normed/Group/Continuity.lean`, lines 139–141.
At the Lean 4.35 pin Mathlib constructs the same structure through
`ESeminormedAddMonoid`. The historical declarations are ordinary definitions
here so each affected source module can select the additive instance locally.
-/

variable {E : Type*}

@[to_additive (attr := instance_reducible)]
def SeminormedGroup.toContinuousENorm [SeminormedGroup E] : ContinuousENorm E where
  continuous_enorm := ENNReal.isOpenEmbedding_coe.continuous.comp continuous_nnnorm'
