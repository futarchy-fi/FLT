/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.SmoothCurveDimension
import FLT.Mazur.SmoothOpenSectionCartier

/-! # Axiom checks for smooth curve geometry

These theorems prove the exact geometric contracts without the arithmetic
assumptions used by the final Fermat theorem.
-/

/-- info: 'FLT.Mazur.FCurve.smoothCurveDimension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.smoothCurveDimension

/-- info: 'FLT.Mazur.FCurve.smoothSectionCartier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.smoothSectionCartier

/-- info: 'FLT.Mazur.FCurve.smoothOpenSectionCartier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.smoothOpenSectionCartier
