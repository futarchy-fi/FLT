/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.CurveFinite

/-! # Axiom audit of the proper-curve finiteness theorems

The FC13 and FC14 geometric inputs must not depend on the unproved arithmetic
inputs of Mazur's theorem.
-/

/-- info: 'FLT.Mazur.FCurve.properClosedSubsetFinite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.properClosedSubsetFinite

/-- info: 'FLT.Mazur.FCurve.nonconstantProperCurveFinite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.nonconstantProperCurveFinite
