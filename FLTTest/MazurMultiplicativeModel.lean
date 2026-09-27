/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.MazurChapter.AdmissibleGroupSchemes

/-! # Axiom checks for the multiplicative prime-order group scheme

The elementary model and its order must not depend on the admitted classification.
-/

/-- info: 'FLT.MazurChapter.multiplicativeOrderPrime'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.MazurChapter.multiplicativeOrderPrime

/-- info: 'FLT.MazurChapter.multiplicativeOrderPrime_order'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.MazurChapter.multiplicativeOrderPrime_order
