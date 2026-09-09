/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Proof

/-!
Regression checks for the `p ≥ 17` proof-spine boundary.
-/

example : FermatLastTheoremFor 5 := fermatLastTheoremFive
example : FermatLastTheoremFor 7 := fermatLastTheoremSeven
example : FermatLastTheoremFor 11 := fermatLastTheoremEleven
example : FermatLastTheoremFor 13 := fermatLastTheoremThirteen

/--
info: 'FLT_small' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT_small

/--
info: 'FLT.Bosses.B2_implies_B1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.Bosses.B2_implies_B1
