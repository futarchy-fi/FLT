/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.ProjectiveTwistQuotient

/-! # Axiom audit of coherent projective twist presentations -/

namespace FLT.Mazur.ProjectiveSpace

/-- info: 'FLT.Mazur.ProjectiveSpace.coordinateAlgebra_finiteType'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coordinateAlgebra_finiteType

/-- info: 'FLT.Mazur.ProjectiveSpace.chartRing_isNoetherian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chartRing_isNoetherian

/-- info: 'FLT.Mazur.ProjectiveSpace.space_isLocallyNoetherian'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms space_isLocallyNoetherian

/-- info: 'FLT.Mazur.ProjectiveSpace.projective_coherent_kernel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projective_coherent_kernel

/-- info: 'FLT.Mazur.ProjectiveSpace.twistTensorEquivalence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twistTensorEquivalence

/-- info: 'FLT.Mazur.ProjectiveSpace.exists_twist_sum_epi'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_twist_sum_epi

/-- info: 'FLT.Mazur.ProjectiveSpace.exists_coherent_twist_presentation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_coherent_twist_presentation

end FLT.Mazur.ProjectiveSpace
