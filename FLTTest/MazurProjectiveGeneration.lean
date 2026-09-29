/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.ProjectiveGenerationEventually

/-! # Axiom audit of finite free generation in projective twists -/

namespace FLT.Mazur.ProjectiveSpace

/-- info: 'FLT.Mazur.ProjectiveSpace.sectionExtension_eventually'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sectionExtension_eventually

/-- info: 'FLT.Mazur.ProjectiveSpace.finite_sections_common_twist'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_sections_common_twist

/-- info: 'FLT.Mazur.ProjectiveSpace.globalEvaluation_epi_of_chart_generators'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalEvaluation_epi_of_chart_generators

/-- info: 'FLT.Mazur.ProjectiveSpace.exists_twist_finite_free_epi'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_twist_finite_free_epi

/-- info: 'FLT.Mazur.ProjectiveSpace.exists_eventually_twist_finite_free_epi'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_eventually_twist_finite_free_epi

end FLT.Mazur.ProjectiveSpace
