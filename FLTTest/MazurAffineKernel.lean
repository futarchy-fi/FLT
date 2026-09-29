/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.AffineKernelLocalization

/-! # Axiom audit of kernels of quasi-coherent affine sheaf maps -/

namespace FLT.Mazur.FCurve

/-- info: 'FLT.Mazur.FCurve.affineKernelIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affineKernelIso

/-- info: 'FLT.Mazur.FCurve.affineKernelIso_hom_ι'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affineKernelIso_hom_ι

/-- info: 'FLT.Mazur.FCurve.affineKernelIso_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affineKernelIso_naturality

end FLT.Mazur.FCurve
