/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleRestrict
public import FLT.Mazur.ModuleStalkExact

/-!
# The ideal quotient exact sequence

The actual quotient map is surjective on affine sections. This gives its
categorical epimorphism property and the global ideal short exact sequence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The closed-subscheme quotient is surjective on every affine open. -/
theorem idealQuotientMap_affine_surjective (U : X.affineOpens) :
    Function.Surjective ((idealQuotientMap I).app U.1) :=
  I.subschemeι.app_surjective U.1 U.2

/-- Affine surjectivity makes the actual ideal quotient an epimorphism. -/
instance idealQuotientMap_epi : Epi (idealQuotientMap I) where
  left_cancellation g h he := by
    apply moduleHom_ext_affine
    intro U
    ext s
    obtain ⟨r, rfl⟩ := idealQuotientMap_affine_surjective I U s
    exact congrArg (fun k ↦ k.app U.1 r) he

/-- The canonical ideal sequence retains the actual closed pushforward. -/
def idealQuotientComplex : ShortComplex X.Modules :=
  ShortComplex.mk (idealModuleι I) (idealQuotientMap I) (kernel.condition _)

/-- The actual ideal, structure module and closed quotient form a short exact sequence. -/
theorem idealQuotientComplex_shortExact : (idealQuotientComplex I).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (idealQuotientMap I))
    (inferInstanceAs (Mono (idealModuleι I)))
    (inferInstanceAs (Epi (idealQuotientMap I)))

end FLT.Mazur.FCurve
