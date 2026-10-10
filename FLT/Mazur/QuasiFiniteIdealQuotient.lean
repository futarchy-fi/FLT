/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Artinian affine quotients of locally quasi-finite ideal subschemes

The actual quotient of an affine chart by an ideal sheaf is a chart of its
closed subscheme. Local quasi-finiteness over an Artinian scheme therefore
makes this quotient Artinian, without requiring rational support points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve

variable {X S : Scheme.{u}}

/-- Affine ideal quotients of a locally Artinian closed subscheme are Artinian. -/
theorem artinian_ideal_quotient_of_subscheme (I : X.IdealSheafData)
    [IsLocallyArtinian I.subscheme] (U : X.affineOpens) :
    IsArtinianRing (Γ(X, U) ⧸ I.ideal U) := by
  have h := IsLocallyArtinian.of_isImmersion (I.subschemeCover.f U)
  exact (Scheme.isLocallyArtinianScheme_Spec (R := .of (Γ(X, U) ⧸ I.ideal U))).mp h

/-- Local quasi-finiteness over an Artinian base controls every affine ideal quotient. -/
theorem artinian_ideal_quotient_of_locallyQuasiFinite (f : X ⟶ S)
    (I : X.IdealSheafData) [IsLocallyArtinian S]
    [LocallyQuasiFinite (I.subschemeι ≫ f)] (U : X.affineOpens) :
    IsArtinianRing (Γ(X, U) ⧸ I.ideal U) := by
  let _ : IsLocallyArtinian I.subscheme :=
    IsLocallyArtinian.of_locallyQuasiFinite (I.subschemeι ≫ f)
  exact artinian_ideal_quotient_of_subscheme I U

end FLT.Mazur.FCurve
