/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarFunctionNaturality

/-!
# Canonical geometric base change over original function scalars

The scheme, its arrows, and all coefficient comparison squares are constructed
from the original scalar algebras. The new scheme retains the full structure sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.FlatScalarSchemeBaseChange
open SchemeScalarPrincipalNeighborhood FlatScalarFunctionPushout FlatAlgebraEqualizer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Scheme.{0}) [Algebra R Γ(X, ⊤)]

/-- Base change of the whole scheme over its specified original scalar ring. -/
def baseChange : Scheme := pullback (scalarMorphism (algebraMap R Γ(X, ⊤)))
  (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The projection to the unchanged original scheme. -/
def source : baseChange R S X ⟶ X := pullback.fst _ _

/-- The projection to the new scalar spectrum. -/
def base : baseChange R S X ⟶ Spec (.of S) := pullback.snd _ _

/-- The defining square is cartesian. -/
theorem square : IsPullback (source R S X) (base R S X)
    (scalarMorphism (algebraMap R Γ(X, ⊤)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) := IsPullback.of_hasPullback _ _

variable {R S X} {Y : Scheme.{0}} [Algebra R Γ(Y, ⊤)]

/-- Base change of a specified original scalar-linear geometric arrow. -/
def map (v : X ⟶ Y) (u : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤))
    (hu : u.toRingHom = v.appTop.hom) : baseChange R S X ⟶ baseChange R S Y :=
  pullback.lift (source R S X ≫ v) (base R S X) (by
    rw [Category.assoc, scalarMorphism_natural v u hu]
    exact (square R S X).w)

/-- The original-source square for each constructed arrow. -/
theorem map_source (v : X ⟶ Y) (u : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤))
    (hu : u.toRingHom = v.appTop.hom) :
    map (S := S) v u hu ≫ source R S Y = source R S X ≫ v := pullback.lift_fst _ _ _

/-- Each constructed arrow uses the same new scalar base. -/
theorem map_base (v : X ⟶ Y) (u : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤))
    (hu : u.toRingHom = v.appTop.hom) :
    map (S := S) v u hu ≫ base R S Y = base R S X := pullback.lift_snd _ _ _

variable [Module.Flat R S]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The full tensor comparison square for the canonical geometric base change. -/
theorem map_sectionsEquiv (v : X ⟶ Y) (u : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤))
    (hu : u.toRingHom = v.appTop.hom) (z : S ⊗[R] Γ(Y, ⊤)) :
    sectionsEquiv (square R S X) (tensorMap S u z) =
      (map (S := S) v u hu).appTop (sectionsEquiv (square R S Y) z) :=
  sectionsEquiv_natural (square R S X) (square R S Y) v _ u hu
    (map_source v u hu) (map_base v u hu) z

end FLT.Mazur.FlatScalarSchemeBaseChange
