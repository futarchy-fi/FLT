/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePointLineAmple
public import FLT.Mazur.AmpleDivisorComplementAffine
public import FLT.Mazur.RelativeGenusOneCoordinateRing

/-!
# The affine cubic is the original relative point complement

Ampleness proves affineness of the actual complement. Its existing coordinate
morphism is consequently an isomorphism, retaining the original base map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "W" => relativePointWeierstrassCurve G hg s hI e
local notation "U" => Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl

include hI in
omit [GrpObj G] in
/-- The original point complement is affine over the Noetherian affine base. -/
theorem relative_pointComplement_isAffine : IsAffineOpen s.left.ker.support.compl :=
  isAffineOpen_divisorComplement (G.hom ≫ S.isoSpec.hom) hI
    (relative_pointLine_ample G s hI)

/-- The original normalized coordinate morphism is an isomorphism of affine schemes. -/
theorem relativePointToAffineCubic_isIso : IsIso (relativePointToAffineCubic G hg s hI e) := by
  let _ : IsAffine U := relative_pointComplement_isAffine G s hI
  let _ : IsIso (CommRingCat.ofHom (relativePointCoordinateEvaluation G hg s hI e)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (relativePointCoordinateRingEquiv G hg s hI e).bijective
  unfold relativePointToAffineCubic
  infer_instance

/-- The actual original point complement identified with its constructed relative cubic. -/
def relativePointAffineIso : U ≅ Spec (.of (W).toAffine.CoordinateRing) := by
  let _ := relativePointToAffineCubic_isIso G hg s hI e
  exact asIso (relativePointToAffineCubic G hg s hI e)

/-- The affine comparison preserves the original structure morphism. -/
theorem relativePointAffineIso_over :
    (relativePointAffineIso G hg s hI e).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing)) =
        (Scheme.Opens.ι (X := G.left) s.left.ker.support.compl) ≫ G.hom ≫ S.toSpecΓ :=
  relativePointToAffineCubic_over G hg s hI e

/-- The constructed affine cubic is smooth over the original affine coefficient ring. -/
theorem relativePointAffineCubic_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing))) := by
  let _ := SmoothOfRelativeDimension.smooth 1 G.hom
  let a := relativePointAffineIso G hg s hI e
  have ha := relativePointAffineIso_over G hg s hI e
  have hu : Smooth (a.inv ≫ (Scheme.Opens.ι (X := G.left) s.left.ker.support.compl) ≫
      G.hom ≫ S.toSpecΓ) := inferInstance
  rw [← ha, Iso.inv_hom_id_assoc] at hu
  exact hu

end FLT.Mazur.FCurve
