/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedOrientedAtlas
public import FLT.Mazur.PolygonSmoothFiniteAtlas

/-!
# The actual resolved smooth fiber and a specified residue polygon

Compare the complete finite arithmetic atlas with the original normalization
atlas of any specified polygon pinching over the residue field. Every label,
Laurent coordinate and coefficient map is retained. This comparison concerns
schemes; it does not identify an arithmetic multiplication law.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) [NeZero depth]
local notation "F" => ResidueField A
local notation "pA" => resolvedSplitStructure A D
variable {C : Over (Spec (.of (ResidueField A)))}
  (p : components (ResidueField A) depth ⟶ C) (q : nodes (ResidueField A) depth ⟶ C)
  (hp : IsPushout (toComponents (ResidueField A) depth D.depth_pos)
    (toNodes (ResidueField A) depth) p q)
  [LocallyOfFinitePresentation C.hom]

/-- Match the actual arithmetic tori with the specified normalized polygon components. -/
def resolvedPolygonSmoothIso : (pA).smoothLocus.toScheme ≅ C.hom.smoothLocus.toScheme :=
  (resolvedOrientedAtlasIso A D r).symm ≪≫ smoothFiniteAtlasIso F depth D.depth_pos p q hp

/-- Every natural finite label and every Laurent coordinate is preserved. -/
@[reassoc] theorem resolvedPolygonSmoothIso_chart (i : Fin depth) :
    resolvedOrientedComponentChart A D r i ≫ (resolvedPolygonSmoothIso A D r p q hp).hom =
      smoothFiniteChart F depth D.depth_pos p q hp i := by
  rw [← resolvedOrientedAtlasMap_chart A D r i]
  change (Sigma.ι _ i ≫ (resolvedOrientedAtlasIso A D r).hom) ≫
    ((resolvedOrientedAtlasIso A D r).inv ≫ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact smoothFiniteAtlasMap_chart F depth D.depth_pos p q hp i

/-- The chart comparison retains the polygon's actual original normalization map. -/
@[reassoc] theorem resolvedPolygonSmoothIso_chart_inclusion (i : Fin depth) :
    resolvedOrientedComponentChart A D r i ≫ (resolvedPolygonSmoothIso A D r p q hp).hom ≫
        C.hom.smoothLocus.ι = (torusToComponent F ≫ componentι F depth i ≫ p).left := by
  rw [resolvedPolygonSmoothIso_chart_assoc, smoothFiniteChart_inclusion]

/-- The full comparison is over the unchanged original residue spectrum. -/
@[reassoc] theorem resolvedPolygonSmoothIso_structure :
    (resolvedPolygonSmoothIso A D r p q hp).hom ≫ C.hom.smoothLocus.ι ≫ C.hom =
      (pA).smoothLocus.ι ≫ pA := by
  apply (cancel_epi (resolvedOrientedAtlasMap A D r)).mp
  apply Sigma.hom_ext
  intro i
  simp only [resolvedOrientedAtlasMap_chart_assoc,
    resolvedPolygonSmoothIso_chart_assoc, smoothFiniteChart_structure,
    resolvedOrientedComponentChart_structure]

/-- The comparison as an isomorphism over the original residue field. -/
def resolvedPolygonSmoothOverIso :
    Over.mk ((pA).smoothLocus.ι ≫ pA) ≅ smoothPolygon F (C := C) :=
  Over.isoMk (resolvedPolygonSmoothIso A D r p q hp)
    (resolvedPolygonSmoothIso_structure A D r p q hp)

/-- Label zero compares the reciprocal arithmetic identity with the original polygon torus. -/
@[reassoc] theorem resolvedPolygonSmoothIso_identity :
    resolvedReciprocalIdentitySmoothChart A D ≫ (resolvedPolygonSmoothIso A D r p q hp).hom =
      smoothFiniteChart F depth D.depth_pos p q hp ⟨0, D.depth_pos⟩ := by
  rw [← resolvedOrientedComponentChart_zero A D r]
  exact resolvedPolygonSmoothIso_chart A D r p q hp _

end FLT.Mazur.WeierstrassDividedDepth
