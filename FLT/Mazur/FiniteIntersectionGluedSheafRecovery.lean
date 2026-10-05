/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionGluedRecoveryComparison
public import FLT.Mazur.FiniteIntersectionScalarRecoverySheaf

/-!
# Line-sheaf recovery on the explicit coefficient model

The same morphism used for cartesian scheme recovery pulls back the explicit
model line sheaf to the original cocycle sheaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
  (p : X ⟶ Spec (.of A)) [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
  (hcover : iSup U = ⊤) (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
  (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
    IsPullback
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrs)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrt)).hom.toRingHom)))
  (e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] (finiteIntersectionSectionDiagram U p).obj a)
  (he : ∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
    (affineScalarExtensionHom (S := A) (D.map f).hom) =
    ((finiteIntersectionSectionDiagram U p).map f).hom.comp (e a).toAlgHom)

variable (g : Cocycle U)
  (y : ∀ s, IntersectionPair s → (D.obj s)ˣ)
  (hnat : ∀ {s t} (f : s ⟶ t) (k : IntersectionPair s),
    (D.map f).hom (y s k) = (y t (intersectionPairMap f k) : D.obj t))
  (hmul : ∀ s (k : IntersectionTriple s),
    y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2))
  (hy : ∀ s k, e s (1 ⊗ₜ[S] (y s k : D.obj s)) =
    (finiteIntersectionCocycleUnit U p g s k : (finiteIntersectionSectionDiagram U p).obj s))

/-- Pullback along the cartesian recovery morphism recovers the original cocycle sheaf. -/
def finiteIntersectionGluedModelSheafRecoveryIso :
    (Scheme.Modules.pullback ((finiteIntersectionScalarGluingIso U p hU hcover D hp e he).inv ≫
        affineIntersectionGluingProjection (A := A) D hp)).obj
        (affineIntersectionGluedModelSheaf D hp y hnat hmul) ≅ g.sheaf := by
  let := intersectionDiagram_isLocallyDirected (affineIntersectionSchemeDiagram D) hp
  let := intersectionDiagram_isLocallyDirected
    (affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D))
    (affineIntersectionScalarExtension_isPullback D hp)
  let f := (finiteIntersectionScalarGluingIso U p hU hcover D hp e he).inv ≫
    affineIntersectionGluingProjection (A := A) D hp
  exact (Scheme.Modules.pullback f).mapIso
      (affineIntersectionGluedModelSheafIso D hp y hnat hmul).symm ≪≫
    (Scheme.Modules.pullbackComp f (affineIntersectionGluedColimitIso D hp).hom).app _ ≪≫
    (Scheme.Modules.pullbackCongr (finiteIntersectionModelRecovery_colimit
      U p hU hcover D hp e he)).app _ ≪≫
    finiteIntersectionModelColimitSheafIso U p hU hcover D e he g y hnat hmul hy

end FLT.Mazur.Approximation
