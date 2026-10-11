/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingZeroCocone
public import FLT.Mazur.PolygonNodalCore
public import FLT.Mazur.PolygonGenusOne
public import FLT.Mazur.DRFiberClassification

/-!
# Nodal geometry and actual genus of the zero-parameter fibers

The original one-gon normalization pushout computes the constants and H1
of the actual cubic and of every specified zero-parameter coefficient fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open FCurve FCurve.CurveFiberHypotheses FCurve.DRFiberClassification
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The actual zero cubic has the original one-gon's nodal core and classification. -/
theorem zeroFiber_classified : ClassifiedFiberCore (family (0 : K)).hom :=
  ⟨PolygonNodalCore.nodalFiberCore K 1 (by decide) _ _ (zeroFiber_isPushout K),
    Or.inr ⟨1, by decide, _, _, zeroFiber_isPushout K⟩⟩

/-- The actual zero cubic has precisely the base-field global functions. -/
theorem zeroFiber_constantSections : HasConstantGlobalSections (family (0 : K)).hom :=
  PolygonConstantSections.constants K 1 (by decide) _ _ (zeroFiber_isPushout K)

/-- The original normalization computation gives the actual zero cubic's H1 dimension. -/
theorem zeroFiberH1_finrank : Module.finrank K (H1 (family (0 : K)).hom) = 1 :=
  PolygonCohomologyIncidence.h1_finrank K 1 (by decide) _ _ (zeroFiber_isPushout K)

variable {R : Type} [CommRing R] [Algebra R K] (t : R)
  (ht : algebraMap R K t = 0)
  {Y : Scheme} (p : Y ⟶ (family t).left) (q : Y ⟶ Spec (.of K))
  (hs : IsPullback p q (family t).hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))

include ht hs

/-- Every zero-parameter coefficient square retains the nodal core and polygon classification. -/
theorem zeroCartesian_classified : ClassifiedFiberCore q :=
  ⟨PolygonNodalCore.nodalFiberCore K 1 (by decide) _ _
    (zeroCartesian_isPushout K t ht p q hs),
    Or.inr ⟨1, by decide, _, _, zeroCartesian_isPushout K t ht p q hs⟩⟩

/-- Constants on the specified fiber use its actual structure morphism. -/
theorem zeroCartesian_constantSections : HasConstantGlobalSections q :=
  PolygonConstantSections.constants K 1 (by decide) _ _
    (zeroCartesian_isPushout K t ht p q hs)

/-- H1 on the specified zero-parameter fiber is one-dimensional over its coefficient field. -/
theorem zeroCartesianH1_finrank : Module.finrank K (H1 q) = 1 :=
  PolygonCohomologyIncidence.h1_finrank K 1 (by decide) (C := Over.mk q) _ _
    (zeroCartesian_isPushout K t ht p q hs)

/-- The actual zero-parameter fiber has dimension one. -/
theorem zeroCartesian_dimension : topologicalKrullDim Y = 1 :=
  PolygonDimension.dimension K 1 (by decide) _ _ (zeroCartesian_isPushout K t ht p q hs)

/-- The original proper-curve genus contract holds on every specified zero-parameter square. -/
theorem zeroCartesian_genus_one :
    let _ := family_proper t
    let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
    curveGenus q (zeroCartesian_dimension K t ht p q hs)
      (zeroCartesian_constantSections K t ht p q hs) = 1 := by
  let _ := family_proper t
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  exact zeroCartesianH1_finrank K t ht p q hs

end FLT.Mazur.OneGonSmoothing
