/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientGrassmannianProduct
public import FLT.Mazur.VariableHilbertCommonAmbientSquare

/-!
# The unrestricted common source immerses in a finite Grassmannian product

The original acyclic source envelope followed by the finite Grassmannian
product is an actual immersion. Both original parameter coordinates and the
coefficient morphism are retained. Its canonical closed factor supplies
actual affine source opens over affine opens of the factorization target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  (U : X.affineOpens)

/-- Immerse the whole common-ambient source without fixing its translation coordinate. -/
def commonAmbientSourceGrassmannianMap :
    commonAmbientSourceTest f d V U ⟶ prod (commonAmbientGrassmannianTest f d U) V :=
  commonAmbientSourceEnvelope f d V U ≫ commonAmbientGrassmannianProduct f d U V

instance commonAmbientSourceGrassmannianMap_isImmersion :
    IsImmersion (commonAmbientSourceGrassmannianMap f d V U).left := by
  change IsImmersion ((commonAmbientSourceEnvelope f d V U).left ≫
    (commonAmbientGrassmannianProduct f d U V).left)
  infer_instance

/-- Its finite Grassmannian coordinate classifies the same original Hilbert family. -/
@[reassoc]
theorem commonAmbientSourceGrassmannianMap_fst :
    (commonAmbientSourceGrassmannianMap f d V U ≫ prod.fst).left =
      commonAmbientSourceParameter f d V U ≫ (commonAmbientGrassmannianArrow f d U).left := by
  rw [commonAmbientSourceGrassmannianMap, Category.assoc,
    commonAmbientGrassmannianProduct_fst, ← Category.assoc,
    commonAmbientSourceEnvelope, prod.lift_fst]
  rfl

/-- The independent translation point is exactly the original source's translation point. -/
@[reassoc]
theorem commonAmbientSourceGrassmannianMap_snd :
    commonAmbientSourceGrassmannianMap f d V U ≫ prod.snd =
      commonAmbientSourceInclusion f d V U ≫ variableHilbertBase f d V := by
  rw [commonAmbientSourceGrassmannianMap, Category.assoc,
    commonAmbientGrassmannianProduct_snd]
  exact prod.lift_snd _ _

/-- The coefficient map remains the original source restriction. -/
@[reassoc]
theorem commonAmbientSourceGrassmannianMap_over :
    (commonAmbientSourceGrassmannianMap f d V U).left ≫
      (prod (commonAmbientGrassmannianTest f d U) V).hom =
        (commonAmbientSourceTest f d V U).hom :=
  Over.w (commonAmbientSourceGrassmannianMap f d V U)

/-- The actual open target in which the whole common source is closed. -/
def commonAmbientSourceGrassmannianNeighborhood :=
  (commonAmbientSourceGrassmannianMap f d V U).left.coborderRange

/-- The actual closed factor, with all original source equations retained. -/
def commonAmbientSourceGrassmannianClosedFactor :
    (commonAmbientSourceTest f d V U).left ⟶
      (commonAmbientSourceGrassmannianNeighborhood f d V U).toScheme :=
  (commonAmbientSourceGrassmannianMap f d V U).left.liftCoborder

instance commonAmbientSourceGrassmannianClosedFactor_isClosedImmersion :
    IsClosedImmersion (commonAmbientSourceGrassmannianClosedFactor f d V U) :=
  inferInstanceAs (IsClosedImmersion
    (commonAmbientSourceGrassmannianMap f d V U).left.liftCoborder)

/-- The canonical closed factor recovers the same original source immersion. -/
@[reassoc]
theorem commonAmbientSourceGrassmannianClosedFactor_ι :
    commonAmbientSourceGrassmannianClosedFactor f d V U ≫
      (commonAmbientSourceGrassmannianNeighborhood f d V U).ι =
        (commonAmbientSourceGrassmannianMap f d V U).left :=
  Scheme.Hom.liftCoborder_ι _

end FLT.Mazur.HilbertChart
