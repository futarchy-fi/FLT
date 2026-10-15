/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticResidueCoefficients
public import FLT.Mazur.PolygonArithmeticStageRestriction
public import FLT.Mazur.PolygonInfinitesimalSpecialFiber

/-!
# The original polygon in every integral arithmetic thickening

The actual residue coefficient map identifies the original cyclic polygon
with the Cartesian closed fiber of every arithmetic stage. The comparison
retains every node chart and original unit-one marking, and its inclusion
commutes with all adjacent arithmetic restrictions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.PolygonArithmeticStages
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] [IsLocalRing A] (π : A)
  (hπ : algebraMap A (ResidueField A) π = 0) (m n : ℕ) (h : 2 ≤ n)
local notation "K" => ResidueField A

/-- The unchanged residue coefficient morphism into the arithmetic thickening. -/
def residueBase : Spec (.of K) ⟶ Spec (.of (Quotient A π m)) :=
  Spec.map (CommRingCat.ofHom (residueMap A π hπ m))

instance residueBase_isClosedImmersion : IsClosedImmersion (residueBase A π hπ m) :=
  IsClosedImmersion.spec_of_surjective _ (residueMap_surjective A π hπ m)

/-- The full zero-parameter polygon map into the original arithmetic stage. -/
def zeroSpecialization : PolygonInfinitesimal.scheme K 0 n h ⟶ (family A π m n h).left :=
  PolygonInfinitesimal.parameterProjection (residueMap A π hπ m) (parameter A π m) 0
    (residueMap_parameter A π hπ m) n h

/-- The residue coefficient map gives the actual whole zero-parameter fiber. -/
theorem zeroSpecialization_isPullback :
    IsPullback (zeroSpecialization A π hπ m n h) (PolygonInfinitesimal.toBase K 0 n h)
      (family A π m n h).hom (residueBase A π hπ m) :=
  PolygonInfinitesimal.parameterProjection_isPullback _ _ _
    (residueMap_parameter A π hπ m) n h

/-- The original cyclic polygon inclusion, preserving the specified node orientation. -/
def residueFiberInclusion : PolygonCyclicAtlas.scheme K n h ⟶ (family A π m n h).left :=
  (PolygonInfinitesimal.zeroFiberIso K n h).hom ≫ zeroSpecialization A π hπ m n h

/-- The original polygon is the entire Cartesian residue fiber of the arithmetic stage. -/
def residueFiberIso : PolygonCyclicAtlas.scheme K n h ≅
    pullback (family A π m n h).hom (residueBase A π hπ m) :=
  PolygonInfinitesimal.zeroFiberIso K n h ≪≫
    (zeroSpecialization_isPullback A π hπ m n h).isoPullback

/-- The comparison retains the original inclusion into the arithmetic thickening. -/
@[reassoc] theorem residueFiberIso_fst :
    (residueFiberIso A π hπ m n h).hom ≫ pullback.fst _ _ =
      residueFiberInclusion A π hπ m n h := by
  rw [residueFiberIso, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_fst]
  rfl

/-- The comparison retains the original polygon's residue structure map. -/
@[reassoc] theorem residueFiberIso_snd :
    (residueFiberIso A π hπ m n h).hom ≫ pullback.snd _ _ =
      PolygonCyclicAtlas.toBase K n h := by
  rw [residueFiberIso, Iso.trans_hom, Category.assoc,
    IsPullback.isoPullback_hom_snd, PolygonInfinitesimal.zeroFiberIso_base]

/-- The original polygon, with its original coefficient map, is the actual residue fiber. -/
theorem residueFiberInclusion_isPullback :
    IsPullback (residueFiberInclusion A π hπ m n h) (PolygonCyclicAtlas.toBase K n h)
      (family A π m n h).hom (residueBase A π hπ m) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (residueFiberIso A π hπ m n h)
    (residueFiberIso_fst A π hπ m n h) (residueFiberIso_snd A π hπ m n h)
  rw [← residueFiberIso_fst, ← residueFiberIso_snd,
    Category.assoc, Category.assoc, pullback.condition]

/-- Every complete original node chart has its specified split-node comparison. -/
@[reassoc] theorem chart_residueFiberInclusion (i : Fin n) :
    PolygonCyclicAtlas.chart K n h i ≫ residueFiberInclusion A π hπ m n h =
      (PolygonSmoothing.specialFiberIso K).hom ≫ PolygonInfinitesimal.chart K 0 n h i ≫
        zeroSpecialization A π hπ m n h := by
  rw [residueFiberInclusion, PolygonInfinitesimal.chart_zeroFiberIso_assoc]

/-- The unchanged unit-one label specializes through the original residue map. -/
@[reassoc] theorem marking_zeroSpecialization (i : Fin n) :
    PolygonInfinitesimal.marking K 0 n h i 1 ≫ zeroSpecialization A π hπ m n h =
      residueBase A π hπ m ≫ marking A π m n h i := by
  simpa only [map_one, zeroSpecialization, residueBase, marking] using
    PolygonInfinitesimal.marking_parameterProjection (residueMap A π hπ m)
      (parameter A π m) 0 (residueMap_parameter A π hπ m) n h i 1

/-- The original closed polygon inclusion is unchanged by adjacent arithmetic restriction. -/
@[reassoc] theorem residueFiberInclusion_stageRestriction :
    residueFiberInclusion A π hπ m n h ≫ stageRestriction A π m n h =
      residueFiberInclusion A π hπ (m + 1) n h := by
  simp only [residueFiberInclusion, zeroSpecialization, stageRestriction, Category.assoc,
    PolygonInfinitesimal.parameterProjection_comp, residueMap_restriction]

end FLT.Mazur.PolygonArithmeticStages
