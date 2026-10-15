/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroundChartOriginalQuotientTopology

/-!
# Effective residual descent from the changed-family quotient

The map to the full original quotient is the actual locally ringed coequalizer
of the original arrows acting on the changed-family quotient. This constructs
descent of compatible maps, including structure sheaves, without assuming that
the residual quotient is a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) {Z : LocallyRingedSpace}
  (g : U.left.toLocallyRingedSpace ⟶ Z)
  (hg : p.left.toLRSHom ≫ g = q.left.toLRSHom ≫ g)

/-- Descend a compatible morphism through the invariant locally ringed projection. -/
def invariantDescend : invariantLocallyRingedSpace e ⟶ Z :=
  (invariantLocallyRingedIso e).inv ≫ coequalizer.desc g hg

/-- Invariant descent preserves the whole original source morphism. -/
@[reassoc]
theorem invariantDescend_projection :
    invariantLocallyRingedProjection e ≫ invariantDescend e g hg = g := by
  dsimp only [invariantLocallyRingedProjection, invariantDescend]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact coequalizer.π_desc _ _

end FLT.Mazur.RelativeRelationOrbit

namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd invariantLocallyRingedProjection
  variableChartFixedBaseQuotientMap restrictedInvariantQuotientMap
  groundOriginalQuotientMap groundOriginalChart equivalence
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => pullback.snd f a
local instance groundOriginalResidualSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
variable {B : Over (Spec (.of S))} (l : B ⟶ variableHilbertTest (pullback.snd f a) d W)


local notation "k" => groundOriginalChart f a hL d V W t l
local notation "E" => variableChartEquivalenceRelation f hL d V c
local notation "D" => equivalence f hL d V c k
local notation "D'" => equivalence q h d W c' l
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l
local notation "r" => groundRelationInclusion f a hL d V W t c l

local notation "M" => groundOriginalQuotientMap f a hL d V W t c l
local notation "π" => invariantLocallyRingedProjection D
local notation "π'" => invariantLocallyRingedProjection D'

/-- The residual quotient map preserves the whole unchanged source projection. -/
@[reassoc]
theorem groundOriginalQuotientMap_projection : π' ≫ M = π := by
  rw [groundOriginalQuotientMap, invariantMap_projection]
  exact Category.id_comp _

/-- All original arrows coequalize after the residual quotient. -/
theorem groundOriginalResidual_condition :
    ((p).left.toLRSHom ≫ π') ≫ M = ((s).left.toLRSHom ≫ π') ≫ M := by
  simp only [Category.assoc, groundOriginalQuotientMap_projection]
  exact invariantProjection_condition D

/-- The residual cofork uses the full original relation, including cross-ground arrows. -/
def groundOriginalResidualCofork : Cofork ((p).left.toLRSHom ≫ π') ((s).left.toLRSHom ≫ π') :=
  Cofork.ofπ M (groundOriginalResidual_condition f a hL d V W t c l)

/-- The full original quotient is the effective residual quotient in locally ringed spaces. -/
def groundOriginalResidualIsColimit :
    IsColimit (groundOriginalResidualCofork f a hL d V W t c l) := by
  apply Cofork.IsColimit.mk'
  intro z
  have hz : (p).left.toLRSHom ≫ (π' ≫ z.π) =
      (s).left.toLRSHom ≫ (π' ≫ z.π) := by
    simpa only [Category.assoc] using z.condition
  let v := invariantDescend D (π' ≫ z.π) hz
  have hv : π ≫ v = π' ≫ z.π := invariantDescend_projection D _ hz
  refine ⟨v, ?_, ?_⟩
  · apply invariantMap_hom_ext D'
    change π' ≫ M ≫ v = π' ≫ z.π
    rw [groundOriginalQuotientMap_projection_assoc, hv]
  · intro w hw
    apply invariantMap_hom_ext D
    rw [hv, ← groundOriginalQuotientMap_projection f a hL d V W t c l,
      Category.assoc]
    exact congrArg (fun g ↦ π' ≫ g) hw

/-- Descend an actual compatible quotient morphism across all original extra arrows. -/
def groundOriginalResidualDescend {T : LocallyRingedSpace}
    (g : invariantLocallyRingedSpace D' ⟶ T)
    (hg : ((p).left.toLRSHom ≫ π') ≫ g = ((s).left.toLRSHom ≫ π') ≫ g) :
    invariantLocallyRingedSpace D ⟶ T := by
  refine invariantDescend D (π' ≫ g) ?_
  exact (Category.assoc _ _ _).symm.trans (hg.trans (Category.assoc _ _ _))

/-- Residual descent recovers the entire original morphism on the changed-family quotient. -/
@[reassoc]
theorem groundOriginalResidualDescend_factor {T : LocallyRingedSpace}
    (g : invariantLocallyRingedSpace D' ⟶ T)
    (hg : ((p).left.toLRSHom ≫ π') ≫ g = ((s).left.toLRSHom ≫ π') ≫ g) :
    M ≫ groundOriginalResidualDescend f a hL d V W t c l g hg = g := by
  apply invariantMap_hom_ext D'
  rw [groundOriginalQuotientMap_projection_assoc, groundOriginalResidualDescend,
    invariantDescend_projection]

end FLT.Mazur.HilbertChart.AffineRestriction
