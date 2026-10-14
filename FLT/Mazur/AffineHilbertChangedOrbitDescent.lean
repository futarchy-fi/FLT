/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertChangedOrbitKernel

/-!
# Effective quotient of the complete changed-family orbit

The freshly rebuilt Picard relation has the entire new ground as its scheme
coequalizer. The quotient is split, surjective and etale. Descent is explicitly
restriction to the original reflexive seed; this makes no assertion that the
parameter map is open or that the ground change is fppf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  (s : Spec (.of R') ⟶ A.left)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
local notation "π" => pullback.snd (Over.Hom.left q) s
local notation "b" =>
  SchemeRelationEtaleBranchPropagation.branch (Over.Hom.left p) (Over.Hom.left q) s
local notation "a" => s ≫ A.hom
local notation "g" => Limits.pullback.snd f a
local notation "W" => RelativeCoefficientBaseChange.target a (T := V)
local notation "t" => RelativeCoefficientBaseChange.toOld a (T := V)
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
local instance changedOrbitDescentSmooth : SmoothOfRelativeDimension 1 g :=
  MorphismProperty.pullback_snd _ _ inferInstance

local notation "B" => changedOrbitSource f hL d V c k s
local notation "l" => changedOrbitParameter f hL d V c k s
local notation "u" => changedOrbitToOld f hL d V c k s
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "p'" => fst g h d W c' l
local notation "q'" => snd g h d W c' l
local notation "D'" => relation g h d W c' l
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u
  (changedOrbitParameter_compat f hL d V c k s)
local notation "K" => (pullback (Over.hom B) (Over.hom B) : Scheme)
local notation "x" => pullback.fst (Over.hom B) (Over.hom B)
local notation "y" => pullback.snd (Over.hom B) (Over.hom B)

local notation "H" => changedOrbitRelation_isPullback f hL d V c k s

/-- The complete new ground is the coequalizer of the rebuilt full Picard relation. -/
def changedOrbitCoequalizer : IsColimit (Cofork.ofπ (B).hom
    (changedOrbitRelation_ground f hL d V c k s)) :=
  isColimitCoforkOfEffectiveEpi (B).hom (H).cone (H).isLimit

attribute [local irreducible] changedOrbitParameter changedOrbitChart
  changedOrbitSource changedOrbitCoequalizer

/-- Descend an invariant scheme map through the actual rebuilt relation. -/
def changedOrbitDescend {Y : Scheme}
    (v : (changedOrbitSource f hL d V c k s).left ⟶ Y)
    (hv : (p').left ≫ v = (q').left ≫ v) : Spec (.of R') ⟶ Y :=
  (changedOrbitCoequalizer f hL d V c k s).desc (Cofork.ofπ v hv)

@[reassoc]
theorem changedOrbitDescend_projection {Y : Scheme}
    (v : (changedOrbitSource f hL d V c k s).left ⟶ Y)
    (hv : (p').left ≫ v = (q').left ≫ v) :
    (B).hom ≫ changedOrbitDescend f hL d V c k s v hv = v :=
  Cofork.IsColimit.π_desc (changedOrbitCoequalizer f hL d V c k s)

/-- Descent is exactly evaluation on the reflexive seed, with all scheme structure retained. -/
theorem changedOrbitDescend_eq_section {Y : Scheme}
    (v : (changedOrbitSource f hL d V c k s).left ⟶ Y)
    (hv : (p').left ≫ v = (q').left ≫ v) : changedOrbitDescend f hL d V c k s v hv =
    changedOrbitSection f hL d V c k s ≫ v := by
  have he := congrArg (fun v' ↦ changedOrbitSection f hL d V c k s ≫ v')
    (changedOrbitDescend_projection f hL d V c k s v hv)
  simpa only [changedOrbitSection_ground_assoc] using he

/-- Any map with the required projection equation is the constructed descent. -/
theorem changedOrbitDescend_unique {Y : Scheme}
    (v : (changedOrbitSource f hL d V c k s).left ⟶ Y)
    (hv : (p').left ≫ v = (q').left ≫ v)
    (v' : Spec (.of R') ⟶ Y)
    (hv' : (B).hom ≫ v' = v) : v' = changedOrbitDescend f hL d V c k s v hv := by
  rw [changedOrbitDescend_eq_section, ← hv', changedOrbitSection_ground_assoc]

/-- Every invariant map descends uniquely over the entire new ground. -/
theorem changedOrbit_existsUnique_descend {Y : Scheme}
    (v : (changedOrbitSource f hL d V c k s).left ⟶ Y)
    (hv : (p').left ≫ v = (q').left ≫ v) : ∃! v' : Spec (.of R') ⟶ Y, (B).hom ≫ v' = v :=
  ⟨changedOrbitDescend f hL d V c k s v hv,
    changedOrbitDescend_projection f hL d V c k s v hv,
    fun v' hv' ↦ changedOrbitDescend_unique f hL d V c k s v hv v' hv'⟩

/-- Descent preserves an arbitrary subsequent coefficient or structure morphism. -/
@[reassoc]
theorem changedOrbitDescend_comp {Y : Scheme}
    (v : (changedOrbitSource f hL d V c k s).left ⟶ Y)
    (hv : (p').left ≫ v = (q').left ≫ v)
    {T : Scheme} (r' : Y ⟶ T)
    (z : Spec (.of R') ⟶ T) (hz : v ≫ r' = (B).hom ≫ z) :
    changedOrbitDescend f hL d V c k s v hv ≫ r' = z := by
  rw [changedOrbitDescend_eq_section, Category.assoc, hz,
    changedOrbitSection_ground_assoc]

end FLT.Mazur.HilbertChart.AffineRestriction
