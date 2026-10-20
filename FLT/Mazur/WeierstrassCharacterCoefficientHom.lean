/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientComposition
public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso
public import FLT.Mazur.WeierstrassSmoothGroupEquationTransport
public import FLT.Mazur.OneGonNilpotentCharacterHom
public import FLT.Mazur.CharacterGroupBaseChange

/-!
# Changing coefficients of actual smooth character homomorphisms

The categorical base change transports the full group homomorphism. Its
projection square is expressed on the original character and smooth schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth CharacterSchemeBaseChange CharacterAlgebraScalarExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S G : Type} [CommRing R] [CommRing S] [AddCommGroup G]
  (W : WeierstrassCurve R) (V : WeierstrassCurve S) (f : R →+* S) (h : V = W.map f)

/-- Character coefficient maps retain the actual coefficient-base projection. -/
@[reassoc] theorem characterCoefficient_structure :
    Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom G f)) ≫ (model R G).hom =
      (model S G).hom ≫ Spec.map (CommRingCat.ofHom f) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun k => Spec.map (CommRingCat.ofHom k))
    (AddMonoidAlgebra.mapRingHom_comp_algebraMap f)

/-- A sealed smooth group comparison retaining the named specialized equation. -/
irreducible_def smoothCoefficientGroupIsoTo : integralSmoothGroup V ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapCommGrp.obj (integralSmoothGroup W) := by
  letI : Algebra R S := f.toAlgebra
  exact smoothEquationGroupIso h ≪≫ originalSmoothCoefficientGroupIso S W

/-- The named group comparison retains both geometric transport factors. -/
theorem smoothCoefficientGroupIsoTo_hom :
    (smoothCoefficientGroupIsoTo W V f h).hom.hom.hom.hom.left =
      eqToHom (congrArg (fun U => (integralSmoothOpen U).toScheme) h) ≫
        (by letI := f.toAlgebra; exact (originalSmoothCoefficientIso S W).hom) := by
  let _ := f.toAlgebra
  rw [smoothCoefficientGroupIsoTo_def]
  exact congrArg₂ (fun a b => a ≫ b) (smoothEquationGroupIso_hom_left h)
    (originalSmoothCoefficientGroupIso_hom S W)

/-- The named group comparison projects to the actual smooth coefficient morphism. -/
@[reassoc] theorem smoothCoefficientGroupIsoTo_fst :
    (smoothCoefficientGroupIsoTo W V f h).hom.hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure W) (Spec.map (CommRingCat.ofHom f)) =
        smoothCoefficientMapTo W V f h := by
  let _ : Algebra R S := f.toAlgebra
  rw [smoothCoefficientGroupIsoTo_hom, Category.assoc]
  exact congrArg (eqToHom (congrArg (fun U => (integralSmoothOpen U).toScheme) h) ≫ ·)
    (originalSmoothCoefficientIso_fst S W)

/-- The inverse group comparison recovers the original pullback projection. -/
@[reassoc] theorem smoothCoefficientGroupIsoTo_inv_projection :
    (smoothCoefficientGroupIsoTo W V f h).inv.hom.hom.hom.left ≫
      smoothCoefficientMapTo W V f h =
        pullback.fst (integralSmoothStructure W) (Spec.map (CommRingCat.ofHom f)) := by
  rw [← smoothCoefficientGroupIsoTo_fst]
  have hi := congrArg (fun k => k.hom.hom.hom.left)
    (smoothCoefficientGroupIsoTo W V f h).inv_hom_id
  change (smoothCoefficientGroupIsoTo W V f h).inv.hom.hom.hom.left ≫
    (smoothCoefficientGroupIsoTo W V f h).hom.hom.hom.hom.left = 𝟙 _ at hi
  rw [← Category.assoc, hi, Category.id_comp]

/-- Projection and the base map jointly detect maps to the changed smooth scheme. -/
theorem smoothCoefficientMapTo_ext {X : Scheme}
    (a b : X ⟶ (integralSmoothOpen V).toScheme)
    (hp : a ≫ smoothCoefficientMapTo W V f h = b ≫ smoothCoefficientMapTo W V f h)
    (hb : a ≫ integralSmoothStructure V = b ≫ integralSmoothStructure V) : a = b := by
  let e := (CommGrp.forget (Over (Spec (.of S))) ⋙ Over.forget _).mapIso
    (smoothCoefficientGroupIsoTo W V f h)
  apply (cancel_mono e.hom).mp
  apply pullback.hom_ext
  · change (a ≫ (smoothCoefficientGroupIsoTo W V f h).hom.hom.hom.hom.left) ≫ _ =
      (b ≫ (smoothCoefficientGroupIsoTo W V f h).hom.hom.hom.hom.left) ≫ _
    erw [Category.assoc, Category.assoc, smoothCoefficientGroupIsoTo_fst]
    exact hp
  · change (a ≫ (smoothCoefficientGroupIsoTo W V f h).hom.hom.hom.hom.left) ≫ _ =
      (b ≫ (smoothCoefficientGroupIsoTo W V f h).hom.hom.hom.hom.left) ≫ _
    erw [Category.assoc, Category.assoc,
      (smoothCoefficientGroupIsoTo W V f h).hom.hom.hom.hom.w]
    exact hb

/-- Full coefficient change of the original character-group homomorphism. -/
irreducible_def characterCoefficientHom
    (g : CommGrp.mk (model R G) ⟶ integralSmoothGroup W) :
    CommGrp.mk (model S G) ⟶ integralSmoothGroup V := by
  letI : Algebra R S := f.toAlgebra
  exact (CommGrp.mkIso (overIso R S G)
    (IsMonHom.one_hom _) (IsMonHom.mul_hom _)).hom ≫
    (Over.pullback (baseMap R S)).mapCommGrp.map g ≫
      (smoothCoefficientGroupIsoTo W V f h).inv

/-- Coefficient change retains the full original character morphism after projection. -/
@[reassoc] theorem characterCoefficientHom_projection
    (g : CommGrp.mk (model R G) ⟶ integralSmoothGroup W) :
    (characterCoefficientHom W V f h g).hom.hom.hom.left ≫
      smoothCoefficientMapTo W V f h =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom G f)) ≫
          g.hom.hom.hom.left := by
  let _ : Algebra R S := f.toAlgebra
  rw [characterCoefficientHom_def]
  change (_ ≫ _ ≫ _) ≫ _ = _
  rw [Category.assoc, Category.assoc, smoothCoefficientGroupIsoTo_inv_projection]
  change (overIso R S G).hom.left ≫
    ((Over.pullback (baseMap R S)).map g.hom.hom.hom).left ≫
      pullback.fst (integralSmoothGroup W).X.hom (baseMap R S) = _
  have hk : ((Over.pullback (baseMap R S)).map g.hom.hom.hom).left ≫
      pullback.fst (integralSmoothGroup W).X.hom (baseMap R S) =
        pullback.fst (model R G).hom (baseMap R S) ≫ g.hom.hom.hom.left :=
    pullback.lift_fst _ _ _
  rw [hk, ← Category.assoc, overIso_fst]
  rfl

/-- The projection square uniquely characterizes the changed group homomorphism. -/
theorem characterCoefficientHom_unique
    (g : CommGrp.mk (model R G) ⟶ integralSmoothGroup W)
    (q : CommGrp.mk (model S G) ⟶ integralSmoothGroup V)
    (hq : q.hom.hom.hom.left ≫ smoothCoefficientMapTo W V f h =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom G f)) ≫
        g.hom.hom.hom.left) : q = characterCoefficientHom W V f h g := by
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  apply smoothCoefficientMapTo_ext W V f h
  · rw [characterCoefficientHom_projection]
    exact hq
  · exact q.hom.hom.hom.w.trans (characterCoefficientHom W V f h g).hom.hom.hom.w.symm

end FLT.Mazur.WeierstrassIntegralChart
