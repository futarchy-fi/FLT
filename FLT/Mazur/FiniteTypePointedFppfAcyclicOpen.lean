/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestRelativePicardOpen
public import FLT.Mazur.GeometricAcyclicFppfLocus

/-!
# Open tests for actual fppf Picard-sheaf sections

Every actual sheaf section on every test determines an open of that test.
It represents membership of all restrictions in the acyclic subsheaf.
This establishes open chart intersections without postulating a global
Picard representative or sufficient charts to cover one.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (e : Spec (.of R) ⟶ X) (he : e ≫ f = 𝟙 _)

local instance fppfAcyclicOpenBaseNoetherian : IsNoetherianRing R :=
  Algebra.FiniteType.isNoetherianRing ℤ R

local instance fppfAcyclicOpenFamilyConnected : GeometricallyConnected f := ⟨by
  intro K _ a Y p q H
  let _ := GeometricallyIntegral.geometrically_isIntegral (f := f) a p q H
  infer_instance⟩

/-- The representing open of an actual Picard-sheaf section on an unrestricted test. -/
def finiteTypePointedFppfAcyclicOpen (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) : T.left.Opens :=
  finiteTypeTestRelativePicardOpen (IsPullback.of_hasPullback f T.hom)
    ((properPointedRelativeFppfEquiv f e he T).symm s)

/-- On any relative representative this open is the intrinsic class open. -/
theorem finiteTypePointedFppfAcyclicOpen_class (T : Over (Spec (.of R)))
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    finiteTypePointedFppfAcyclicOpen f e he T (relativeFppfClass f T c) =
      finiteTypeTestRelativePicardOpen (IsPullback.of_hasPullback f T.hom) c := by
  change finiteTypeTestRelativePicardOpen _
    ((properPointedRelativeFppfEquiv f e he T).symm
      (properPointedRelativeFppfEquiv f e he T c)) = _
  rw [Equiv.symm_apply_apply]

/-- A restriction lies in the acyclic subsheaf exactly when it factors through the open. -/
theorem finiteTypePointedFppfAcyclicOpen_represents {T U : Over (Spec (.of R))}
    (b : U ⟶ T) (s : (relativeFppfSheaf f).obj.obj (op T)) :
    (relativeFppfSheaf f).obj.map b.op s ∈
        (geometricAcyclicFppfSubfunctor f).obj (op U) ↔
      ∃! k : U.left ⟶ (finiteTypePointedFppfAcyclicOpen f e he T s).toScheme,
        k ≫ (finiteTypePointedFppfAcyclicOpen f e he T s).ι = b.left := by
  let c := (properPointedRelativeFppfEquiv f e he T).symm s
  have hs : relativeFppfClass f T c = s :=
    (properPointedRelativeFppfEquiv f e he T).apply_symm_apply s
  have hn := relativeFppfClass_naturality f b c
  rw [hs] at hn
  rw [hn, geometricAcyclicFppf_class_iff f e he]
  exact finiteTypeTestRelativePicardOpen_represents (IsPullback.of_hasPullback f T.hom)
    (relativeTotalMap_isPullback f b) c

end FLT.Mazur.CartierAbel
