/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeUnpointedFppfOpenNaturality
public import FLT.Mazur.FiniteTypePointedFppfAcyclicOpen
public import FLT.Mazur.ProperPointedAcyclicFppfSheaf

/-!
# Compatibility with the pointed acyclic Picard locus

For pointed proper families the local subsheaf is exactly the previously
constructed represented image. For pointed finite-type integral originals,
the unpointed construction recovers the same actual test open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard

/-- With an original section, local acyclic sections already have global representatives. -/
theorem localGeometricAcyclicFppf_eq_pointed {X S : Scheme.{0}}
    (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    [IsLocallyNoetherian S] [IsProper f] [Flat f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    localGeometricAcyclicFppfSubfunctor f = geometricAcyclicFppfSubfunctor f := by
  apply Eq.symm
  apply Subfunctor.eq_sheafify
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose (Scheme.fppfTopology.over S) (forget CommGrpCat.{1})).obj
      (relativeFppfSheaf f)).property
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact properPointed_geometricAcyclicFppf_isSheaf f e he

/-- The general construction agrees with the pointed open on every actual sheaf section. -/
theorem finiteTypeUnpointedFppfAcyclicOpen_eq_pointed
    {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] [GeometricallyIntegral f]
    (e : Spec (.of R) ⟶ X) (he : e ≫ f = 𝟙 _)
    (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T)) :
    finiteTypeUnpointedFppfAcyclicOpen f T s = finiteTypePointedFppfAcyclicOpen f e he T s := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let _ : GeometricallyConnected f := ⟨by
    intro K _ a Y p q H
    let _ := GeometricallyIntegral.geometrically_isIntegral (f := f) a p q H
    infer_instance⟩
  obtain ⟨c, rfl⟩ := (properPointedRelativeFppfEquiv f e he T).surjective s
  exact (finiteTypeUnpointedFppfAcyclicOpen_class f T c).trans
    (finiteTypePointedFppfAcyclicOpen_class f e he T c).symm

end FLT.Mazur.CartierAbel
