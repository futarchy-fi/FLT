/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeBaseIndependentLineModel
public import FLT.Mazur.RelativeAcyclicClassDivisor

/-!
# Full divisors for all acyclic classes on arbitrary ring tests

The original proper flat geometrically integral family is over a ring of
finite type over the integers. Every class on every ring test is allowed;
its line bundle need not extend to the original model. Approximation constructs
such an extension on a new Noetherian model, then constructs the full ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A] [Algebra.FiniteType ℤ R]
  {X Y : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ Spec (.of A)} {q : Y ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q]
  (g : R →+* A) (h : IsPullback a f q (Spec.map (CommRingCat.ofHom g)))
  (c : RelativePic f) (hc : RelativeGeometricAcyclicRankOne f c)

include h hc in
/-- Every acyclic class on any ring test constructs an actual full relative Cartier divisor. -/
theorem finiteTypeBaseClass_divisor_exists :
    ∃ D : AcyclicRankOneRelativeDivisor f, abel f D.val = c := by
  obtain ⟨L, hL, hLc, hA⟩ := hc
  obtain ⟨Z, B, r, p, b, M, hB, hr, hflat, hint, hM, H, ⟨e⟩⟩ :=
    Approximation.finiteTypeBase_independent_line_model g h L hL
  let d := relativeClass r (mk M hM)
  have hd : relativeMap f r p b H.w.symm d = c :=
    (congrArg (relativeClass f) (mk_eq_of_iso (hM.pullback p) hL e)).trans hLc
  have htest : RelativeGeometricAcyclicRankOne f (relativeMap f r p b H.w.symm d) := by
    rw [hd]
    exact ⟨L, hL, hLc, hA⟩
  obtain ⟨D, hD⟩ := relativeClass_test_divisor_exists H d htest
  exact ⟨D, hD.trans hd⟩

/-- The canonical full inverse on all acyclic relative classes of the ring test. -/
def finiteTypeBaseClassDivisor : AcyclicRankOneRelativeDivisor f :=
  (finiteTypeBaseClass_divisor_exists g h c hc).choose

/-- The full divisor has the original independently varying class. -/
theorem finiteTypeBaseClassDivisor_class :
    abel f (finiteTypeBaseClassDivisor g h c hc).val = c :=
  (finiteTypeBaseClass_divisor_exists g h c hc).choose_spec

/-- All relative Cartier competitors coincide, without a cohomology condition on the competitor. -/
theorem finiteTypeBaseClassDivisor_unique (D : Divisor X)
    (hD : Flat (D.val.subschemeι ≫ f)) (hDc : abel f D = c) :
    D = (finiteTypeBaseClassDivisor g h c hc).val := by
  let E := finiteTypeBaseClassDivisor g h c hc
  let M := divisorLineBundle E.val.val E.val.property
  have hM := E.val.property.divisorLineBundle_locallyFreeRankOne
  let d : RelativeFiber f M hM :=
    ⟨⟨D, hDc.trans (finiteTypeBaseClassDivisor_class g h c hc).symm⟩, hD⟩
  let e : RelativeFiber f M hM := ⟨⟨E.val, rfl⟩, E.property.1⟩
  let _ : Surjective f := MorphismProperty.of_isPullback h inferInstance
  let _ := rankOne_relativeFiber_subsingleton f M hM E.property.2.2
  exact congrArg (fun z : RelativeFiber f M hM ↦ z.val.val) (Subsingleton.elim d e)

include h hc in
/-- Every acyclic class on an unrestricted ring test determines a unique full divisor. -/
theorem finiteTypeBaseClassDivisor_existsUnique :
    ∃! D : Divisor X, Flat (D.val.subschemeι ≫ f) ∧ abel f D = c :=
  ⟨(finiteTypeBaseClassDivisor g h c hc).val,
    ⟨(finiteTypeBaseClassDivisor g h c hc).property.1,
      finiteTypeBaseClassDivisor_class g h c hc⟩,
    fun D hD ↦ finiteTypeBaseClassDivisor_unique g h c hc D hD.1 hD.2⟩

end FLT.Mazur.CartierAbel
