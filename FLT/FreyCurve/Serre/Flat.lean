/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.Flat
public import FLT.EllipticCurve.FlatTorsion
public import FLT.FreyCurve.Basic
public import FLT.FreyCurve.Serre.LocalInertia
public import FLT.FreyCurve.Serre.LocalTorsion

/-!
# Flatness of geometric torsion at good-reduction places

The geometric torsion comparison transports the finite-flat model over a local
field to the restriction of the global torsion representation. Passing to
coefficient quotients then gives `IsFlatAt`.

The good-reduction case uses the existing `torsion_flat_of_good_reduction`
admission. The multiplicative-reduction case is not covered.
-/

@[expose] public section

open NumberField

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

universe u

namespace WeierstrassCurve

variable {K : Type u} [Field K] [NumberField K]
  [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (E : WeierstrassCurve K) [E.IsElliptic] (n : ℕ) (hn : 0 < n)

set_option backward.isDefEq.respectTransparency false in
/-- A finite-flat model for local geometric torsion gives a finite-flat prolongation
of the global torsion representation restricted to that place. -/
theorem hasFlatProlongationAt_torsion_of_isFiniteFlat
    [DecidableEq (v.adicCompletion K)] [DecidableEq (AlgebraicClosure (v.adicCompletion K))]
    (hflat : GaloisModule.IsFiniteFlat (v.adicCompletionIntegers K) (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K))
      ((E.map (algebraMap K (v.adicCompletion K))).galoisRep n hn).Space) :
    (E.galoisRep n hn).HasFlatProlongationAt v := by
  classical
  let : (E.baseChange (v.adicCompletion K)).IsElliptic :=
    inferInstanceAs (E.map (algebraMap K (v.adicCompletion K))).IsElliptic
  let e := LinearEquiv.ofBijective (E.geometricTorsionBaseChange (L := v.adicCompletion K) n)
    (E.geometricTorsionBaseChange_bijective hn)
  let f : ((E.baseChange (v.adicCompletion K)).galoisRep n hn).Space →+[
      Field.absoluteGaloisGroup (v.adicCompletion K)] ((E.galoisRep n hn).toLocal v).Space :=
    { e.symm.toAddMonoidHom with
      map_smul' := by
        intro σ x
        apply e.injective
        change e (e.symm (_)) = e (((E.galoisRep n hn).toLocal v σ) (e.symm x))
        rw [e.apply_symm_apply]
        change _ = E.geometricTorsionBaseChange (L := v.adicCompletion K) n
          (((E.galoisRep n hn).toLocal v σ) (e.symm x))
        rw [E.geometricTorsionBaseChange_equivariant n hn]
        exact congrArg (((E.baseChange (v.adicCompletion K)).galoisRep n hn) σ)
          (e.apply_symm_apply x).symm }
  exact GaloisModule.IsFiniteFlat.map _ _ _ _ hflat f e.symm.bijective

/-- Good reduction at a completion gives a finite-flat prolongation of the global
torsion representation restricted to that place. -/
theorem hasFlatProlongationAt_torsion_of_goodReduction
    [(E.baseChange (v.adicCompletion K)).HasGoodReduction (v.adicCompletionIntegers K)] :
    (E.galoisRep n hn).HasFlatProlongationAt v := by
  classical
  let : (E.map (algebraMap K (v.adicCompletion K))).HasGoodReduction
      (v.adicCompletionIntegers K) :=
    inferInstanceAs ((E.baseChange (v.adicCompletion K)).HasGoodReduction
      (v.adicCompletionIntegers K))
  exact E.hasFlatProlongationAt_torsion_of_isFiniteFlat v n hn
    ((E.map (algebraMap K (v.adicCompletion K))).isFiniteFlat_torsion_of_goodReduction
      (v.adicCompletionIntegers K) (v.adicCompletion K) n hn)

/-- At a place of good reduction, prime torsion satisfies the flatness condition
for every open ideal of its coefficient field. -/
theorem isFlatAt_torsion_of_goodReduction [Fact n.Prime]
    [(E.baseChange (v.adicCompletion K)).HasGoodReduction (v.adicCompletionIntegers K)] :
    (E.galoisRep n hn).IsFlatAt v :=
  (E.hasFlatProlongationAt_torsion_of_goodReduction v n hn).isFlatAt v _

end WeierstrassCurve

namespace FreyCurve

/-- The good-reduction case of flatness at the Frey exponent prime. -/
theorem torsion_isFlatAt_of_goodReduction (P : FreyPackage)
    [(P.freyCurve.baseChange
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)).HasGoodReduction
      (P.pp.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ)] :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  exact P.freyCurve.isFlatAt_torsion_of_goodReduction
    P.pp.toHeightOneSpectrumRingOfIntegersRat P.p P.hppos

end FreyCurve
