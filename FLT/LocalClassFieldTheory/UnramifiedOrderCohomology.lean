/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOrderSequence
public import FLT.LocalClassFieldTheory.UnramifiedUnitAcyclic

/-!
# The order-induced cohomology isomorphism at finite unramified stages

Unit acyclicity and the actual short exact order sequence prove that order
induces an isomorphism in every positive degree, in particular degree two.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory Limits IsLocalRing

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [Finite (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]

/-- Order induces an isomorphism on every positive finite-stage cohomology group. -/
theorem unramifiedOrderMap_cohomology_isIso (n : ℕ) :
    IsIso ((groupCohomology.functor ℤ Gal(L/K) (n + 1)).map (unramifiedOrderMap R S K L)) := by
  let X := unramifiedOrderSequence R S K L
  have hX := unramifiedOrderSequence_shortExact R S K L
  have hz := unramified_unit_cohomology_isZero R S K L n
  have hzs := unramified_unit_cohomology_isZero R S K L (n + 1)
  let : Mono ((groupCohomology.functor ℤ Gal(L/K) (n + 1)).map X.g) :=
    ((groupCohomology.mapShortComplex₂ X (n + 1)).exact_iff_mono
      (IsZero.eq_zero_of_src hz _)).1 (groupCohomology.mapShortComplex₂_exact hX (n + 1))
  let : Epi ((groupCohomology.functor ℤ Gal(L/K) (n + 1)).map X.g) :=
    ((groupCohomology.mapShortComplex₃ hX (i := n + 1) rfl).exact_iff_epi
      (IsZero.eq_zero_of_tgt hzs _)).1 (groupCohomology.mapShortComplex₃_exact hX rfl)
  change IsIso ((groupCohomology.functor ℤ Gal(L/K) (n + 1)).map X.g)
  exact isIso_of_mono_of_epi _

/-- The finite-stage order isomorphism from multiplicative H² to integral H². -/
def unramifiedOrderH2Iso :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ≅
      groupCohomology (Rep.trivial ℤ Gal(L/K) ℤ) 2 := by
  exact @asIso (ModuleCat ℤ) _ _ _
    ((groupCohomology.functor ℤ Gal(L/K) 2).map (unramifiedOrderMap R S K L))
    (unramifiedOrderMap_cohomology_isIso R S K L 1)

/-- The constructed isomorphism is induced by the concrete order coefficient map. -/
theorem unramifiedOrderH2Iso_hom :
    (unramifiedOrderH2Iso R S K L).hom =
      (groupCohomology.functor ℤ Gal(L/K) 2).map (unramifiedOrderMap R S K L) := rfl

end LocalClassFieldTheory
