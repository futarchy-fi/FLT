/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSlopeLaurentLocalization
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The exact slope image in the Laurent infinity chart

The full two-root slope spectrum is precisely the principal Laurent open
T-1, with its complete scheme structure and original coefficient projection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [CommRing K]

/-- A Laurent algebra map is determined by the positive generator. -/
theorem slopeLaurent_hom_ext {S : Type*} [CommRing S] [Algebra K S]
    {f g : K[T;T⁻¹] →ₐ[K] S} (h : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) :
    f = g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : K[X]))
  apply Polynomial.ringHom_ext
  · intro r
    change f (Polynomial.toLaurent (Polynomial.C r)) =
      g (Polynomial.toLaurent (Polynomial.C r))
    rw [Polynomial.toLaurent_C]
    exact (f.commutes r).trans (g.commutes r).symm
  · change f (Polynomial.toLaurent Polynomial.X) = g (Polynomial.toLaurent Polynomial.X)
    rw [Polynomial.toLaurent_X]
    exact h

variable (a : Kˣ)
local notation "r" => (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹])
local notation "P" => SlopeOpen (a : K)
local notation "L" => WeierstrassIntegralChart.LaurentPuncture K

/-- The full slope spectrum is the entire punctured Laurent infinity spectrum. -/
def slopeLaurentPunctureIso : Spec (.of P) ≅ Spec (.of L) :=
  Scheme.Spec.mapIso (slopeLaurentPunctureEquiv a).toRingEquiv.toCommRingCatIso.op

/-- The spectrum transition preserves all Laurent restrictions on the actual puncture. -/
@[reassoc] theorem slopeLaurentPunctureIso_inclusion :
    (slopeLaurentPunctureIso a).hom ≫ PrincipalOpenTransport.inclusion r =
      Spec.map (CommRingCat.ofHom (slopeLaurentMap a).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (slopeLaurentPunctureEquiv_base a))

instance slopeLaurentMap_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (slopeLaurentMap a).toRingHom)) := by
  rw [← slopeLaurentPunctureIso_inclusion]
  infer_instance

/-- The exact image is the entire principal open T-1, including its generic points. -/
theorem slopeLaurentMap_range :
    Set.range (Spec.map (CommRingCat.ofHom (slopeLaurentMap a).toRingHom)) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum K[T;T⁻¹])) := by
  rw [← slopeLaurentPunctureIso_inclusion]
  exact PrincipalOpenTransport.chart_range r (slopeLaurentPunctureEquiv a)

/-- The full slope transition is over the original coefficient ring. -/
@[reassoc] theorem slopeLaurentMap_structure :
    Spec.map (CommRingCat.ofHom (slopeLaurentMap a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K[T;T⁻¹])) =
        Spec.map (CommRingCat.ofHom (algebraMap K P)) := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (slopeLaurentMap a).commutes)

end FLT.Mazur.WeierstrassModificationX
