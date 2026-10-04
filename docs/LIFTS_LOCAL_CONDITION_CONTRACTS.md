# Local lifting conditions after W43

This is a specification and dependency list, not a local representability or
crystalline comparison theorem. Sources: Khare–Wintenberger II,
<https://www.math.ucla.edu/~shekhar/papers/proofs.pdf>, §3.2.2,
Proposition 3.6, §3.3.4 and §4.1.1. Saved source: `Scratch/kw-proofs.pdf`;
text anchors 1152, 1259, 1987, 2016 in `Scratch/kw-proofs.txt`.

## Lp0: the condition at p

Fix the residual representation, coefficient ring O, determinant and integral
framing. On a proartinian O-algebra A the existing integral condition is exactly:
for every open ideal I of A, the local representation on
`(A/I) ⊗[A] (Fin 2 → A)` has a finite-flat model over Z_p.
`flatFunctor` in `FLT.Deformations.LiftFunctor` implements this condition and
proves preservation under coefficient morphisms. `GaloisRep.IsFlatAt` is its
unframed predicate. Neither carries a chosen compatible system of group schemes.

The source's characteristic-zero condition is different data: crystalline
representations of weight 2, with Hodge–Tate weights {0,1} in KW's convention,
fixed cyclotomic determinant (psi=1 here), and trivial Weil–Deligne inertial
type and monodromy. KW §3.2.2(i) also discusses other weight-2 *potentially*
semistable types; that larger condition is not the endpoint's flat condition.
Proposition 3.6 concerns the specified flat, reduced O-algebras and their
characteristic-zero points; it is not an assertion that every arbitrary
representation with an inertia trace condition is crystalline.

Required comparison: characterize the integral lattices in weight-2 crystalline
representations by the actual finite-flat reductions, then prove the condition
is represented by an appropriate closed quotient of the unrestricted ring.
A statement equating these conditions cannot be a definition or record field.
R1a/R1b concern residual ordinary models and do not establish this integral
comparison, including the nonordinary branch. Lp0 source/API specification is
settled here; the comparison and local representing ring remain open.

## L20: fix the quotient character at two

KW §3.3.4 fixes gamma_v lifting the residual quotient character, with its
inertial restriction the Teichmueller lift and gamma_v^2 chi_p = phi. For our
unramified quadratic residual quotient and phi=chi_p, fix an unramified
quadratic lift gamma over O. On A the quotient must be its image gamma_A
under the same O-algebra map. The upper character is then chi_p gamma_A
using the determinant. The exact sequence must retain its surjective map.

`HasSpecifiedQuotientAtTwo` keeps the actual rank-one quotient representation
as a parameter. Conjugation and coefficient extension preserve it, with the
extended quotient constructed by tensoring and the canonical right-unit map.
This proves stability for that parameterized condition. Constructing gamma
from a residual quotient, packaging it into the existing framed functor, and
proving its local quotient ring are still required.

`IsHardlyRamified.isTameAtTwo` existentially supplies a quotient with the
unramified and square-one conditions. It does not fix the same quotient
character across all lifts. `narrowTraceConditionFunctor` supplies trace 2 on
inertia; it supplies neither this quotient map nor a fixed Frobenius character.
Consequently `narrowSLiftFunctor` cannot silently replace the KW condition.
Its existing admitted corepresentability theorem remains unused here.

## D1a: the first quotient construction

`OpenIdealCondition` proves that maps from any existing proartinian parameter
ring U killing a proper open ideal I form a subfunctor, corepresented by the
constructed quotient U/I. The equivalence, unique factor, continuity and
naturality are proved. It applies in particular to the unrestricted universal
trace ring from `HardlyRamifiedUniversal`.

This is the open-ideal case only. It does not identify an arithmetic ideal.
Next: construct quotients by arbitrary closed ideals (using inverse limits if
necessary), identify the local conditions with the kernel condition on actual
universal representations, and prove closure and effectivity. No supplied
comparison isomorphism or local representability assertion replaces those
proofs. The global Selmer dimension, characteristic-zero point, finiteness,
coefficient-order and residual-conjugacy gates remain separate.
