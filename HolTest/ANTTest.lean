/- File: HolTest/ANTTest.lean
Runtime test suite: the 91 files of ANT/ (HolANT/, wired by SessionANT/).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "ANT/<file>.ml"`, then `string_of_thm`, newlines joined).
tools/antgrp<G>diff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here.  The files are
in one test module so that each SessionANT module replays once. -/

import HolTest.CommonTest
import SessionANT.Algmisc
import SessionANT.Ufd
import SessionANT.Integral
import SessionANT.IntegralPrimes
import SessionANT.IdealArith
import SessionANT.Hensel
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.ValuationRing
import SessionANT.IdealNorm
import SessionANT.IdealEuler
import SessionANT.DedekindAbsolute
import SessionANT.Zlattice
import SessionANT.LinearForms
import SessionANT.HermiteInequality
import SessionANT.Numfield
import SessionANT.DedekindExtension
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.ClassgroupGroup
import SessionANT.FractionalIdeals
import SessionANT.DedekindCriteria
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.PowerBasis
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.Integrality
import SessionANT.Different
import SessionANT.DedekindKummer
import SessionANT.PowerBasisIndex
import SessionANT.DifferentExtension
import SessionANT.DifferentExponent
import SessionANT.Eisenstein
import SessionANT.Quadratic
import SessionANT.QuadraticSplit
import SessionANT.SplittingTypes
import SessionANT.Decomposition
import SessionANT.NfDecomposition
import SessionANT.DecompositionField
import SessionANT.ConjugateIdeals
import SessionANT.QuadraticIdeals
import SessionANT.SplitPrimes
import SessionANT.IdealNormExtension
import SessionANT.DiscriminantExtension
import SessionANT.ClassGroupMaps
import SessionANT.SIntegers
import SessionANT.UnramifiedOutside
import SessionANT.ValuationResidue
import SessionANT.FingenGroup
import SessionANT.CyclotomicPoly
import SessionANT.CyclotomicField
import SessionANT.CyclotomicIntegers
import SessionANT.CyclotomicSplit
import SessionANT.CyclotomicGalois
import SessionANT.CyclotomicFrobenius
import SessionANT.CyclotomicSubfields
import SessionANT.CyclotomicSubfieldSplit
import SessionANT.GaussSum
import SessionANT.CyclotomicQuadraticSplit
import SessionANT.ComplexEmbeddings
import SessionANT.ComplexConjugation
import SessionANT.CyclotomicCharacter
import SessionANT.Sunits
import SessionANT.InfinitePlaces
import SessionANT.MinkowskiTheory
import SessionANT.InertiaGenerators
import SessionANT.DiscriminantCompositum
import SessionANT.Hermite
import SessionANT.UnitTheorem
import SessionANT.Regulator
import SessionANT.RootsOfUnity
import SessionANT.QuadraticUnits
import SessionANT.Stickelberger
import SessionANT.ProductFormula
import SessionANT.SunitRank
import SessionANT.ValuationRankOne
import SessionANT.AbsoluteValues
import SessionANT.Places
import SessionANT.RamificationGroups
import SessionANT.PowerBasisExtension
import SessionANT.HilbertFormula
import SessionANT.DedekindZeta
import SessionANT.FrobeniusDensity

open HolCore.Kernel HolTest.CommonTest

#eval SessionANT.Algmisc.ensureAlgmisc
#eval SessionANT.Ufd.ensureUfd
#eval SessionANT.Integral.ensureIntegral
#eval SessionANT.IntegralPrimes.ensureIntegralPrimes
#eval SessionANT.IdealArith.ensureIdealArith
#eval SessionANT.Hensel.ensureHensel
#eval SessionANT.Dedekind.ensureDedekind
#eval SessionANT.DedekindStruct.ensureDedekindStruct
#eval SessionANT.DedekindLocal.ensureDedekindLocal
#eval SessionANT.DedekindValuation.ensureDedekindValuation
#eval SessionANT.ValuationRing.ensureValuationRing
#eval SessionANT.IdealNorm.ensureIdealNorm
#eval SessionANT.IdealEuler.ensureIdealEuler
#eval SessionANT.DedekindAbsolute.ensureDedekindAbsolute
#eval SessionANT.Zlattice.ensureZlattice
#eval SessionANT.LinearForms.ensureLinearForms
#eval SessionANT.HermiteInequality.ensureHermiteInequality
#eval SessionANT.Numfield.ensureNumfield
#eval SessionANT.DedekindExtension.ensureDedekindExtension
#eval SessionANT.RingOfIntegers.ensureRingOfIntegers
#eval SessionANT.NormIndex.ensureNormIndex
#eval SessionANT.Classgroup.ensureClassgroup
#eval SessionANT.NfValuation.ensureNfValuation
#eval SessionANT.ClassgroupGroup.ensureClassgroupGroup
#eval SessionANT.FractionalIdeals.ensureFractionalIdeals
#eval SessionANT.DedekindCriteria.ensureDedekindCriteria
#eval SessionANT.PrimeSplit.ensurePrimeSplit
#eval SessionANT.Discriminant.ensureDiscriminant
#eval SessionANT.PowerBasis.ensurePowerBasis
#eval SessionANT.TraceForm.ensureTraceForm
#eval SessionANT.FiniteFieldTrace.ensureFiniteFieldTrace
#eval SessionANT.Ramification.ensureRamification
#eval SessionANT.RelativeSplit.ensureRelativeSplit
#eval SessionANT.RelativeDegree.ensureRelativeDegree
#eval SessionANT.Integrality.ensureIntegrality
#eval SessionANT.Different.ensureDifferent
#eval SessionANT.DedekindKummer.ensureDedekindKummer
#eval SessionANT.PowerBasisIndex.ensurePowerBasisIndex
#eval SessionANT.DifferentExtension.ensureDifferentExtension
#eval SessionANT.DifferentExponent.ensureDifferentExponent
#eval SessionANT.Eisenstein.ensureEisenstein
#eval SessionANT.Quadratic.ensureQuadratic
#eval SessionANT.QuadraticSplit.ensureQuadraticSplit
#eval SessionANT.SplittingTypes.ensureSplittingTypes
#eval SessionANT.Decomposition.ensureDecomposition
#eval SessionANT.NfDecomposition.ensureNfDecomposition
#eval SessionANT.DecompositionField.ensureDecompositionField
#eval SessionANT.ConjugateIdeals.ensureConjugateIdeals
#eval SessionANT.QuadraticIdeals.ensureQuadraticIdeals
#eval SessionANT.SplitPrimes.ensureSplitPrimes
#eval SessionANT.IdealNormExtension.ensureIdealNormExtension
#eval SessionANT.DiscriminantExtension.ensureDiscriminantExtension
#eval SessionANT.ClassGroupMaps.ensureClassGroupMaps
#eval SessionANT.SIntegers.ensureSIntegers
#eval SessionANT.UnramifiedOutside.ensureUnramifiedOutside
#eval SessionANT.ValuationResidue.ensureValuationResidue
#eval SessionANT.FingenGroup.ensureFingenGroup
#eval SessionANT.CyclotomicPoly.ensureCyclotomicPoly
#eval SessionANT.CyclotomicField.ensureCyclotomicField
#eval SessionANT.CyclotomicIntegers.ensureCyclotomicIntegers
#eval SessionANT.CyclotomicSplit.ensureCyclotomicSplit
#eval SessionANT.CyclotomicGalois.ensureCyclotomicGalois
#eval SessionANT.CyclotomicFrobenius.ensureCyclotomicFrobenius
#eval SessionANT.CyclotomicSubfields.ensureCyclotomicSubfields
#eval SessionANT.CyclotomicSubfieldSplit.ensureCyclotomicSubfieldSplit
#eval SessionANT.GaussSum.ensureGaussSum
#eval SessionANT.CyclotomicQuadraticSplit.ensureCyclotomicQuadraticSplit
#eval SessionANT.ComplexEmbeddings.ensureComplexEmbeddings
#eval SessionANT.ComplexConjugation.ensureComplexConjugation
#eval SessionANT.CyclotomicCharacter.ensureCyclotomicCharacter
#eval SessionANT.Sunits.ensureSunits
#eval SessionANT.InfinitePlaces.ensureInfinitePlaces
#eval SessionANT.MinkowskiTheory.ensureMinkowskiTheory
#eval SessionANT.InertiaGenerators.ensureInertiaGenerators
#eval SessionANT.DiscriminantCompositum.ensureDiscriminantCompositum
#eval SessionANT.Hermite.ensureHermite
#eval SessionANT.UnitTheorem.ensureUnitTheorem
#eval SessionANT.Regulator.ensureRegulator
#eval SessionANT.RootsOfUnity.ensureRootsOfUnity
#eval SessionANT.QuadraticUnits.ensureQuadraticUnits
#eval SessionANT.Stickelberger.ensureStickelberger
#eval SessionANT.ProductFormula.ensureProductFormula
#eval SessionANT.SunitRank.ensureSunitRank
#eval SessionANT.ValuationRankOne.ensureValuationRankOne
#eval SessionANT.AbsoluteValues.ensureAbsoluteValues
#eval SessionANT.Places.ensurePlaces
#eval SessionANT.RamificationGroups.ensureRamificationGroups
#eval SessionANT.PowerBasisExtension.ensurePowerBasisExtension
#eval SessionANT.HilbertFormula.ensureHilbertFormula
#eval SessionANT.DedekindZeta.ensureDedekindZeta
#eval SessionANT.FrobeniusDensity.ensureFrobeniusDensity

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

namespace T

-- Algmisc
#eval thm' "Algmisc.UPPER_BOUND_FINITE_SET_INT" SessionANT.Algmisc.«UPPER_BOUND_FINITE_SET_INT»
  "|- forall f s. FINITE s ==> (exists a. forall x. x IN s ==> f x <= a)"
#eval thm' "Algmisc.INT_DIVIDES_NUM_OF_INT_ABS" SessionANT.Algmisc.«INT_DIVIDES_NUM_OF_INT_ABS»
  "|- forall d n. d divides n <=> num_of_int (abs d) divides num_of_int (abs n)"

-- Ufd
#eval thm' "Ufd.UFD_COPRIME_MUL_POW" SessionANT.Ufd.«UFD_COPRIME_MUL_POW»
  "|- forall r a b c k.        UFD r /\\        a IN ring_carrier r /\\        b IN ring_carrier r /\\        c IN ring_carrier r /\\        ring_coprime r (a,b) /\\        ring_mul r a b = ring_pow r c k        ==> (exists u e.                 ring_unit r u /\\                 e IN ring_carrier r /\\                 a = ring_mul r u (ring_pow r e k))"
#eval thm' "Ufd.UFD_COPRIME_MUL_POW_ASSOCIATES" SessionANT.Ufd.«UFD_COPRIME_MUL_POW_ASSOCIATES»
  "|- forall r a b c k.        UFD r /\\        a IN ring_carrier r /\\        b IN ring_carrier r /\\        c IN ring_carrier r /\\        ring_coprime r (a,b) /\\        ring_mul r a b = ring_pow r c k        ==> (exists e.                 e IN ring_carrier r /\\ ring_associates r a (ring_pow r e k))"

-- Integral
#eval thm' "Integral.integral_element" SessionANT.Integral.«integral_element»
  "|- forall r h x r'.        integral_element (r,r') h x <=>        x IN ring_carrier r' /\\        (exists p.             p IN ring_carrier (poly_ring r (:1)) /\\             monic r p /\\             poly_extend (r,r') h (\\v. x) p = ring_0 r')"
#eval thm' "Integral.INTEGRAL_HOMOGENEOUS_SCALE" SessionANT.Integral.«INTEGRAL_HOMOGENEOUS_SCALE»
  "|- forall r p a b c n.        p IN ring_carrier r /\\        a IN ring_carrier r /\\        b IN ring_carrier r /\\        (forall i. i < n ==> c i IN ring_carrier r)        ==> ring_add r (ring_pow r (ring_mul r p a) n)            (ring_sum r {i | i < n}            (\\i.                 ring_mul r (c i)                 (ring_mul r (ring_pow r (ring_mul r p a) i)                 (ring_pow r (ring_mul r p b) (n - i))))) =            ring_mul r (ring_pow r p n)            (ring_add r (ring_pow r a n)            (ring_sum r {i | i < n}            (\\i.                 ring_mul r (c i)                 (ring_mul r (ring_pow r a i) (ring_pow r b (n - i))))))"

-- IntegralPrimes
#eval thm' "IntegralPrimes.INTEGRAL_DETERMINANT_TRICK_IDEAL" SessionANT.IntegralPrimes.«INTEGRAL_DETERMINANT_TRICK_IDEAL»
  "|- forall r s f j p g a t.        ring_homomorphism (r,s) f /\\        ring_ideal s j /\\        ring_ideal r p /\\        FINITE g /\\        g SUBSET ring_carrier s /\\        ring_1 s IN ring_span (r,s) f g /\\        t IN ring_carrier r /\\        (forall x y. x IN g /\\ y IN g ==> a x y IN p) /\\        (forall x.             x IN g             ==> ring_sub s (ring_mul s (f t) x)                 (ring_sum s g (\\y. ring_mul s (f (a x y)) y)) IN                 j)        ==> (exists d.                 d IN ring_carrier r /\\                 f d IN j /\\                 ring_sub r d (ring_pow r t (CARD g)) IN p)"
#eval thm' "IntegralPrimes.INTEGRAL_EXTENSION_GOING_UP" SessionANT.IntegralPrimes.«INTEGRAL_EXTENSION_GOING_UP»
  "|- forall r s f p p' q.        ring_homomorphism (r,s) f /\\        (forall y. y IN ring_carrier s ==> integral_element (r,s) f y) /\\        prime_ideal s q /\\        {x | x IN ring_carrier r /\\ f x IN q} = p /\\        prime_ideal r p' /\\        p SUBSET p'        ==> (exists q'.                 prime_ideal s q' /\\                 q SUBSET q' /\\                 {x | x IN ring_carrier r /\\ f x IN q'} = p')"

-- IdealArith
#eval thm' "IdealArith.ideal_prod" SessionANT.IdealArith.«ideal_prod»
  "|- forall r j k. ideal_prod r j k = ideal_generated r (ring_setmul r j k)"
#eval thm' "IdealArith.RING_MUL_IN_IDEAL_POW" SessionANT.IdealArith.«RING_MUL_IN_IDEAL_POW»
  "|- forall r j x y m n.        j SUBSET ring_carrier r /\\        x IN ideal_pow r j m /\\        y IN ideal_pow r j n        ==> ring_mul r x y IN ideal_pow r j (m + n)"

-- Hensel
#eval thm' "Hensel.RING_UNIT_QUOTIENT_RING_IDEAL_POW" SessionANT.Hensel.«RING_UNIT_QUOTIENT_RING_IDEAL_POW»
  "|- forall r j n x.        ring_ideal r j /\\ ~(n = 0) /\\ x IN ring_carrier r        ==> (ring_unit (quotient_ring r (ideal_pow r j n))             (ring_coset r (ideal_pow r j n) x) <=>             ring_unit (quotient_ring r j) (ring_coset r j x))"
#eval thm' "Hensel.POLY_EVAL_DERIV_VAR_POW_SUB_CONST" SessionANT.Hensel.«POLY_EVAL_DERIV_VAR_POW_SUB_CONST»
  "|- forall r n c.        c IN ring_carrier r        ==> poly_sub r (poly_pow r (poly_var r one) n) (poly_const r c) IN            ring_carrier (poly_ring r (:1)) /\\            (forall x.                 x IN ring_carrier r                 ==> poly_eval r                     (poly_sub r (poly_pow r (poly_var r one) n)                     (poly_const r c))                     x =                     ring_sub r (ring_pow r x n) c /\\                     poly_eval r                     (poly_deriv r                     (poly_sub r (poly_pow r (poly_var r one) n)                     (poly_const r c)))                     x =                     ring_mul r (ring_of_num r n) (ring_pow r x (n - 1)))"

-- Dedekind
#eval thm' "Dedekind.dedekind_domain" SessionANT.Dedekind.«dedekind_domain»
  "|- forall r.        dedekind_domain r <=>        integral_domain r /\\        noetherian_ring r /\\        integrally_closed r /\\        (forall p. prime_ideal r p /\\ ~(p = {ring_0 r}) ==> maximal_ideal r p)"
#eval thm' "Dedekind.DEDEKIND_IDEAL_FACTORIZATION" SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  "|- forall r j.        dedekind_domain r /\\ ring_ideal r j /\\ ~(j = {ring_0 r})        ==> FINITE {p | prime_ideal r p /\\ ~(p = {ring_0 r}) /\\ j SUBSET p} /\\            ideal_product r            {p | prime_ideal r p /\\ ~(p = {ring_0 r}) /\\ j SUBSET p}            (\\p. ideal_pow r p (ideal_valuation r p j)) =            j"

-- DedekindStruct
#eval thm' "DedekindStruct.DVR" SessionANT.DedekindStruct.«DVR»
  "|- forall r. DVR r <=> PID r /\\ local_ring r /\\ ~field r"
#eval thm' "DedekindStruct.DEDEKIND_BEZOUT_IFF_PID" SessionANT.DedekindStruct.«DEDEKIND_BEZOUT_IFF_PID»
  "|- forall r. dedekind_domain r ==> (bezout_ring r <=> PID r)"

-- DedekindLocal
#eval thm' "DedekindLocal.MAXIMAL_IDEAL_LOCALIZATION" SessionANT.DedekindLocal.«MAXIMAL_IDEAL_LOCALIZATION»
  "|- forall r s m.        ring_multsys r s /\\ maximal_ideal r m /\\ m INTER s = {}        ==> maximal_ideal (ring_localization r s)            {ring_localequiv r s (a,b) | a,b | a IN m /\\ b IN s}"
#eval thm' "DedekindLocal.DEDEKIND_LOCALIZATION" SessionANT.DedekindLocal.«DEDEKIND_LOCALIZATION»
  "|- forall r s.        dedekind_domain r /\\ ring_multsys r s /\\ ~(ring_0 r IN s)        ==> dedekind_domain (ring_localization r s)"

-- DedekindValuation
#eval thm' "DedekindValuation.dedekind_valuation" SessionANT.DedekindValuation.«dedekind_valuation»
  "|- forall k x h P r.        dedekind_valuation (r,k) h P x =        (@v.             forall a b.                 a IN ring_carrier r /\\                 b IN ring_carrier r /\\                 ~(a = ring_0 r) /\\                 ~(b = ring_0 r) /\\                 ring_mul k (h b) x = h a                 ==> v =                     &(ideal_valuation r P (ideal_generated r {a})) -                     &(ideal_valuation r P (ideal_generated r {b})))"
#eval thm' "DedekindValuation.DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS" SessionANT.DedekindValuation.«DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS»
  "|- forall r f.        dedekind_domain r /\\        FINITE {p | prime_ideal r p /\\ ~(p = {ring_0 r}) /\\ ~(f p = 0)}        ==> (exists j.                 ring_ideal r j /\\                 ~(j = {ring_0 r}) /\\                 (forall p.                      prime_ideal r p /\\ ~(p = {ring_0 r})                      ==> ideal_valuation r p j = f p))"

-- ValuationRing
#eval thm' "ValuationRing.valuation_ring" SessionANT.ValuationRing.«valuation_ring»
  "|- forall r.        valuation_ring r <=>        integral_domain r /\\        (forall a b.             a IN ring_carrier r /\\ b IN ring_carrier r             ==> ring_divides r a b \\/ ring_divides r b a)"
#eval thm' "ValuationRing.VALUATION_SUBRING_INTEGRAL_ELEMENT" SessionANT.ValuationRing.«VALUATION_SUBRING_INTEGRAL_ELEMENT»
  "|- forall k b x.        valuation_subring k b /\\        integral_element (subring_generated k b,k) I x        ==> x IN b"

-- IdealNorm
#eval thm' "IdealNorm.ideal_norm" SessionANT.IdealNorm.«ideal_norm»
  "|- forall r j. ideal_norm r j = CARD (ring_carrier (quotient_ring r j))"
#eval thm' "IdealNorm.IDEAL_NORM_SUBSET_DIVIDES" SessionANT.IdealNorm.«IDEAL_NORM_SUBSET_DIVIDES»
  "|- forall r j k.        ring_ideal r j /\\        ring_ideal r k /\\        j SUBSET k /\\        FINITE (ring_carrier (quotient_ring r j))        ==> ideal_norm r k divides ideal_norm r j"

-- IdealEuler
#eval thm' "IdealEuler.IDEAL_EULER" SessionANT.IdealEuler.«IDEAL_EULER»
  "|- forall r j x.        ring_ideal r j /\\        FINITE (ring_carrier (quotient_ring r j)) /\\        x IN ring_carrier r /\\        ring_setadd r (ideal_generated r {x}) j = ring_carrier r        ==> ring_sub r            (ring_pow r x (CARD {u | ring_unit (quotient_ring r j) u}))            (ring_1 r) IN            j"
#eval thm' "IdealEuler.CARD_UNITS_QUOTIENT_RING_COPRIME" SessionANT.IdealEuler.«CARD_UNITS_QUOTIENT_RING_COPRIME»
  "|- forall r j k.        ring_ideal r j /\\        ring_ideal r k /\\        ring_setadd r j k = ring_carrier r /\\        FINITE (ring_carrier (quotient_ring r j)) /\\        FINITE (ring_carrier (quotient_ring r k))        ==> CARD {u | ring_unit (quotient_ring r (ideal_prod r j k)) u} =            CARD {u | ring_unit (quotient_ring r j) u} *            CARD {u | ring_unit (quotient_ring r k) u}"

-- DedekindAbsolute
#eval thm' "DedekindAbsolute.absolute_value" SessionANT.DedekindAbsolute.«absolute_value»
  "|- forall k f.        absolute_value k f <=>        (forall x.             x IN ring_carrier k ==> &0 <= f x /\\ (f x = &0 <=> x = ring_0 k)) /\\        (forall x y.             x IN ring_carrier k /\\ y IN ring_carrier k             ==> f (ring_mul k x y) = f x * f y) /\\        (forall x y.             x IN ring_carrier k /\\ y IN ring_carrier k             ==> f (ring_add k x y) <= f x + f y)"
#eval thm' "DedekindAbsolute.ABSOLUTE_VALUE_INV" SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_INV»
  "|- forall k f x.        field k /\\ absolute_value k f /\\ x IN ring_carrier k        ==> f (ring_inv k x) = inv (f x)"

-- Zlattice
#eval thm' "Zlattice.int_lattice" SessionANT.Zlattice.«int_lattice»
  "|- forall s L.        int_lattice s L <=>        L SUBSET {x | forall i. ~(i IN s) ==> x i = &0} /\\        (\\i. &0) IN L /\\        (forall x y. x IN L /\\ y IN L ==> (\\i. x i - y i) IN L)"
#eval thm' "Zlattice.INT_MATRIX_IMAGE_INJECTIVE" SessionANT.Zlattice.«INT_MATRIX_IMAGE_INJECTIVE»
  "|- forall s M z z'.        FINITE s /\\        ~(ring_det integer_ring s M = &0) /\\        (forall i.             i IN s ==> isum s (\\j. M i j * z j) = isum s (\\j. M i j * z' j))        ==> (forall j. j IN s ==> z j = z' j)"

-- LinearForms
#eval thm' "LinearForms.PRODUCT_SUB_BOUND" SessionANT.LinearForms.«PRODUCT_SUB_BOUND»
  "|- forall s f g B.        FINITE s /\\ (forall i. i IN s ==> abs (f i) <= B /\\ abs (g i) <= B)        ==> abs (product s f - product s g) <=            B pow (CARD s - 1) * sum s (\\i. abs (f i - g i))"
#eval thm' "LinearForms.REAL_DET_SCHUR_COMPLEMENT" SessionANT.LinearForms.«REAL_DET_SCHUR_COMPLEMENT»
  "|- forall a t A.        FINITE t /\\ ~(a IN t) /\\ ~(A a a = &0)        ==> ring_det real_ring (a INSERT t) A =            A a a * ring_det real_ring t (\\i j. A i j - A i a * A a j / A a a)"

-- HermiteInequality
#eval thm' "HermiteInequality.QUADRATIC_FORM_DET_POS" SessionANT.HermiteInequality.«QUADRATIC_FORM_DET_POS»
  "|- forall s A.        FINITE s /\\        (forall i j. i IN s /\\ j IN s ==> A i j = A j i) /\\        (forall x.             (exists i. i IN s /\\ ~(x i = &0))             ==> &0 < sum s (\\i. sum s (\\j. A i j * x i * x j)))        ==> &0 < ring_det real_ring s A"
#eval thm' "HermiteInequality.QUADRATIC_FORM_MINIMAL_VECTOR" SessionANT.HermiteInequality.«QUADRATIC_FORM_MINIMAL_VECTOR»
  "|- forall s A.        FINITE s /\\        ~(s = {}) /\\        (forall i j. i IN s /\\ j IN s ==> A i j = A j i) /\\        (forall x.             (exists i. i IN s /\\ ~(x i = &0))             ==> &0 < sum s (\\i. sum s (\\j. A i j * x i * x j)))        ==> (exists x.                 (forall i. ~(i IN s) ==> x i = &0) /\\                 (exists i. i IN s /\\ ~(x i = &0)) /\\                 (forall y.                      (forall i. ~(i IN s) ==> y i = &0) /\\                      (exists i. i IN s /\\ ~(y i = &0))                      ==> sum s                          (\\i.                               sum s                               (\\j.                                    A i j *                                    real_of_int (x i) *                                    real_of_int (x j))) <=                          sum s                          (\\i.                               sum s                               (\\j.                                    A i j *                                    real_of_int (y i) *                                    real_of_int (y j)))))"

-- Numfield
#eval thm' "Numfield.number_field" SessionANT.Numfield.«number_field»
  "|- forall k.        number_field k <=>        ring_char k = 0 /\\        finite_extension (subfield_generated k {ring_0 k},k) I"
#eval thm' "Numfield.RING_OF_INT_IN_RING_OF_INTEGERS" SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  "|- forall k n. ring_of_int k n IN ring_carrier (ring_of_integers k)"

-- DedekindExtension
#eval thm' "DedekindExtension.INTEGRAL_ELEMENT_DENOMINATOR" SessionANT.DedekindExtension.«INTEGRAL_ELEMENT_DENOMINATOR»
  "|- forall r k l h g x.        field_of_fractions (r,k) h /\\        ring_homomorphism (k,l) g /\\        integral_element (k,l) g x        ==> (exists d.                 d IN ring_carrier r /\\                 ~(d = ring_0 r) /\\                 integral_element (r,l) (g o h) (ring_mul l (g (h d)) x))"
#eval thm' "DedekindExtension.FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE" SessionANT.DedekindExtension.«FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE»
  "|- forall r k l h g.        field_of_fractions (r,k) h /\\ algebraic_extension (k,l) g        ==> field_of_fractions            (subring_generated l {y | integral_element (r,l) (g o h) y},l)            I"

-- RingOfIntegers
#eval thm' "RingOfIntegers.QUOTIENT_RING_HAS_SIZE_INT_LINEAR" SessionANT.RingOfIntegers.«QUOTIENT_RING_HAS_SIZE_INT_LINEAR»
  "|- forall r j psi s N.        ring_ideal r j /\\        (forall z. psi z IN ring_carrier r) /\\        (forall x y. psi (\\i. x i - y i) = ring_sub r (psi x) (psi y)) /\\        (forall x.             x IN ring_carrier r             ==> (exists z. (forall i. ~(i IN s) ==> z i = &0) /\\ psi z = x))        ==> (ring_carrier (quotient_ring r j) HAS_SIZE N <=>             int_cosets s             {z | (forall i. ~(i IN s) ==> z i = &0) /\\ psi z IN j} HAS_SIZE             N)"
#eval thm' "RingOfIntegers.RING_OF_INTEGERS_FREE" SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  "|- forall k.        number_field k        ==> (exists w.                 free_basis (integer_ring,ring_of_integers k) (ring_of_int k)                 (extension_degree (subfield_generated k {ring_0 k},k) I)                 w)"

-- NormIndex
#eval thm' "NormIndex.FREE_BASIS_IDEAL_NORM_COORD_MUL" SessionANT.NormIndex.«FREE_BASIS_IDEAL_NORM_COORD_MUL»
  "|- forall r n w f a x.        free_basis (integer_ring,r) (ring_of_int r) n w /\\        (forall x i.             f x i =             (if i < n              then basis_coordinates (integer_ring,r) (ring_of_int r) n w x i              else &0)) /\\        a IN ring_carrier r /\\        x IN ring_carrier r        ==> f (ring_mul r a x) =            (\\i.                 if i < n                 then isum {i | i < n}                      (\\j.                           mul_matrix (integer_ring,r) (ring_of_int r) n w a i                           j *                           f x j)                 else &0)"
#eval thm' "NormIndex.NUMBER_FIELD_TRACE_INTEGRAL_BASIS" SessionANT.NormIndex.«NUMBER_FIELD_TRACE_INTEGRAL_BASIS»
  "|- forall k n w x.        number_field k /\\        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\\        x IN ring_carrier (ring_of_integers k)        ==> algebra_trace (subfield_generated k {ring_0 k},k) I x =            ring_of_int k            (algebra_trace (integer_ring,ring_of_integers k) (ring_of_int k)            x)"

-- Classgroup
#eval thm' "Classgroup.ideal_classes" SessionANT.Classgroup.«ideal_classes»
  "|- forall r.        ideal_classes r =        {ideal_class r j | j | ring_ideal r j /\\ ~(j = {ring_0 r})}"
#eval thm' "Classgroup.NUMBER_FIELD_IDEAL_SMALL_ELEMENT" SessionANT.Classgroup.«NUMBER_FIELD_IDEAL_SMALL_ELEMENT»
  "|- forall k n w B j.        number_field k /\\        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\\        (forall i l m.             i < n /\\ l < n /\\ m < n             ==> abs                 (mul_matrix (integer_ring,ring_of_integers k) (ring_of_int k)                  n                  w                  (w i)                  m                 l) <=                 B) /\\        ring_ideal (ring_of_integers k) j /\\        ~(j = {ring_0 k})        ==> (exists a.                 a IN j /\\                 ~(a = ring_0 k) /\\                 &(ideal_norm (ring_of_integers k)                  (ideal_generated (ring_of_integers k) {a})) <=                 (&(FACT n) * (&n * B) pow n) *                 &(ideal_norm (ring_of_integers k) j))"

-- NfValuation
#eval thm' "NfValuation.RING_OF_INTEGERS_FRACTION_FIELD" SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  "|- forall k.        ring_monomorphism (ring_of_integers k,k) I /\\        (number_field k         ==> dedekind_domain (ring_of_integers k) /\\             field_of_fractions (ring_of_integers k,k) I)"
#eval thm' "NfValuation.NUMBER_FIELD_VALUATION_ADD_STRICT" SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_ADD_STRICT»
  "|- forall k P x y.        number_field k /\\        prime_ideal (ring_of_integers k) P /\\        ~(P = {ring_0 k}) /\\        x IN ring_carrier k /\\        ~(x = ring_0 k) /\\        y IN ring_carrier k /\\        dedekind_valuation (ring_of_integers k,k) I P x <        dedekind_valuation (ring_of_integers k,k) I P y        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_add k x y) =            dedekind_valuation (ring_of_integers k,k) I P x"

-- ClassgroupGroup
#eval thm' "ClassgroupGroup.class_group" SessionANT.ClassgroupGroup.«class_group»
  "|- forall r.        class_group r =        group        (ideal_classes r,         ideal_class r (ring_carrier r),         (\\c.              {k | ring_ideal r k /\\                   (exists j.                        j IN c /\\                        ring_carrier r IN ideal_class r (ideal_prod r j k))}),         (\\c d.              {l | exists j k.                       j IN c /\\                       k IN d /\\                       l IN ideal_class r (ideal_prod r j k)}))"
#eval thm' "ClassgroupGroup.DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER" SessionANT.ClassgroupGroup.«DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER»
  "|- forall r j.        dedekind_domain r /\\ FINITE (ideal_classes r) /\\ ring_ideal r j        ==> principal_ideal r (ideal_pow r j (class_number r))"

-- FractionalIdeals
#eval thm' "FractionalIdeals.fractional_ideal" SessionANT.FractionalIdeals.«fractional_ideal»
  "|- forall J k h r.        fractional_ideal (r,k) h J <=>        field_of_fractions (r,k) h /\\        J SUBSET ring_carrier k /\\        ~(J = {ring_0 k}) /\\        ring_0 k IN J /\\        (forall x y. x IN J /\\ y IN J ==> ring_add k x y IN J) /\\        (forall a x.             a IN ring_carrier r /\\ x IN J ==> ring_mul k (h a) x IN J) /\\        (exists d.             d IN ring_carrier r /\\             ~(d = ring_0 r) /\\             (forall x.                  x IN J ==> ring_mul k (h d) x IN IMAGE h (ring_carrier r)))"
#eval thm' "FractionalIdeals.FRACTIONAL_IDEAL_VALUATION_IMAGE" SessionANT.FractionalIdeals.«FRACTIONAL_IDEAL_VALUATION_IMAGE»
  "|- forall r k h P j.        dedekind_domain r /\\        field_of_fractions (r,k) h /\\        prime_ideal r P /\\        ~(P = {ring_0 r}) /\\        ring_ideal r j /\\        ~(j = {ring_0 r})        ==> fractional_ideal_valuation (r,k) h P (IMAGE h j) =            &(ideal_valuation r P j)"

-- DedekindCriteria
#eval thm' "DedekindCriteria.DEDEKIND_SEMILOCAL_IMP_PID" SessionANT.DedekindCriteria.«DEDEKIND_SEMILOCAL_IMP_PID»
  "|- forall r. dedekind_domain r /\\ FINITE {m | maximal_ideal r m} ==> PID r"
#eval thm' "DedekindCriteria.INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL" SessionANT.DedekindCriteria.«INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL»
  "|- forall r p.        integral_domain r /\\        (forall j.             ring_ideal r j /\\ ~(j = {ring_0 r})             ==> (exists k e.                      ring_ideal r k /\\                      e IN ring_carrier r /\\                      ~(e = ring_0 r) /\\                      ideal_prod r j k = ideal_generated r {e})) /\\        prime_ideal r p /\\        ~(p = {ring_0 r})        ==> maximal_ideal r p"

-- PrimeSplit
#eval thm' "PrimeSplit.ramification_index" SessionANT.PrimeSplit.«ramification_index»
  "|- forall s r h P.        ramification_index (r,s) h P =        ideal_valuation s P        (ideal_generated s (IMAGE h {x | x IN ring_carrier r /\\ h x IN P}))"
#eval thm' "PrimeSplit.NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE" SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE»
  "|- forall k P.        number_field k /\\        prime_ideal (ring_of_integers k) P /\\        ~(P = {ring_0 k})        ==> (residue_degree (integer_ring,ring_of_integers k) (ring_of_int k)             P =             1 <=>             prime (ideal_norm (ring_of_integers k) P))"

-- Discriminant
#eval thm' "Discriminant.number_field_discriminant" SessionANT.Discriminant.«number_field_discriminant»
  "|- forall k.        number_field_discriminant k =        (@d.             forall n w.                 free_basis (integer_ring,ring_of_integers k) (ring_of_int k)                 n                 w                 ==> basis_discriminant (integer_ring,ring_of_integers k)                     (ring_of_int k)                     n                     w =                     d)"
#eval thm' "Discriminant.NUMBER_FIELD_INDEX_DETERMINANT" SessionANT.Discriminant.«NUMBER_FIELD_INDEX_DETERMINANT»
  "|- forall k n g.        number_field k /\\        free_basis (subfield_generated k {ring_0 k},k) I n g /\\        (forall i. i < n ==> g i IN ring_carrier (ring_of_integers k))        ==> (exists d.                 ~(d = &0) /\\                 basis_discriminant (subfield_generated k {ring_0 k},k) I n g =                 ring_of_int k (d pow 2 * number_field_discriminant k) /\\                 {ring_coset (ring_of_integers k)                  {ring_sum k {i | i < n}                   (\\i. ring_mul k (ring_of_int k (c i)) (g i)) | c IN                                                                  (:num->int)}                  x | x | x IN ring_carrier (ring_of_integers k)} HAS_SIZE                 num_of_int (abs d) /\\                 (forall p.                      prime p                      ==> (ring_setadd (ring_of_integers k)                           {ring_sum k {i | i < n}                            (\\i. ring_mul k (ring_of_int k (c i)) (g i)) |                            c IN                           (:num->int)}                           (ideal_generated (ring_of_integers k)                           {ring_of_num k p}) =                           ring_carrier (ring_of_integers k) <=>                           ~(&p divides d))))"

-- PowerBasis
#eval thm' "PowerBasis.NUMBER_FIELD_TRACE_HOMOMORPHISMS" SessionANT.PowerBasis.«NUMBER_FIELD_TRACE_HOMOMORPHISMS»
  "|- forall k l E g x.        number_field k /\\        field l /\\        E HAS_SIZE extension_degree (subfield_generated k {ring_0 k},k) I /\\        (forall h. h IN E ==> ring_homomorphism (k,l) h) /\\        E SUBSET EXTENSIONAL (ring_carrier k) /\\        ring_homomorphism (k,l) g /\\        x IN ring_carrier k        ==> g (algebra_trace (subfield_generated k {ring_0 k},k) I x) =            ring_sum l E (\\h. h x)"
#eval thm' "PowerBasis.NUMBER_FIELD_FREE_BASIS_POWERS" SessionANT.PowerBasis.«NUMBER_FIELD_FREE_BASIS_POWERS»
  "|- forall k a.        number_field k /\\        a IN ring_carrier k /\\        poly_deg (subfield_generated k {ring_0 k})        (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =        extension_degree (subfield_generated k {ring_0 k},k) I        ==> free_basis (subfield_generated k {ring_0 k},k) I            (extension_degree (subfield_generated k {ring_0 k},k) I)            (\\i. ring_pow k a i)"

-- TraceForm
#eval thm' "TraceForm.EXTENSION_LINCOMB_PROD_RING" SessionANT.TraceForm.«EXTENSION_LINCOMB_PROD_RING»
  "|- forall k l1 l2 h1 h2 n1 n2 g1 g2 c.        ring_homomorphism (k,l1) h1 /\\        ring_homomorphism (k,l2) h2 /\\        (forall i. i < n1 ==> g1 i IN ring_carrier l1) /\\        (forall i. i < n2 ==> g2 i IN ring_carrier l2) /\\        (forall i. i < n1 + n2 ==> c i IN ring_carrier k)        ==> ring_sum (prod_ring l1 l2) {i | i < n1 + n2}            (\\i.                 ring_mul (prod_ring l1 l2) (h1 (c i),h2 (c i))                 (if i < n1 then g1 i,ring_0 l2 else ring_0 l1,g2 (i - n1))) =            ring_sum l1 {i | i < n1} (\\i. ring_mul l1 (h1 (c i)) (g1 i)),            ring_sum l2 {i | i < n2}            (\\i. ring_mul l2 (h2 (c (n1 + i))) (g2 i))"
#eval thm' "TraceForm.ALGEBRA_TRACE_PROD_RING" SessionANT.TraceForm.«ALGEBRA_TRACE_PROD_RING»
  "|- forall k l1 l2 h1 h2 n1 n2 g1 g2 x1 x2.        ring_homomorphism (k,l1) h1 /\\        ring_homomorphism (k,l2) h2 /\\        free_basis (k,l1) h1 n1 g1 /\\        free_basis (k,l2) h2 n2 g2 /\\        x1 IN ring_carrier l1 /\\        x2 IN ring_carrier l2        ==> algebra_trace (k,prod_ring l1 l2) (\\a. h1 a,h2 a) (x1,x2) =            ring_add k (algebra_trace (k,l1) h1 x1)            (algebra_trace (k,l2) h2 x2)"

-- FiniteFieldTrace
#eval thm' "FiniteFieldTrace.ALGEBRA_TRACE_FINITE_FIELD_NONZERO" SessionANT.FiniteFieldTrace.«ALGEBRA_TRACE_FINITE_FIELD_NONZERO»
  "|- forall k l h n g.        field k /\\        field l /\\        FINITE (ring_carrier l) /\\        ring_homomorphism (k,l) h /\\        free_basis (k,l) h n g        ==> (exists x.                 x IN ring_carrier l /\\ ~(algebra_trace (k,l) h x = ring_0 k))"
#eval thm' "FiniteFieldTrace.ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO" SessionANT.FiniteFieldTrace.«ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO»
  "|- forall f r g n G P Q.        field f /\\        FINITE (ring_carrier f) /\\        ring_homomorphism (f,quotient_ring r (P INTER Q)) g /\\        free_basis (f,quotient_ring r (P INTER Q)) g n G /\\        maximal_ideal r P /\\        ring_ideal r Q /\\        ring_setadd r P Q = ring_carrier r        ==> (exists x.                 x IN Q /\\                 ~(algebra_trace (f,quotient_ring r (P INTER Q)) g                   (ring_coset r (P INTER Q) x) =                   ring_0 f))"

-- Ramification
#eval thm' "Ramification.RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING" SessionANT.Ramification.«RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING»
  "|- forall r m.        ring_homomorphism        (integer_mod_ring m,         quotient_ring r (ideal_generated r {ring_of_num r m}))        (ring_of_int (quotient_ring r (ideal_generated r {ring_of_num r m}))) /\\        (forall a.             ring_coset r (ideal_generated r {ring_of_num r m})             (ring_of_int r a) =             ring_of_int             (quotient_ring r (ideal_generated r {ring_of_num r m}))             (a rem &m))"
#eval thm' "Ramification.ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD" SessionANT.Ramification.«ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD»
  "|- forall r n w p x m.        free_basis (integer_ring,r) (ring_of_int r) n w /\\        prime p /\\        x IN ring_carrier r /\\        ~(m = 0) /\\        ring_pow r x m IN ideal_generated r {ring_of_num r p}        ==> &p divides algebra_trace (integer_ring,r) (ring_of_int r) x"

-- RelativeSplit
#eval thm' "RelativeSplit.RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE" SessionANT.RelativeSplit.«RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE»
  "|- forall k l h x.        ring_monomorphism (k,l) h /\\ x IN ring_carrier k        ==> (h x IN ring_carrier (ring_of_integers l) <=>             x IN ring_carrier (ring_of_integers k))"
#eval thm' "RelativeSplit.NUMBER_FIELD_VALUATION_RAMIFICATION_INDEX" SessionANT.RelativeSplit.«NUMBER_FIELD_VALUATION_RAMIFICATION_INDEX»
  "|- forall k l h Q x.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        prime_ideal (ring_of_integers l) Q /\\        ~(Q = {ring_0 l}) /\\        x IN ring_carrier k /\\        ~(x = ring_0 k)        ==> dedekind_valuation (ring_of_integers l,l) I Q (h x) =            &(ramification_index (ring_of_integers k,ring_of_integers l) h Q) *            dedekind_valuation (ring_of_integers k,k) I            {y | y IN ring_carrier (ring_of_integers k) /\\ h y IN Q}            x"

-- RelativeDegree
#eval thm' "RelativeDegree.NUMBER_FIELD_INDEPENDENT_MOD_IDEAL" SessionANT.RelativeDegree.«NUMBER_FIELD_INDEPENDENT_MOD_IDEAL»
  "|- forall k l h j s w.        number_field k /\\        ring_homomorphism (k,l) h /\\        ring_ideal (ring_of_integers k) j /\\        ~(j = ring_carrier (ring_of_integers k)) /\\        FINITE s /\\        (forall i. i IN s ==> w i IN ring_carrier l) /\\        (forall u.             (forall i. i IN s ==> u i IN ring_carrier (ring_of_integers k)) /\\             ring_sum l s (\\i. ring_mul l (h (u i)) (w i)) = ring_0 l             ==> (forall i. i IN s ==> u i IN j))        ==> (forall c.                 (forall i. i IN s ==> c i IN ring_carrier k) /\\                 ring_sum l s (\\i. ring_mul l (h (c i)) (w i)) = ring_0 l                 ==> (forall i. i IN s ==> c i = ring_0 k))"
#eval thm' "RelativeDegree.NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE" SessionANT.RelativeDegree.«NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE»
  "|- forall k l h j.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        ring_ideal (ring_of_integers k) j /\\        ~(j = {ring_0 k})        ==> ideal_norm (ring_of_integers l)            (ideal_generated (ring_of_integers l) (IMAGE h j)) <=            ideal_norm (ring_of_integers k) j EXP extension_degree (k,l) h"

-- Integrality
#eval thm' "Integrality.RING_OF_INTEGERS_INTEGRAL_ELEMENT" SessionANT.Integrality.«RING_OF_INTEGERS_INTEGRAL_ELEMENT»
  "|- forall k l h x.        ring_homomorphism (k,l) h        ==> (integral_element (ring_of_integers k,l) h x <=>             x IN ring_carrier (ring_of_integers l))"
#eval thm' "Integrality.RING_OF_INTEGERS_UNIT_NORM" SessionANT.Integrality.«RING_OF_INTEGERS_UNIT_NORM»
  "|- forall k l h x.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        x IN ring_carrier (ring_of_integers l)        ==> (ring_unit (ring_of_integers l) x <=>             ring_unit (ring_of_integers k) (algebra_norm (k,l) h x))"

-- Different
#eval thm' "Different.number_field_codifferent" SessionANT.Different.«number_field_codifferent»
  "|- forall h l k.        number_field_codifferent (k,l) h =        {x | x IN ring_carrier l /\\             (forall y.                  y IN ring_carrier (ring_of_integers l)                  ==> algebra_trace (k,l) h (ring_mul l x y) IN                      ring_carrier (ring_of_integers k))}"
#eval thm' "Different.NUMBER_FIELD_CODIFFERENT_DIFFERENT" SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_DIFFERENT»
  "|- forall k l h.        field k /\\ number_field l /\\ ring_homomorphism (k,l) h        ==> number_field_codifferent (k,l) h =            {x | x IN ring_carrier l /\\                 (forall y.                      y IN number_field_different (k,l) h                      ==> ring_mul l x y IN ring_carrier (ring_of_integers l))}"

-- DedekindKummer
#eval thm' "DedekindKummer.RING_EPIMORPHISM_KERNEL_EQ" SessionANT.DedekindKummer.«RING_EPIMORPHISM_KERNEL_EQ»
  "|- forall r r' f j.        ring_epimorphism (r,r') f /\\        ring_ideal r j /\\        j SUBSET ring_kernel (r,r') f /\\        FINITE (ring_carrier (quotient_ring r j)) /\\        CARD (ring_carrier (quotient_ring r j)) = CARD (ring_carrier r')        ==> ring_kernel (r,r') f = j"
#eval thm' "DedekindKummer.DEDEKIND_KUMMER_KERNEL" SessionANT.DedekindKummer.«DEDEKIND_KUMMER_KERNEL»
  "|- forall r s h k f p x m.        ring_homomorphism (r,s) h /\\        field k /\\        FINITE (ring_carrier k) /\\        ring_epimorphism (r,k) f /\\        ring_kernel (r,k) f = p /\\        x IN ring_carrier s /\\        m IN ring_carrier (poly_ring r (:1)) /\\        monic r m /\\        poly_extend (r,s) h (\\v. x) m = ring_0 s /\\        ideal_norm s (ideal_generated s (IMAGE h p)) =        CARD (ring_carrier k) EXP poly_deg r m /\\        ring_setadd s        (ring_carrier        (subring_generated s (x INSERT IMAGE h (ring_carrier r))))        (ideal_generated s (IMAGE h p)) =        ring_carrier s        ==> (exists ph.                 ring_epimorphism                 (poly_ring k (:1),                  quotient_ring s (ideal_generated s (IMAGE h p)))                 ph /\\                 (forall g.                      g IN ring_carrier (poly_ring r (:1))                      ==> ph (f o g) =                          ring_coset s (ideal_generated s (IMAGE h p))                          (poly_extend (r,s) h (\\v. x) g)) /\\                 ring_kernel                 (poly_ring k (:1),                  quotient_ring s (ideal_generated s (IMAGE h p)))                 ph =                 ideal_generated (poly_ring k (:1)) {f o m})"

-- PowerBasisIndex
#eval thm' "PowerBasisIndex.NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS" SessionANT.PowerBasisIndex.«NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS»
  "|- forall k a f m.        number_field k /\\        a IN ring_carrier k /\\        f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\\        m = extension_degree (subfield_generated k {ring_0 k},k) I /\\        poly_deg (subfield_generated k {ring_0 k}) f = m        ==> (exists l g e.                 field l /\\                 ring_monomorphism (k,l) g /\\                 (forall i.                      i < m                      ==> ring_homomorphism (k,l) (e i) /\\                          e i a IN ring_carrier l) /\\                 (forall i y.                      i < m /\\                      y IN ring_carrier (subfield_generated k {ring_0 k})                      ==> e i y = g y) /\\                 (forall u v. u < m /\\ v < m ==> (e u a = e v a <=> u = v)) /\\                 g o f =                 ring_product (poly_ring l (:1)) {i | i < m}                 (\\i. poly_sub l (poly_var l one) (poly_const l (e i a))) /\\                 (forall i.                      i < m                      ==> e i                          (poly_extend (subfield_generated k {ring_0 k},k) I                           (\\v. a)                          (poly_deriv (subfield_generated k {ring_0 k}) f)) =                          ring_product l ({t | t < m} DELETE i)                          (\\t. ring_sub l (e i a) (e t a))) /\\                 (forall x.                      x IN ring_carrier k                      ==> g                          (algebra_trace (subfield_generated k {ring_0 k},k) I                          x) =                          ring_sum l {i | i < m} (\\i. e i x)))"
#eval thm' "PowerBasisIndex.NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME" SessionANT.PowerBasisIndex.«NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME»
  "|- forall k a m p.        number_field k /\\        a IN ring_carrier k /\\        subfield_generated k {a} = k /\\        m IN ring_carrier (poly_ring integer_ring (:1)) /\\        monic integer_ring m /\\        poly_deg integer_ring m =        extension_degree (subfield_generated k {ring_0 k},k) I /\\        poly_extend (integer_ring,k) (ring_of_int k) (\\v. a) m = ring_0 k /\\        prime p /\\        ~(&p pow 2 divides poly_discriminant integer_ring m)        ==> ring_setadd (ring_of_integers k)            (ring_carrier (subring_generated k {a}))            (ideal_generated (ring_of_integers k) {ring_of_num k p}) =            ring_carrier (ring_of_integers k)"

-- DifferentExtension
#eval thm' "DifferentExtension.RING_OF_INTEGERS_BASIS_MOD_PRIME" SessionANT.DifferentExtension.«RING_OF_INTEGERS_BASIS_MOD_PRIME»
  "|- forall k l h p.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        prime_ideal (ring_of_integers k) p /\\        ~(p = {ring_0 k})        ==> (exists w.                 (forall i.                      i < extension_degree (k,l) h                      ==> w i IN ring_carrier (ring_of_integers l)) /\\                 (forall i j.                      i < extension_degree (k,l) h /\\                      j < extension_degree (k,l) h /\\                      w i = w j                      ==> i = j) /\\                 (forall x.                      x IN ring_carrier (ring_of_integers l)                      ==> (exists c.                               (forall i.                                    c i IN ring_carrier (ring_of_integers k)) /\\                               ring_sub l x                               (ring_sum l {i | i < extension_degree (k,l) h}                               (\\i. ring_mul l (h (c i)) (w i))) IN                               ideal_generated (ring_of_integers l)                               (IMAGE h p))) /\\                 (forall c.                      (forall i. c i IN ring_carrier (ring_of_integers k)) /\\                      ring_sum l {i | i < extension_degree (k,l) h}                      (\\i. ring_mul l (h (c i)) (w i)) IN                      ideal_generated (ring_of_integers l) (IMAGE h p)                      ==> (forall i.                               i < extension_degree (k,l) h ==> c i IN p)))"
#eval thm' "DifferentExtension.NUMBER_FIELD_CODIFFERENT_TRACE_DIV" SessionANT.DifferentExtension.«NUMBER_FIELD_CODIFFERENT_TRACE_DIV»
  "|- forall k l h c y x.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        c IN ring_carrier (ring_of_integers k) /\\        ~(c = ring_0 k) /\\        y IN ring_carrier (ring_of_integers k) /\\        x IN ring_carrier (ring_of_integers l)        ==> ((forall z.                  z IN ring_carrier (ring_of_integers l)                  ==> ring_mul k y (algebra_trace (k,l) h (ring_mul l x z)) IN                      ideal_generated (ring_of_integers k) {c}) <=>             (forall d.                  d IN number_field_different (k,l) h                  ==> ring_mul l (h y) (ring_mul l x d) IN                      ideal_generated (ring_of_integers l) {h c}))"

-- DifferentExponent
#eval thm' "DifferentExponent.DEDEKIND_IDEAL_POW_LEVEL_SPAN" SessionANT.DifferentExponent.«DEDEKIND_IDEAL_POW_LEVEL_SPAN»
  "|- forall r P t p f g b e.        dedekind_domain r /\\        prime_ideal r P /\\        ~(P = {ring_0 r}) /\\        t IN P /\\        ~(t IN ideal_pow r P 2) /\\        free_basis (integer_mod_ring p,quotient_ring r P)        (ring_of_int (quotient_ring r P))        f        g /\\        (forall j. b j IN ring_carrier r) /\\        (forall j. j < f ==> ring_coset r P (b j) = g j)        ==> (forall i y.                 i <= e /\\ y IN ideal_pow r P i                 ==> (exists c.                          (forall s. s DIV f < i ==> c s = &0) /\\                          ring_sub r y                          (ring_sum r {s | s < f * e}                          (\\s.                               ring_mul r (ring_of_int r (c s))                               (ring_mul r (ring_pow r t (s DIV f))                               (b (s MOD f))))) IN                          ideal_pow r P e))"
#eval thm' "DifferentExponent.ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW" SessionANT.DifferentExponent.«ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW»
  "|- forall r n w p P Q e.        dedekind_domain r /\\        free_basis (integer_ring,r) (ring_of_int r) n w /\\        prime p /\\        prime_ideal r P /\\        ~(P = {ring_0 r}) /\\        ring_ideal r Q /\\        ring_setadd r (ideal_pow r P e) Q = ring_carrier r /\\        ideal_pow r P e INTER Q = ideal_generated r {ring_of_num r p} /\\        ~(p divides e)        ==> (exists x.                 x IN Q /\\                 ~(&p divides                   algebra_trace (integer_ring,r) (ring_of_int r) x))"

-- Eisenstein
#eval thm' "Eisenstein.NUMBER_FIELD_EISENSTEIN_VALUATION" SessionANT.Eisenstein.«NUMBER_FIELD_EISENSTEIN_VALUATION»
  "|- forall k a m p P.        number_field k /\\        a IN ring_carrier k /\\        m IN ring_carrier (poly_ring integer_ring (:1)) /\\        monic integer_ring m /\\        poly_extend (integer_ring,k) (ring_of_int k) (\\v. a) m = ring_0 k /\\        prime p /\\        (forall i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\\        ~(&p pow 2 divides coeff 0 m) /\\        prime_ideal (ring_of_integers k) P /\\        ring_of_num k p IN P        ==> a IN ring_carrier (ring_of_integers k) /\\            ~(a = ring_0 k) /\\            1 <=            ideal_valuation (ring_of_integers k) P            (ideal_generated (ring_of_integers k) {a}) /\\            poly_deg integer_ring m *            ideal_valuation (ring_of_integers k) P            (ideal_generated (ring_of_integers k) {a}) =            ramification_index (integer_ring,ring_of_integers k)            (ring_of_int k)            P"
#eval thm' "Eisenstein.NUMBER_FIELD_EISENSTEIN_INDEPENDENT" SessionANT.Eisenstein.«NUMBER_FIELD_EISENSTEIN_INDEPENDENT»
  "|- forall k a m p c.        number_field k /\\        a IN ring_carrier k /\\        m IN ring_carrier (poly_ring integer_ring (:1)) /\\        monic integer_ring m /\\        poly_extend (integer_ring,k) (ring_of_int k) (\\v. a) m = ring_0 k /\\        prime p /\\        (forall i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\\        ~(&p pow 2 divides coeff 0 m) /\\        ring_sum k {i | i < poly_deg integer_ring m}        (\\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) IN        ideal_generated (ring_of_integers k) {ring_of_num k p}        ==> (forall i. i < poly_deg integer_ring m ==> &p divides c i)"

-- Quadratic
#eval thm' "Quadratic.INT_SQUARE_SUB_MUL_SQUARE_MOD_4" SessionANT.Quadratic.«INT_SQUARE_SUB_MUL_SQUARE_MOD_4»
  "|- forall d A B N.        ~(&4 divides d) /\\ A pow 2 - d * B pow 2 = &4 * N        ==> (if (d == &1) (mod &4)             then &2 divides A - B             else &2 divides A /\\ &2 divides B)"
#eval thm' "Quadratic.QUADRATIC_FIELD_SQRT_UNIQUE" SessionANT.Quadratic.«QUADRATIC_FIELD_SQRT_UNIQUE»
  "|- forall k x y d e.        number_field k /\\        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\\        x IN ring_carrier k /\\        ring_pow k x 2 = ring_of_int k d /\\        squarefree (num_of_int (abs d)) /\\        ~(d = &1) /\\        y IN ring_carrier k /\\        ring_pow k y 2 = ring_of_int k e /\\        squarefree (num_of_int (abs e)) /\\        ~(e = &1)        ==> d = e"

-- QuadraticSplit
#eval thm' "QuadraticSplit.QUADRATIC_POLY_IN_CARRIER" SessionANT.QuadraticSplit.«QUADRATIC_POLY_IN_CARRIER»
  "|- forall r b c.        b IN ring_carrier r /\\ c IN ring_carrier r        ==> ring_sub (poly_ring r (:1))            (ring_pow (poly_ring r (:1)) (poly_var r one) 2)            (ring_add (poly_ring r (:1))             (ring_mul (poly_ring r (:1)) (poly_const r b) (poly_var r one))            (poly_const r c)) IN            ring_carrier (poly_ring r (:1))"
#eval thm' "QuadraticSplit.RING_OF_INTEGERS_SETADD_SUBRING_GENERATED" SessionANT.QuadraticSplit.«RING_OF_INTEGERS_SETADD_SUBRING_GENERATED»
  "|- forall k a j.        a IN ring_carrier (ring_of_integers k) /\\        ring_ideal (ring_of_integers k) j /\\        (forall z.             z IN ring_carrier (ring_of_integers k)             ==> (exists u v.                      u IN ring_carrier (subring_generated k {a}) /\\                      v IN j /\\                      z = ring_add k u v))        ==> ring_setadd (ring_of_integers k)            (ring_carrier (subring_generated k {a}))            j =            ring_carrier (ring_of_integers k)"

-- SplittingTypes
#eval thm' "SplittingTypes.weakly_unramified" SessionANT.SplittingTypes.«weakly_unramified»
  "|- forall p r s h.        weakly_unramified (r,s) h p <=>        (forall P.             prime_ideal s P /\\ IMAGE h p SUBSET P             ==> ramification_index (r,s) h P = 1)"
#eval thm' "SplittingTypes.NUMBER_FIELD_TOTALLY_SPLIT_CARD" SessionANT.SplittingTypes.«NUMBER_FIELD_TOTALLY_SPLIT_CARD»
  "|- forall k p.        number_field k /\\ prime p        ==> (totally_split (integer_ring,ring_of_integers k) (ring_of_int k)             (ideal_generated integer_ring {&p}) <=>             CARD             {P | prime_ideal (ring_of_integers k) P /\\ ring_of_num k p IN P} =             extension_degree (subfield_generated k {ring_0 k},k) I)"

-- Decomposition
#eval thm' "Decomposition.GALOIS_GROUP_SUBRING_IMAGE" SessionANT.Decomposition.«GALOIS_GROUP_SUBRING_IMAGE»
  "|- forall h k l b f.        subring_generated l (ring_carrier b) = b /\\        (forall f.             f IN group_carrier (galois_group (k,l) h)             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\\        f IN group_carrier (galois_group (k,l) h)        ==> IMAGE f (ring_carrier b) = ring_carrier b /\\            ring_isomorphism (b,b) f"
#eval thm' "Decomposition.DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM" SessionANT.Decomposition.«DECOMPOSITION_GROUP_RESIDUE_AUTOMORPHISM»
  "|- forall h k l b Q f.        subring_generated l (ring_carrier b) = b /\\        (forall f.             f IN group_carrier (decomposition_group (k,l) h Q)             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\\        ring_ideal b Q /\\        f IN group_carrier (decomposition_group (k,l) h Q)        ==> (forall x.                 x IN ring_carrier b                 ==> (\\X.                          if X IN ring_carrier (quotient_ring b Q)                          then IMAGE f X                          else X)                     (ring_coset b Q x) =                     ring_coset b Q (f x)) /\\            (\\X.                 if X IN ring_carrier (quotient_ring b Q)                 then IMAGE f X                 else X) permutes            ring_carrier (quotient_ring b Q) /\\            ring_automorphism (quotient_ring b Q)            (\\X.                 if X IN ring_carrier (quotient_ring b Q)                 then IMAGE f X                 else X)"

-- NfDecomposition
#eval thm' "NfDecomposition.GALOIS_GROUP_RING_OF_INTEGERS" SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS»
  "|- forall h k l f.        f IN group_carrier (galois_group (k,l) h)        ==> IMAGE f (ring_carrier (ring_of_integers l)) SUBSET            ring_carrier (ring_of_integers l)"
#eval thm' "NfDecomposition.NUMBER_FIELD_IDEAL_NORM_CONJUGATE" SessionANT.NfDecomposition.«NUMBER_FIELD_IDEAL_NORM_CONJUGATE»
  "|- forall h k l f Q.        number_field l /\\        f IN group_carrier (galois_group (k,l) h) /\\        prime_ideal (ring_of_integers l) Q /\\        ~(Q = {ring_0 l})        ==> ideal_norm (ring_of_integers l) (IMAGE f Q) =            ideal_norm (ring_of_integers l) Q"

-- DecompositionField
#eval thm' "DecompositionField.NUMBER_FIELD_INTERMEDIATE_FIELD" SessionANT.DecompositionField.«NUMBER_FIELD_INTERMEDIATE_FIELD»
  "|- forall h k l s.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        s subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET s        ==> field (subfield_generated l s) /\\            ring_carrier (subfield_generated l s) = s /\\            number_field (subfield_generated l s) /\\            ring_monomorphism (k,subfield_generated l s) h /\\            ring_monomorphism (subfield_generated l s,l) I /\\            ring_homomorphism (k,subfield_generated l s) h /\\            ring_homomorphism (subfield_generated l s,l) I /\\            ring_carrier (ring_of_integers (subfield_generated l s)) =            ring_carrier (ring_of_integers l) INTER s"
#eval thm' "DecompositionField.NUMBER_FIELD_GALOIS_SPLITTING_TYPES" SessionANT.DecompositionField.«NUMBER_FIELD_GALOIS_SPLITTING_TYPES»
  "|- forall h k l p Q.        number_field l /\\        galois_extension (k,l) h /\\        prime_ideal (ring_of_integers k) p /\\        ~(p = {ring_0 k}) /\\        prime_ideal (ring_of_integers l) Q /\\        IMAGE h p SUBSET Q        ==> (unramified (ring_of_integers k,ring_of_integers l) h p <=>             group_carrier (inertia_group (k,l) h (ring_of_integers l) Q) =             {I}) /\\            (totally_split (ring_of_integers k,ring_of_integers l) h p <=>             group_carrier (decomposition_group (k,l) h Q) = {I}) /\\            (inert (ring_of_integers k,ring_of_integers l) h p <=>             group_carrier (decomposition_group (k,l) h Q) =             group_carrier (galois_group (k,l) h) /\\             group_carrier (inertia_group (k,l) h (ring_of_integers l) Q) =             {I}) /\\            (totally_ramified (ring_of_integers k,ring_of_integers l) h p <=>             group_carrier (inertia_group (k,l) h (ring_of_integers l) Q) =             group_carrier (galois_group (k,l) h))"

-- ConjugateIdeals
#eval thm' "ConjugateIdeals.NUMBER_FIELD_GALOIS_PRODUCT_PRIME" SessionANT.ConjugateIdeals.«NUMBER_FIELD_GALOIS_PRODUCT_PRIME»
  "|- forall h k l p P.        number_field l /\\        galois_extension (k,l) h /\\        prime_ideal (ring_of_integers k) p /\\        ~(p = {ring_0 k}) /\\        prime_ideal (ring_of_integers l) P /\\        IMAGE h p SUBSET P        ==> ideal_product (ring_of_integers l)            (group_carrier (galois_group (k,l) h))            (\\f. IMAGE f P) =            ideal_pow (ring_of_integers l)            (ideal_generated (ring_of_integers l) (IMAGE h p))            (residue_degree (ring_of_integers k,ring_of_integers l) h P)"
#eval thm' "ConjugateIdeals.NUMBER_FIELD_GALOIS_PRODUCT_IDEAL" SessionANT.ConjugateIdeals.«NUMBER_FIELD_GALOIS_PRODUCT_IDEAL»
  "|- forall k j.        number_field k /\\        galois_extension (subfield_generated k {ring_0 k},k) I /\\        ring_ideal (ring_of_integers k) j /\\        ~(j = {ring_0 k})        ==> ideal_product (ring_of_integers k)            (group_carrier            (galois_group (subfield_generated k {ring_0 k},k) I))            (\\f. IMAGE f j) =            ideal_generated (ring_of_integers k)            {ring_of_num k (ideal_norm (ring_of_integers k) j)}"

-- QuadraticIdeals
#eval thm' "QuadraticIdeals.QUADRATIC_FIELD_SUBFIELD_GENERATED" SessionANT.QuadraticIdeals.«QUADRATIC_FIELD_SUBFIELD_GENERATED»
  "|- forall k x.        number_field k /\\        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\\        x IN ring_carrier k /\\        ~(x IN ring_carrier (subfield_generated k {ring_0 k}))        ==> subfield_generated k {x} = k"
#eval thm' "QuadraticIdeals.QUADRATIC_FIELD_NORM" SessionANT.QuadraticIdeals.«QUADRATIC_FIELD_NORM»
  "|- forall k x a b.        number_field k /\\        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\\        x IN ring_carrier k /\\        ~(x IN ring_carrier (subfield_generated k {ring_0 k})) /\\        ring_pow k x 2 IN ring_carrier (subfield_generated k {ring_0 k}) /\\        a IN ring_carrier (subfield_generated k {ring_0 k}) /\\        b IN ring_carrier (subfield_generated k {ring_0 k})        ==> algebra_norm (subfield_generated k {ring_0 k},k) I            (ring_add k a (ring_mul k b x)) =            ring_sub k (ring_pow k a 2)            (ring_mul k (ring_pow k b 2) (ring_pow k x 2))"

-- SplitPrimes
#eval thm' "SplitPrimes.INTEGER_POLY_CONGRUENCE" SessionANT.SplitPrimes.«INTEGER_POLY_CONGRUENCE»
  "|- forall q m x y.        q IN ring_carrier (poly_ring integer_ring (:1)) /\\ m divides x - y        ==> m divides poly_eval integer_ring q x - poly_eval integer_ring q y"
#eval thm' "SplitPrimes.NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE" SessionANT.SplitPrimes.«NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE»
  "|- forall l.        number_field l /\\        galois_extension (subfield_generated l {ring_0 l},l) I        ==> INFINITE            {p | prime p /\\                 totally_split (integer_ring,ring_of_integers l)                 (ring_of_int l)                 (ideal_generated integer_ring {&p})}"

-- IdealNormExtension
#eval thm' "IdealNormExtension.RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION" SessionANT.IdealNormExtension.«RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION»
  "|- forall k l h j.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        ring_ideal (ring_of_integers k) j        ==> {x | x IN ring_carrier (ring_of_integers k) /\\                 h x IN ideal_generated (ring_of_integers l) (IMAGE h j)} =            j"
#eval thm' "IdealNormExtension.NUMBER_FIELD_IDEAL_NORM_EXTENSION_SUBSET" SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_EXTENSION_SUBSET»
  "|- forall k l h J.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        ring_ideal (ring_of_integers l) J        ==> ideal_generated (ring_of_integers l)            (IMAGE h (number_field_ideal_norm (k,l) h J)) SUBSET            J"

-- DiscriminantExtension
#eval thm' "DiscriminantExtension.NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST" SessionANT.DiscriminantExtension.«NUMBER_FIELD_BASIS_DISCRIMINANT_TWIST»
  "|- forall k l h n w t d.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        free_basis (k,l) h n w /\\        t IN ring_carrier k /\\        d IN ring_carrier l /\\        ~(d = ring_0 l)        ==> ring_mul k (algebra_norm (k,l) h d)            (ring_det k {i | i < n}            (\\i j.                 algebra_trace (k,l) h                 (ring_mul l (ring_mul l (h t) (ring_inv l d))                 (ring_mul l (w i) (w j))))) =            ring_mul k (ring_pow k t n) (basis_discriminant (k,l) h n w)"
#eval thm' "DiscriminantExtension.NUMBER_FIELD_NORM_DIFFERENT_LOCAL_BASIS" SessionANT.DiscriminantExtension.«NUMBER_FIELD_NORM_DIFFERENT_LOCAL_BASIS»
  "|- forall k l h p.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        prime_ideal (ring_of_integers k) p /\\        ~(p = {ring_0 k})        ==> (exists w.                 free_basis (k,l) h (extension_degree (k,l) h) w /\\                 (forall i.                      i < extension_degree (k,l) h                      ==> w i IN ring_carrier (ring_of_integers l)) /\\                 ideal_valuation (ring_of_integers k) p                 (ideal_generated (ring_of_integers k)                 {basis_discriminant (k,l) h (extension_degree (k,l) h) w}) =                 ideal_valuation (ring_of_integers k) p                 (number_field_ideal_norm (k,l) h                 (number_field_different (k,l) h)))"

-- ClassGroupMaps
#eval thm' "ClassGroupMaps.NUMBER_FIELD_CLASS_GROUP_EXTENSION" SessionANT.ClassGroupMaps.«NUMBER_FIELD_CLASS_GROUP_EXTENSION»
  "|- forall k l h.        field k /\\ number_field l /\\ ring_homomorphism (k,l) h        ==> (exists f.                 group_homomorphism                 (class_group (ring_of_integers k),                  class_group (ring_of_integers l))                 f /\\                 (forall j.                      ring_ideal (ring_of_integers k) j /\\ ~(j = {ring_0 k})                      ==> f (ideal_class (ring_of_integers k) j) =                          ideal_class (ring_of_integers l)                          (ideal_generated (ring_of_integers l) (IMAGE h j))))"
#eval thm' "ClassGroupMaps.NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW" SessionANT.ClassGroupMaps.«NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW»
  "|- forall k l h j.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        ring_ideal (ring_of_integers k) j /\\        principal_ideal (ring_of_integers l)        (ideal_generated (ring_of_integers l) (IMAGE h j))        ==> principal_ideal (ring_of_integers k)            (ideal_pow (ring_of_integers k) j (extension_degree (k,l) h))"

-- SIntegers
#eval thm' "SIntegers.ring_of_s_integers" SessionANT.SIntegers.«ring_of_s_integers»
  "|- forall S r k h.        ring_of_s_integers (r,k) h S =        subring_generated k        {x | x IN ring_carrier k /\\             (forall P.                  prime_ideal r P /\\ ~(P = {ring_0 r}) /\\ ~(P IN S)                  ==> x = ring_0 k \\/ &0 <= dedekind_valuation (r,k) h P x)}"
#eval thm' "SIntegers.RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME" SessionANT.SIntegers.«RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME»
  "|- forall r k h S P.        dedekind_domain r /\\        field_of_fractions (r,k) h /\\        prime_ideal r P /\\        ~(P = {ring_0 r})        ==> ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h P) =            (if P IN S             then ring_carrier (ring_of_s_integers (r,k) h S)             else {x | x IN ring_carrier (ring_of_s_integers (r,k) h S) /\\                       (x = ring_0 k \\/ &1 <= dedekind_valuation (r,k) h P x)})"

-- UnramifiedOutside
#eval thm' "UnramifiedOutside.FINITE_SUBEXTENSION_NUMBER_FIELD" SessionANT.UnramifiedOutside.«FINITE_SUBEXTENSION_NUMBER_FIELD»
  "|- forall h k l e.        number_field k /\\        field l /\\        e subfield_of l /\\        finite_extension (k,subfield_generated l e) h        ==> ring_carrier (subfield_generated l e) = e /\\            field (subfield_generated l e) /\\            number_field (subfield_generated l e) /\\            ring_homomorphism (k,subfield_generated l e) h"
#eval thm' "UnramifiedOutside.maximal_unramified_outside" SessionANT.UnramifiedOutside.«maximal_unramified_outside»
  "|- forall k l h S.        maximal_unramified_outside (k,l) h S =        UNIONS        {e | e IN finite_galois_subfields (k,l) h /\\             unramified_outside (k,l) h S e}"

-- ValuationResidue
#eval thm' "ValuationResidue.VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED" SessionANT.ValuationResidue.«VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED»
  "|- forall k v m.        algebraically_closed_field k /\\        valuation_subring k v /\\        maximal_ideal (subring_generated k v) m        ==> algebraically_closed_field            (quotient_ring (subring_generated k v) m)"
#eval thm' "ValuationResidue.VALUATION_SUBRING_DECOMPOSITION_RESIDUE" SessionANT.ValuationResidue.«VALUATION_SUBRING_DECOMPOSITION_RESIDUE»
  "|- forall k v m Q.        valuation_subring k v /\\        maximal_ideal (subring_generated k v) m /\\        Q = m INTER ring_carrier (ring_of_integers k)        ==> group_homomorphism            (decomposition_group (subfield_generated k {ring_0 k},k) I Q,             galois_group             (subring_generated (quotient_ring (ring_of_integers k) Q)              (IMAGE (ring_coset (ring_of_integers k) Q)              {a | a IN ring_carrier (subfield_generated k {ring_0 k}) /\\                   a IN ring_carrier (ring_of_integers k)}),              quotient_ring (ring_of_integers k) Q)             I)            (\\f X.                 if X IN ring_carrier (quotient_ring (ring_of_integers k) Q)                 then IMAGE f X                 else X) /\\            group_kernel            (decomposition_group (subfield_generated k {ring_0 k},k) I Q,             galois_group             (subring_generated (quotient_ring (ring_of_integers k) Q)              (IMAGE (ring_coset (ring_of_integers k) Q)              {a | a IN ring_carrier (subfield_generated k {ring_0 k}) /\\                   a IN ring_carrier (ring_of_integers k)}),              quotient_ring (ring_of_integers k) Q)             I)            (\\f X.                 if X IN ring_carrier (quotient_ring (ring_of_integers k) Q)                 then IMAGE f X                 else X) =            group_carrier            (inertia_group (subfield_generated k {ring_0 k},k) I             (ring_of_integers k)            Q)"

-- FingenGroup
#eval thm' "FingenGroup.FINITELY_GENERATED_GROUP_EXTENSION" SessionANT.FingenGroup.«FINITELY_GENERATED_GROUP_EXTENSION»
  "|- forall G H f.        group_homomorphism (G,H) f /\\        finitely_generated_group (subgroup_generated G (group_kernel (G,H) f)) /\\        finitely_generated_group (subgroup_generated H (group_image (G,H) f))        ==> finitely_generated_group G"
#eval thm' "FingenGroup.GROUP_REAL_MULTIPLICATIVE_BOX_COUNT" SessionANT.FingenGroup.«GROUP_REAL_MULTIPLICATIVE_BOX_COUNT»
  "|- forall G s f k.        FINITE s /\\        (forall i x. i IN s /\\ x IN group_carrier G ==> &0 < f i x) /\\        (forall i x y.             i IN s /\\ x IN group_carrier G /\\ y IN group_carrier G             ==> f i (group_mul G x y) = f i x * f i y) /\\        FINITE        {x | x IN group_carrier G /\\             (forall i. i IN s ==> inv (&2) <= f i x /\\ f i x <= &2)}        ==> FINITE            {x | x IN group_carrier G /\\                 (forall i.                      i IN s ==> inv (&2 pow k) <= f i x /\\ f i x <= &2 pow k)} /\\            CARD            {x | x IN group_carrier G /\\                 (forall i.                      i IN s ==> inv (&2 pow k) <= f i x /\\ f i x <= &2 pow k)} <=            (2 * k + 1) EXP CARD s *            CARD            {x | x IN group_carrier G /\\                 (forall i. i IN s ==> inv (&2) <= f i x /\\ f i x <= &2)}"

-- CyclotomicPoly
#eval thm' "CyclotomicPoly.cyclotomic_poly" SessionANT.CyclotomicPoly.«cyclotomic_poly»
  "|- forall r n.        cyclotomic_poly r n =        (if n = 0         then poly_1 r         else poly_div r              (poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r))              (ring_product (poly_ring r (:1)) {d | d divides n /\\ d < n}              (cyclotomic_poly r)))"
#eval thm' "CyclotomicPoly.CYCLOTOMIC_POLY_RING_OF_INT" SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_RING_OF_INT»
  "|- forall r n.        cyclotomic_poly r n = ring_of_int r o cyclotomic_poly integer_ring n /\\        monic r (cyclotomic_poly r n) /\\        (~(n = 0)         ==> ring_product (poly_ring r (:1)) {d | d divides n}             (cyclotomic_poly r) =             poly_sub r (poly_pow r (poly_var r one) n) (poly_1 r))"

-- CyclotomicField
#eval thm' "CyclotomicField.NUMBER_FIELD_FINITE_EXTENSION" SessionANT.CyclotomicField.«NUMBER_FIELD_FINITE_EXTENSION»
  "|- forall k l h.        number_field k /\\ finite_extension (k,l) h ==> number_field l"
#eval thm' "CyclotomicField.NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES" SessionANT.CyclotomicField.«NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES»
  "|- forall k z q p.        number_field k /\\        z IN ring_carrier k /\\        q IN ring_carrier (poly_ring integer_ring (:1)) /\\        monic integer_ring q /\\        poly_deg integer_ring q =        poly_deg (subfield_generated k {ring_0 k})        (minimal_polynomial (subfield_generated k {ring_0 k},k) I z) /\\        poly_extend (integer_ring,k) (ring_of_int k) (\\v. z) q = ring_0 k /\\        p IN ring_carrier (poly_ring integer_ring (:1)) /\\        poly_extend (integer_ring,k) (ring_of_int k) (\\v. z) p = ring_0 k        ==> ring_divides (poly_ring integer_ring (:1)) q p"

-- CyclotomicIntegers
#eval thm' "CyclotomicIntegers.CYCLOTOMIC_POLY_INTEGER_ROOT" SessionANT.CyclotomicIntegers.«CYCLOTOMIC_POLY_INTEGER_ROOT»
  "|- forall k w n.        integral_domain k /\\        w IN ring_carrier k /\\        ring_order k w = n /\\        ~(n = 0)        ==> poly_extend (integer_ring,k) (ring_of_int k) (\\v. w)            (cyclotomic_poly integer_ring n) =            ring_0 k"
#eval thm' "CyclotomicIntegers.SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL" SessionANT.CyclotomicIntegers.«SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL»
  "|- forall k z n p x.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = n /\\        ~(n = 0) /\\        prime p /\\        x IN ring_carrier (ring_of_integers k) /\\        ring_mul k (ring_of_num k p) x IN        ring_carrier (subring_generated k {z})        ==> x IN ring_carrier (subring_generated k {z})"

-- CyclotomicSplit
#eval thm' "CyclotomicSplit.CYCLOTOMIC_FIELD_DEDEKIND_KUMMER" SessionANT.CyclotomicSplit.«CYCLOTOMIC_FIELD_DEDEKIND_KUMMER»
  "|- forall k z p a m s P.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = p EXP a * m /\\        subfield_generated k {z} = k /\\        prime p /\\        ~(p divides m) /\\        FINITE s /\\        (forall g.             g IN s             ==> g IN ring_carrier (poly_ring (integer_mod_ring p) (:1)) /\\                 monic (integer_mod_ring p) g /\\                 ring_irreducible (poly_ring (integer_mod_ring p) (:1)) g) /\\        cyclotomic_poly (integer_mod_ring p) m =        ring_product (poly_ring (integer_mod_ring p) (:1)) s (\\g. g) /\\        (forall g.             P g =             ideal_generated (ring_of_integers k)             {ring_of_num k p,              poly_extend (integer_ring,k) (ring_of_int k) (\\v. z) g})        ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =            ideal_product (ring_of_integers k) s            (\\g. ideal_pow (ring_of_integers k) (P g) (phi (p EXP a))) /\\            {Q | prime_ideal (ring_of_integers k) Q /\\ ring_of_num k p IN Q} =            IMAGE P s /\\            (forall g h. g IN s /\\ h IN s /\\ P g = P h ==> g = h) /\\            (forall g.                 g IN s                 ==> prime_ideal (ring_of_integers k) (P g) /\\                     residue_degree (integer_ring,ring_of_integers k)                     (ring_of_int k)                     (P g) =                     poly_deg (integer_mod_ring p) g /\\                     ramification_index (integer_ring,ring_of_integers k)                     (ring_of_int k)                     (P g) =                     phi (p EXP a))"
#eval thm' "CyclotomicSplit.CYCLOTOMIC_FIELD_RAMIFIED" SessionANT.CyclotomicSplit.«CYCLOTOMIC_FIELD_RAMIFIED»
  "|- forall k z n p.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = n /\\        ~(n = 0) /\\        subfield_generated k {z} = k /\\        prime p        ==> (&p divides number_field_discriminant k <=>             p divides n /\\ ~(p = 2 /\\ ~(4 divides n)))"

-- CyclotomicGalois
#eval thm' "CyclotomicGalois.UNIT_GROUP_INTEGER_MOD_RING" SessionANT.CyclotomicGalois.«UNIT_GROUP_INTEGER_MOD_RING»
  "|- forall n.        ~(n = 0)        ==> group_carrier (unit_group (integer_mod_ring n)) =            IMAGE & {a | a < n /\\ coprime (a,n)}"
#eval thm' "CyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP" SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP»
  "|- forall k z n.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = n /\\        ~(n = 0) /\\        subfield_generated k {z} = k        ==> (exists f.                 group_isomorphism                 (unit_group (integer_mod_ring n),                  galois_group (subfield_generated k {ring_0 k},k) I)                 f /\\                 (forall c.                      c IN group_carrier (unit_group (integer_mod_ring n))                      ==> f c z = ring_pow k z (num_of_int c)))"

-- CyclotomicFrobenius
#eval thm' "CyclotomicFrobenius.NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD" SessionANT.CyclotomicFrobenius.«NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD»
  "|- forall k P p.        field k /\\        ring_char k = 0 /\\        prime p /\\        ring_ideal (ring_of_integers k) P /\\        (forall m. ring_of_int k m IN P <=> &p divides m)        ==> CARD            {ring_coset (ring_of_integers k) P (I a) | a | a IN                                                           ring_carrier                                                           (subfield_generated                                                            k                                                           {ring_0 k}) /\\                                                           I a IN                                                           ring_carrier                                                           (ring_of_integers                                                           k)} =            p"
#eval thm' "CyclotomicFrobenius.CYCLOTOMIC_FIELD_INERTIA_GROUP" SessionANT.CyclotomicFrobenius.«CYCLOTOMIC_FIELD_INERTIA_GROUP»
  "|- forall k z n p P.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = n /\\        subfield_generated k {z} = k /\\        prime p /\\        ~(p divides n) /\\        maximal_ideal (ring_of_integers k) P /\\        ring_of_num k p IN P        ==> group_carrier            (inertia_group (subfield_generated k {ring_0 k},k) I             (ring_of_integers k)            P) =            {I}"

-- CyclotomicSubfields
#eval thm' "CyclotomicSubfields.CYCLOTOMIC_SUBFIELD_COMPOSITUM" SessionANT.CyclotomicSubfields.«CYCLOTOMIC_SUBFIELD_COMPOSITUM»
  "|- forall l z w.        field l /\\        z IN ring_carrier l /\\        w IN ring_carrier l /\\        ~(ring_order l z = 0) /\\        ~(ring_order l w = 0)        ==> (exists v.                 v IN ring_carrier (subfield_generated l {z, w}) /\\                 ring_order l v = lcm (ring_order l z,ring_order l w)) /\\            (forall v.                 v IN ring_carrier l /\\                 ring_order l v = lcm (ring_order l z,ring_order l w)                 ==> subfield_generated l {z, w} = subfield_generated l {v})"
#eval thm' "CyclotomicSubfields.CYCLOTOMIC_FIELD_INVERSION_EXISTS" SessionANT.CyclotomicSubfields.«CYCLOTOMIC_FIELD_INVERSION_EXISTS»
  "|- forall k z n.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = n /\\        ~(n = 0) /\\        subfield_generated k {z} = k        ==> (exists c.                 c IN                 group_carrier                 (galois_group (subfield_generated k {ring_0 k},k) I) /\\                 c z = ring_inv k z)"

-- CyclotomicSubfieldSplit
#eval thm' "CyclotomicSubfieldSplit.CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE" SessionANT.CyclotomicSubfieldSplit.«CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE»
  "|- forall k z n s p Q.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = n /\\        subfield_generated k {z} = k /\\        prime p /\\        ~(p divides n) /\\        prime_ideal (ring_of_integers k) Q /\\        ring_of_num k p IN Q        ==> prime_ideal (ring_of_integers (subfield_generated k s))            (Q INTER ring_carrier (subfield_generated k s)) /\\            ring_of_num (subfield_generated k s) p IN            Q INTER ring_carrier (subfield_generated k s) /\\            ramification_index            (integer_ring,ring_of_integers (subfield_generated k s))            (ring_of_int (subfield_generated k s))            (Q INTER ring_carrier (subfield_generated k s)) =            1 /\\            (forall d.                 residue_degree                 (integer_ring,ring_of_integers (subfield_generated k s))                 (ring_of_int (subfield_generated k s))                 (Q INTER ring_carrier (subfield_generated k s)) divides                 d <=>                 (forall g x.                      g IN                      group_carrier                      (galois_group (subfield_generated k {ring_0 k},k) I) /\\                      g z = ring_pow k z (p EXP d) /\\                      x IN s                      ==> g x = x))"
#eval thm' "CyclotomicSubfieldSplit.CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES" SessionANT.CyclotomicSubfieldSplit.«CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES»
  "|- forall k z n s p.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = n /\\        subfield_generated k {z} = k /\\        prime p /\\        ~(p divides n)        ==> unramified            (integer_ring,ring_of_integers (subfield_generated k s))            (ring_of_int (subfield_generated k s))            (ideal_generated integer_ring {&p}) /\\            (totally_split             (integer_ring,ring_of_integers (subfield_generated k s))             (ring_of_int (subfield_generated k s))             (ideal_generated integer_ring {&p}) <=>             (forall g x.                  g IN                  group_carrier                  (galois_group (subfield_generated k {ring_0 k},k) I) /\\                  g z = ring_pow k z p /\\                  x IN s                  ==> g x = x))"

-- GaussSum
#eval thm' "GaussSum.QUADRATIC_GAUSS_SUM" SessionANT.GaussSum.«QUADRATIC_GAUSS_SUM»
  "|- forall r z p.        integral_domain r /\\        prime p /\\        ~(p = 2) /\\        z IN ring_carrier r /\\        ring_order r z = p        ==> ring_pow r            (ring_sum r {a | a < p}            (\\a. ring_mul r (ring_of_int r (jacobi (a,p))) (ring_pow r z a)))            2 =            ring_of_int r (-- &1 pow ((p - 1) DIV 2) * &p)"
#eval thm' "GaussSum.NUMBER_FIELD_SQRT_DEGREE" SessionANT.GaussSum.«NUMBER_FIELD_SQRT_DEGREE»
  "|- forall k x.        number_field k /\\        x IN ring_carrier k /\\        ~(x IN ring_carrier (subfield_generated k {ring_0 k})) /\\        ring_pow k x 2 IN ring_carrier (subfield_generated k {ring_0 k})        ==> extension_degree            (subfield_generated k {ring_0 k},subfield_generated k {x})            I =            2"

-- CyclotomicQuadraticSplit
#eval thm' "CyclotomicQuadraticSplit.QUADRATIC_FIELD_TOTALLY_SPLIT_ODD_PRIME" SessionANT.CyclotomicQuadraticSplit.«QUADRATIC_FIELD_TOTALLY_SPLIT_ODD_PRIME»
  "|- forall k x d p.        number_field k /\\        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\\        x IN ring_carrier k /\\        ring_pow k x 2 = ring_of_int k d /\\        squarefree (num_of_int (abs d)) /\\        ~(d = &1) /\\        prime p /\\        ~(p = 2) /\\        ~(&p divides d)        ==> (totally_split (integer_ring,ring_of_integers k) (ring_of_int k)             (ideal_generated integer_ring {&p}) <=>             (exists y. (y pow 2 == d) (mod &p)))"
#eval thm' "CyclotomicQuadraticSplit.CYCLOTOMIC_QUADRATIC_SUBFIELD_TOTALLY_SPLIT" SessionANT.CyclotomicQuadraticSplit.«CYCLOTOMIC_QUADRATIC_SUBFIELD_TOTALLY_SPLIT»
  "|- forall k z p y q.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = p /\\        prime p /\\        ~(p = 2) /\\        subfield_generated k {z} = k /\\        y IN ring_carrier k /\\        ring_pow k y 2 = ring_of_int k (-- &1 pow ((p - 1) DIV 2) * &p) /\\        prime q /\\        ~(q = p)        ==> (totally_split             (integer_ring,ring_of_integers (subfield_generated k {y}))             (ring_of_int (subfield_generated k {y}))             (ideal_generated integer_ring {&q}) <=>             (exists x. (x EXP 2 == q) (mod p)))"

-- ComplexEmbeddings
#eval thm' "ComplexEmbeddings.complex_embeddings" SessionANT.ComplexEmbeddings.«complex_embeddings»
  "|- forall k.        complex_embeddings k =        {f | ring_homomorphism (k,complex_ring) f /\\             f IN EXTENSIONAL (ring_carrier k)}"
#eval thm' "ComplexEmbeddings.COMPLEX_EMBEDDINGS_HAS_SIZE" SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_HAS_SIZE»
  "|- forall k.        number_field k        ==> complex_embeddings k HAS_SIZE            extension_degree (subfield_generated k {ring_0 k},k) I"

-- ComplexConjugation
#eval thm' "ComplexConjugation.GALOIS_GROUP_COMPLEX_CONJUGATION" SessionANT.ComplexConjugation.«GALOIS_GROUP_COMPLEX_CONJUGATION»
  "|- forall k e.        normal_extension (subfield_generated k {ring_0 k},k) I /\\        ring_homomorphism (k,complex_ring) e        ==> (exists c.                 c IN                 group_carrier                 (galois_group (subfield_generated k {ring_0 k},k) I) /\\                 (forall x. x IN ring_carrier k ==> e (c x) = cnj (e x)) /\\                 group_mul                 (galois_group (subfield_generated k {ring_0 k},k) I)                 c                 c =                 group_id (galois_group (subfield_generated k {ring_0 k},k) I) /\\                 (c =                  group_id                  (galois_group (subfield_generated k {ring_0 k},k) I) <=>                  (forall x. x IN ring_carrier k ==> real (e x))))"
#eval thm' "ComplexConjugation.COMPLEX_CONJUGATION_REAL_SUBFIELD" SessionANT.ComplexConjugation.«COMPLEX_CONJUGATION_REAL_SUBFIELD»
  "|- forall k e c.        field k /\\        ring_homomorphism (k,complex_ring) e /\\        c IN        group_carrier (galois_group (subfield_generated k {ring_0 k},k) I) /\\        (forall x. x IN ring_carrier k ==> e (c x) = cnj (e x)) /\\        ~(c = I)        ==> {x | x IN ring_carrier k /\\ real (e x)} subfield_of k /\\            finite_extension            (subfield_generated k {x | x IN ring_carrier k /\\ real (e x)},k)            I /\\            galois_extension            (subfield_generated k {x | x IN ring_carrier k /\\ real (e x)},k)            I /\\            extension_degree            (subfield_generated k {x | x IN ring_carrier k /\\ real (e x)},k)            I =            2"

-- CyclotomicCharacter
#eval thm' "CyclotomicCharacter.cyclotomic_character" SessionANT.CyclotomicCharacter.«cyclotomic_character»
  "|- forall n f k.        cyclotomic_character k n f =        (@c.             c IN group_carrier (unit_group (integer_mod_ring n)) /\\             (forall x.                  x IN ring_carrier k /\\ ring_pow k x n = ring_1 k                  ==> f x = ring_pow k x (num_of_int c)))"
#eval thm' "CyclotomicCharacter.CYCLOTOMIC_CHARACTER_KERNEL" SessionANT.CyclotomicCharacter.«CYCLOTOMIC_CHARACTER_KERNEL»
  "|- forall h k l n z.        field l /\\ z IN ring_carrier l /\\ ring_order l z = n /\\ ~(n = 0)        ==> group_kernel            (galois_group (k,l) h,unit_group (integer_mod_ring n))            (cyclotomic_character l n) =            group_carrier            (galois_group             (subfield_generated l (z INSERT IMAGE h (ring_carrier k)),l)            I)"

-- Sunits
#eval thm' "Sunits.s_unit_group" SessionANT.Sunits.«s_unit_group»
  "|- forall S k.        s_unit_group k S =        subgroup_generated (unit_group k)        {x | x IN ring_carrier k /\\             ~(x = ring_0 k) /\\             (forall P.                  prime_ideal (ring_of_integers k) P /\\                  ~(P = {ring_0 k}) /\\                  ~(P IN S)                  ==> dedekind_valuation (ring_of_integers k,k) I P x = &0)}"
#eval thm' "Sunits.FINITELY_GENERATED_S_UNIT_GROUP" SessionANT.Sunits.«FINITELY_GENERATED_S_UNIT_GROUP»
  "|- forall k S.        number_field k /\\ FINITE S        ==> finitely_generated_group (s_unit_group k S)"

-- InfinitePlaces
#eval thm' "InfinitePlaces.real_embeddings" SessionANT.InfinitePlaces.«real_embeddings»
  "|- forall k.        real_embeddings k =        {g | g IN complex_embeddings k /\\             (forall x. x IN ring_carrier k ==> real (g x))}"
#eval thm' "InfinitePlaces.CARD_INFINITE_PLACE_EMBEDDINGS" SessionANT.InfinitePlaces.«CARD_INFINITE_PLACE_EMBEDDINGS»
  "|- forall k g.        g IN complex_embeddings k        ==> CARD            {h | h IN complex_embeddings k /\\                 (\\x. norm (h x)) = (\\x. norm (g x))} =            (if g IN real_embeddings k then 1 else 2)"

-- MinkowskiTheory
#eval thm' "MinkowskiTheory.NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS" SessionANT.MinkowskiTheory.«NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS»
  "|- forall k j c.        number_field k /\\        ring_ideal (ring_of_integers k) j /\\        ~(j = {ring_0 k}) /\\        (forall g. g IN complex_embeddings k ==> &0 < c g) /\\        sqrt (abs (real_of_int (number_field_discriminant k))) *        &(ideal_norm (ring_of_integers k) j) <=        product (complex_embeddings k) c        ==> (exists x.                 x IN j /\\                 ~(x = ring_0 k) /\\                 (forall g.                      g IN complex_embeddings k                      ==> abs (Re (g x) + Im (g x)) <= c g))"
#eval thm' "MinkowskiTheory.NUMBER_FIELD_PID_MINKOWSKI" SessionANT.MinkowskiTheory.«NUMBER_FIELD_PID_MINKOWSKI»
  "|- forall k.        number_field k /\\        (forall P.             prime_ideal (ring_of_integers k) P /\\             ~(P = {ring_0 k}) /\\             &(ideal_norm (ring_of_integers k) P) <=             sqrt (abs (real_of_int (number_field_discriminant k)))             ==> (exists a.                      a IN ring_carrier (ring_of_integers k) /\\                      P = ideal_generated (ring_of_integers k) {a}))        ==> PID (ring_of_integers k)"

-- InertiaGenerators
#eval thm' "InertiaGenerators.NUMBER_FIELD_RATIONAL_RAMIFICATION_INDEX" SessionANT.InertiaGenerators.«NUMBER_FIELD_RATIONAL_RAMIFICATION_INDEX»
  "|- forall k p.        number_field k /\\        extension_degree (subfield_generated k {ring_0 k},k) I = 1 /\\        prime_ideal (ring_of_integers k) p /\\        ~(p = {ring_0 k})        ==> ramification_index (integer_ring,ring_of_integers k)            (ring_of_int k)            p =            1"
#eval thm' "InertiaGenerators.NUMBER_FIELD_UNRAMIFIED_RATIONAL" SessionANT.InertiaGenerators.«NUMBER_FIELD_UNRAMIFIED_RATIONAL»
  "|- forall h k l.        field k /\\        number_field l /\\        ring_homomorphism (k,l) h /\\        extension_degree (subfield_generated k {ring_0 k},k) I = 1 /\\        (forall p.             prime_ideal (ring_of_integers k) p /\\ ~(p = {ring_0 k})             ==> unramified (ring_of_integers k,ring_of_integers l) h p)        ==> extension_degree (k,l) h = 1"

-- DiscriminantCompositum
#eval thm' "DiscriminantCompositum.NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS" SessionANT.DiscriminantCompositum.«NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS»
  "|- forall k s n e.        number_field k /\\        free_basis (integer_ring,ring_of_integers (subfield_generated k s))        (ring_of_int (subfield_generated k s))        n        e        ==> number_field (subfield_generated k s) /\\            extension_degree            (subfield_generated k {ring_0 k},subfield_generated k s)            I =            n /\\            free_basis            (subfield_generated k {ring_0 k},subfield_generated k s)            I            n            e /\\            (forall i. i < n ==> e i IN ring_carrier (subfield_generated k s)) /\\            (forall i. i < n ==> e i IN ring_carrier (ring_of_integers k)) /\\            ring_of_int k (number_field_discriminant (subfield_generated k s)) =            basis_discriminant            (subfield_generated k {ring_0 k},subfield_generated k s)            I            n            e"
#eval thm' "DiscriminantCompositum.NUMBER_FIELD_COMPOSITUM_COORDINATES" SessionANT.DiscriminantCompositum.«NUMBER_FIELD_COMPOSITUM_COORDINATES»
  "|- forall k s t n m e f alpha c.        number_field k /\\        subfield_generated k (s UNION t) = k /\\        extension_degree (subfield_generated k {ring_0 k},k) I = n * m /\\        free_basis (integer_ring,ring_of_integers (subfield_generated k s))        (ring_of_int (subfield_generated k s))        n        e /\\        free_basis (integer_ring,ring_of_integers (subfield_generated k t))        (ring_of_int (subfield_generated k t))        m        f /\\        alpha IN ring_carrier (ring_of_integers k) /\\        (forall i j.             i < n /\\ j < m             ==> c i j IN ring_carrier (subfield_generated k {ring_0 k})) /\\        alpha =        ring_sum k {i | i < n}        (\\i.             ring_sum k {j | j < m}             (\\j. ring_mul k (c i j) (ring_mul k (e i) (f j))))        ==> (forall i j.                 i < n /\\ j < m                 ==> (exists z.                          ring_mul k                          (ring_of_int k                          (number_field_discriminant (subfield_generated k s)))                          (c i j) =                          ring_of_int k z))"

-- Hermite
#eval thm' "Hermite.RING_OF_INTEGERS_NORM_PRODUCT_GE_1" SessionANT.Hermite.«RING_OF_INTEGERS_NORM_PRODUCT_GE_1»
  "|- forall k x.        number_field k /\\        x IN ring_carrier (ring_of_integers k) /\\        ~(x = ring_0 k)        ==> &1 <= product (complex_embeddings k) (\\g. norm (g x))"
#eval thm' "Hermite.NUMBER_FIELD_HERMITE_GENERATOR" SessionANT.Hermite.«NUMBER_FIELD_HERMITE_GENERATOR»
  "|- forall k.        number_field k        ==> (exists x.                 x IN ring_carrier (ring_of_integers k) /\\                 subfield_generated k {x} = k /\\                 (forall g.                      g IN complex_embeddings k                      ==> norm (g x) <=                          &2 pow                          (extension_degree                           (subfield_generated k {ring_0 k},k)                           I -                           1) *                          sqrt                          (abs (real_of_int (number_field_discriminant k)))))"

-- UnitTheorem
#eval thm' "UnitTheorem.NUMBER_FIELD_UNIT_DOMINANT_PLACE" SessionANT.UnitTheorem.«NUMBER_FIELD_UNIT_DOMINANT_PLACE»
  "|- forall k g.        number_field k /\\ g IN complex_embeddings k        ==> (exists u.                 ring_unit (ring_of_integers k) u /\\                 (forall h.                      h IN complex_embeddings k /\\                      ~(forall x.                            x IN ring_carrier k ==> norm (h x) = norm (g x))                      ==> norm (h u) < &1))"
#eval thm' "UnitTheorem.NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC" SessionANT.UnitTheorem.«NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC»
  "|- forall k.        number_field k        ==> (exists z.                 z IN ring_carrier k /\\                 (exists m. 1 <= m /\\ ring_pow k z m = ring_1 k) /\\                 (forall x.                      x IN ring_carrier k /\\                      (exists m. 1 <= m /\\ ring_pow k x m = ring_1 k)                      ==> (exists j. x = ring_pow k z j)))"

-- Regulator
#eval thm' "Regulator.REAL_MATRIX_SOLVE" SessionANT.Regulator.«REAL_MATRIX_SOLVE»
  "|- forall s m v.        FINITE s /\\ ~(ring_det real_ring s m = &0)        ==> (exists t. forall i. i IN s ==> sum s (\\j. m i j * t j) = v i)"
#eval thm' "Regulator.NUMBER_FIELD_LOG_MATRIX_CHANGE" SessionANT.Regulator.«NUMBER_FIELD_LOG_MATRIX_CHANGE»
  "|- forall k c s e x z a p.        number_field k /\\        FINITE s /\\        (forall i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\\        (forall i. i IN s ==> p i IN infinite_places k) /\\        (forall j.             j IN s             ==> z j IN ring_carrier k /\\                 (exists m. 1 <= m /\\ ring_pow k (z j) m = ring_1 k) /\\                 x j =                 ring_mul k (z j)                 (group_sum (unit_group (ring_of_integers k)) s                 (\\l.                      group_zpow (unit_group (ring_of_integers k)) (e l)                      (a j l))))        ==> ring_det real_ring s (\\i j. c (p i) * log (p i (x j))) =            ring_det real_ring s (\\i j. c (p i) * log (p i (e j))) *            ring_det real_ring s (\\l j. real_of_int (a j l))"

-- RootsOfUnity
#eval thm' "RootsOfUnity.NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES" SessionANT.RootsOfUnity.«NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES»
  "|- forall k z m.        number_field k /\\        z IN ring_carrier k /\\        ring_order k z = m /\\        ~(m = 0)        ==> phi m divides            extension_degree (subfield_generated k {ring_0 k},k) I"
#eval thm' "RootsOfUnity.NUMBER_FIELD_REAL_ROOTS_OF_UNITY" SessionANT.RootsOfUnity.«NUMBER_FIELD_REAL_ROOTS_OF_UNITY»
  "|- forall k.        number_field k /\\ ~(real_embeddings k = {})        ==> {x | x IN ring_carrier k /\\                 (exists n. 1 <= n /\\ ring_pow k x n = ring_1 k)} =            {ring_1 k, ring_neg k (ring_1 k)}"

-- QuadraticUnits
#eval thm' "QuadraticUnits.NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL" SessionANT.QuadraticUnits.«NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL»
  "|- forall k g.        number_field k /\\        CARD (infinite_places k) = 2 /\\        g IN real_embeddings k        ==> (exists e.                 ring_unit (ring_of_integers k) e /\\                 &1 < Re (g e) /\\                 (forall u.                      ring_unit (ring_of_integers k) u <=>                      (exists n.                           u =                           group_zpow (unit_group (ring_of_integers k)) e n \\/                           u =                           ring_neg k                           (group_zpow (unit_group (ring_of_integers k)) e n))) /\\                 (forall n.                      group_zpow (unit_group (ring_of_integers k)) e n =                      ring_1 k                      ==> n = &0) /\\                 (forall u.                      ring_unit (ring_of_integers k) u /\\ &1 < Re (g u)                      ==> Re (g e) <= Re (g u)))"
#eval thm' "QuadraticUnits.QUADRATIC_FIELD_UNITS_IMAGINARY_CARD" SessionANT.QuadraticUnits.«QUADRATIC_FIELD_UNITS_IMAGINARY_CARD»
  "|- forall k x d.        number_field k /\\        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\\        x IN ring_carrier k /\\        ring_pow k x 2 = ring_of_int k d /\\        squarefree (num_of_int (abs d)) /\\        d < &0        ==> {u | ring_unit (ring_of_integers k) u} HAS_SIZE            (if d = -- &1 then 4 else if d = -- &3 then 6 else 2)"

-- Stickelberger
#eval thm' "Stickelberger.RING_DET_PERMANENT_MOD_4" SessionANT.Stickelberger.«RING_DET_PERMANENT_MOD_4»
  "|- forall k s f a d.        field k /\\        ring_char k = 0 /\\        FINITE s /\\        (forall i j.             i IN s /\\ j IN s ==> f i j IN ring_carrier (ring_of_integers k)) /\\        ring_sum k {p | p permutes s} (\\p. ring_product k s (\\i. f i (p i))) =        ring_of_int k a /\\        ring_pow k (ring_det k s f) 2 = ring_of_int k d        ==> (d == a pow 2) (mod &4)"
#eval thm' "Stickelberger.NUMBER_FIELD_PERMANENT_INTEGRAL" SessionANT.Stickelberger.«NUMBER_FIELD_PERMANENT_INTEGRAL»
  "|- forall k s e w.        number_field k /\\        (forall j. j IN s ==> w j IN ring_carrier (ring_of_integers k)) /\\        (forall i j. i IN s /\\ j IN s /\\ e i = e j ==> i = j) /\\        IMAGE e s = complex_embeddings k        ==> (exists a.                 ring_sum complex_ring {p | p permutes s}                 (\\p. ring_product complex_ring s (\\i. e i (w (p i)))) =                 Cx (real_of_int a))"

-- ProductFormula
#eval thm' "ProductFormula.NUMBER_FIELD_PRODUCT_FORMULA" SessionANT.ProductFormula.«NUMBER_FIELD_PRODUCT_FORMULA»
  "|- forall k x.        number_field k /\\ x IN ring_carrier k /\\ ~(x = ring_0 k)        ==> FINITE            {P | prime_ideal (ring_of_integers k) P /\\                 ~(P = {ring_0 k}) /\\                 ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)} /\\            product            {P | prime_ideal (ring_of_integers k) P /\\                 ~(P = {ring_0 k}) /\\                 ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}            (\\P.                 &(ideal_norm (ring_of_integers k) P) zpow                 --dedekind_valuation (ring_of_integers k,k) I P x) *            product (complex_embeddings k) (\\g. norm (g x)) =            &1"
#eval thm' "ProductFormula.COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE" SessionANT.ProductFormula.«COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE»
  "|- forall k g.        field k /\\ g IN complex_embeddings k        ==> absolute_value k (\\x. norm (g x))"

-- SunitRank
#eval thm' "SunitRank.GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP" SessionANT.SunitRank.«GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP»
  "|- forall k S.        number_field k        ==> group_homomorphism            (unit_group (ring_of_integers k),s_unit_group k S)            I"
#eval thm' "SunitRank.S_UNIT_GROUP_BOUNDED_EMBEDDINGS" SessionANT.SunitRank.«S_UNIT_GROUP_BOUNDED_EMBEDDINGS»
  "|- forall k S v0 b x.        number_field k /\\        FINITE S /\\        v0 IN infinite_places k /\\        &1 <= b /\\        x IN group_carrier (s_unit_group k S) /\\        (forall v.             v IN infinite_places k /\\ ~(v = v0) ==> inv b <= v x /\\ v x <= b) /\\        (forall P.             P IN S /\\ prime_ideal (ring_of_integers k) P /\\ ~(P = {ring_0 k})             ==> &(ideal_norm (ring_of_integers k) P) zpow                 dedekind_valuation (ring_of_integers k,k) I P x <=                 b)        ==> (forall g.                 g IN complex_embeddings k                 ==> norm (g x) <=                     b pow (CARD S + CARD (complex_embeddings k)))"

-- ValuationRankOne
#eval thm' "ValuationRankOne.VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION" SessionANT.ValuationRankOne.«VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION»
  "|- forall k v m p l.        valuation_subring k v /\\        maximal_ideal (subring_generated k v) m /\\        prime p /\\        (forall n. ring_of_int k n IN m <=> &p divides n) /\\        l subfield_of k /\\        number_field (subfield_generated k l)        ==> ~(m INTER ring_carrier (ring_of_integers (subfield_generated k l)) =              {ring_0 k}) /\\            dedekind_valuation            (ring_of_integers (subfield_generated k l),subfield_generated k l)            I            (m INTER ring_carrier (ring_of_integers (subfield_generated k l)))            (ring_of_num k p) =            &(ramification_index              (integer_ring,ring_of_integers (subfield_generated k l))              (ring_of_int (ring_of_integers (subfield_generated k l)))             (m INTER              ring_carrier (ring_of_integers (subfield_generated k l)))) /\\            ~(ramification_index              (integer_ring,ring_of_integers (subfield_generated k l))              (ring_of_int (ring_of_integers (subfield_generated k l)))              (m INTER               ring_carrier (ring_of_integers (subfield_generated k l))) =              0)"
#eval thm' "ValuationRankOne.VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO" SessionANT.ValuationRankOne.«VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO»
  "|- forall k v m p l l' x.        valuation_subring k v /\\        maximal_ideal (subring_generated k v) m /\\        prime p /\\        (forall n. ring_of_int k n IN m <=> &p divides n) /\\        l subfield_of k /\\        number_field (subfield_generated k l) /\\        l' subfield_of k /\\        number_field (subfield_generated k l') /\\        l SUBSET l' /\\        x IN l /\\        ~(x = ring_0 k)        ==> real_of_int            (dedekind_valuation             (ring_of_integers (subfield_generated k l'),              subfield_generated k l')             I             (m INTER              ring_carrier (ring_of_integers (subfield_generated k l')))            x) /            real_of_int            (dedekind_valuation             (ring_of_integers (subfield_generated k l'),              subfield_generated k l')             I             (m INTER              ring_carrier (ring_of_integers (subfield_generated k l')))            (ring_of_num k p)) =            real_of_int            (dedekind_valuation             (ring_of_integers (subfield_generated k l),              subfield_generated k l)             I             (m INTER              ring_carrier (ring_of_integers (subfield_generated k l)))            x) /            real_of_int            (dedekind_valuation             (ring_of_integers (subfield_generated k l),              subfield_generated k l)             I             (m INTER              ring_carrier (ring_of_integers (subfield_generated k l)))            (ring_of_num k p))"

-- AbsoluteValues
#eval thm' "AbsoluteValues.ABSOLUTE_VALUE_EQUIVALENT" SessionANT.AbsoluteValues.«ABSOLUTE_VALUE_EQUIVALENT»
  "|- forall k f1 f2.        field k /\\        absolute_value k f1 /\\        absolute_value k f2 /\\        (exists x. x IN ring_carrier k /\\ ~(x = ring_0 k) /\\ ~(f1 x = &1))        ==> ((exists s.                  &0 < s /\\                  (forall x. x IN ring_carrier k ==> f2 x = f1 x rpow s)) <=>             (forall x. x IN ring_carrier k /\\ f1 x < &1 ==> f2 x < &1))"
#eval thm' "AbsoluteValues.ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE" SessionANT.AbsoluteValues.«ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE»
  "|- forall k f1 f2.        field k /\\        absolute_value k f1 /\\        absolute_value k f2 /\\        (exists x. x IN ring_carrier k /\\ ~(x = ring_0 k) /\\ ~(f1 x = &1)) /\\        (exists x. x IN ring_carrier k /\\ ~(x = ring_0 k) /\\ ~(f2 x = &1)) /\\        ~(exists s.              &0 < s /\\ (forall x. x IN ring_carrier k ==> f2 x = f1 x rpow s))        ==> (exists z. z IN ring_carrier k /\\ &1 < f1 z /\\ f2 z < &1)"

-- Places
#eval thm' "Places.NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS" SessionANT.Places.«NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS»
  "|- forall k f x.        field k /\\        nonarchimedean_absolute_value k f /\\        x IN ring_carrier (ring_of_integers k)        ==> f x <= &1"
#eval thm' "Places.OSTROWSKI_NUM_LEMMA" SessionANT.Places.«OSTROWSKI_NUM_LEMMA»
  "|- forall g.        g 0 = &0 /\\        g 1 = &1 /\\        (forall n. &0 <= g n) /\\        (forall m n. g (m * n) = g m * g n) /\\        (forall m n. g (m + n) <= g m + g n) /\\        (exists n. &1 < g n)        ==> (exists s. &0 < s /\\ (forall n. g n = &n rpow s))"

-- RamificationGroups
#eval thm' "RamificationGroups.RING_HOMOMORPHISM_POW_DIFFERENCE" SessionANT.RamificationGroups.«RING_HOMOMORPHISM_POW_DIFFERENCE»
  "|- forall r k f x m.        ring_homomorphism (r,r) f /\\        ring_ideal r k /\\        x IN ring_carrier r /\\        ring_mul r (ring_sub r (f x) x) (ring_sub r (f x) x) IN k        ==> ring_sub r            (ring_mul r x (ring_sub r (f (ring_pow r x m)) (ring_pow r x m)))            (ring_mul r (ring_of_num r m)            (ring_mul r (ring_pow r x m) (ring_sub r (f x) x))) IN            k"
#eval thm' "RamificationGroups.INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS" SessionANT.RamificationGroups.«INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS»
  "|- forall h k l b Q t i f.        subring_generated l (ring_carrier b) = b /\\        (forall f.             f IN group_carrier (galois_group (k,l) h)             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\\        dedekind_domain b /\\        prime_ideal b Q /\\        ~(Q = {ring_0 l}) /\\        t IN Q /\\        ~(t IN ideal_pow b Q 2) /\\        f IN group_carrier (inertia_group (k,l) h b (ideal_pow b Q (i + 1)))        ==> (exists a.                 a IN ideal_pow b Q i /\\                 ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t) IN                 ideal_pow b Q (i + 2))"

-- PowerBasisExtension
#eval thm' "PowerBasisExtension.FIELD_POWER_BASIS_EMBEDDINGS" SessionANT.PowerBasisExtension.«FIELD_POWER_BASIS_EMBEDDINGS»
  "|- forall h k l a.        finite_extension (k,l) h /\\        separable_extension (k,l) h /\\        a IN ring_carrier l /\\        subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l        ==> (exists m g e.                 field m /\\                 ring_monomorphism (k,m) g /\\                 (forall t.                      t < extension_degree (k,l) h                      ==> ring_homomorphism (l,m) (e t) /\\                          (forall y. y IN ring_carrier k ==> e t (h y) = g y)) /\\                 (forall u v.                      u < extension_degree (k,l) h /\\                      v < extension_degree (k,l) h                      ==> (e u a = e v a <=> u = v)) /\\                 g o minimal_polynomial (k,l) h a =                 ring_product (poly_ring m (:1))                 {t | t < extension_degree (k,l) h}                 (\\t. poly_sub m (poly_var m one) (poly_const m (e t a))) /\\                 (forall t.                      t < extension_degree (k,l) h                      ==> e t                          (poly_extend (k,l) h (\\v. a)                          (poly_deriv k (minimal_polynomial (k,l) h a))) =                          ring_product m                          ({s | s < extension_degree (k,l) h} DELETE t)                          (\\s. ring_sub m (e t a) (e s a))) /\\                 (forall x.                      x IN ring_carrier l                      ==> g (algebra_trace (k,l) h x) =                          ring_sum m {t | t < extension_degree (k,l) h}                          (\\t. e t x)))"
#eval thm' "PowerBasisExtension.NUMBER_FIELD_CODIFFERENT_POWER_BASIS_Q" SessionANT.PowerBasisExtension.«NUMBER_FIELD_CODIFFERENT_POWER_BASIS_Q»
  "|- forall k a f d.        number_field k /\\        a IN ring_carrier (ring_of_integers k) /\\        f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\\        poly_deg (subfield_generated k {ring_0 k}) f =        extension_degree (subfield_generated k {ring_0 k},k) I /\\        d =        poly_extend (subfield_generated k {ring_0 k},k) I (\\v. a)        (poly_deriv (subfield_generated k {ring_0 k}) f)        ==> ~(d = ring_0 k) /\\            {x | x IN ring_carrier k /\\                 (forall y.                      y IN ring_carrier (subring_generated k {a})                      ==> algebra_trace (subfield_generated k {ring_0 k},k) I                          (ring_mul k x y) IN                          ring_carrier (ring_of_integers k))} =            IMAGE (ring_mul k (ring_inv k d))            (ring_carrier (subring_generated k {a}))"

-- HilbertFormula
#eval thm' "HilbertFormula.NSUM_CARD_SUBSETS_DELETE" SessionANT.HilbertFormula.«NSUM_CARD_SUBSETS_DELETE»
  "|- forall G e H n.        FINITE G /\\ (forall i. i < n ==> H i SUBSET G /\\ e IN H i)        ==> nsum (G DELETE e) (\\g. CARD {i | i < n /\\ g IN H i}) =            nsum {i | i < n} (\\i. CARD (H i) - 1)"
#eval thm' "HilbertFormula.NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA" SessionANT.HilbertFormula.«NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA»
  "|- forall h k l p Q.        number_field l /\\        galois_extension (k,l) h /\\        prime_ideal (ring_of_integers k) p /\\        ~(p = {ring_0 k}) /\\        prime_ideal (ring_of_integers l) Q /\\        IMAGE h p SUBSET Q        ==> ideal_valuation (ring_of_integers l) Q            (number_field_different (k,l) h) =            nsum (:num)            (\\i.                 CARD                 (group_carrier                 (inertia_group (k,l) h (ring_of_integers l)                 (ideal_pow (ring_of_integers l) Q (i + 1)))) -                 1)"

-- DedekindZeta
#eval thm' "DedekindZeta.DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS" SessionANT.DedekindZeta.«DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS»
  "|- forall a C c N0 s.        (forall m. &0 <= a m) /\\        &0 <= c /\\        (forall N. sum (1..N) a <= C * &N) /\\        (forall N. N0 <= N ==> c * &N <= sum (1..N) a) /\\        &1 < s        ==> real_summable (from 1) (\\m. a m / &m rpow s) /\\            c * real_infsum (from 1) (\\m. inv (&m rpow s)) - c * &N0 <=            real_infsum (from 1) (\\m. a m / &m rpow s) /\\            real_infsum (from 1) (\\m. a m / &m rpow s) <=            C * real_infsum (from 1) (\\m. inv (&m rpow s))"
#eval thm' "DedekindZeta.DEDEKIND_ZETA_EULER_PRODUCT_REAL" SessionANT.DedekindZeta.«DEDEKIND_ZETA_EULER_PRODUCT_REAL»
  "|- forall k s.        number_field k /\\ &1 < s        ==> ((\\n.                  product                  {P | prime_ideal (ring_of_integers k) P /\\                       ~(P = {ring_0 k}) /\\                       ideal_norm (ring_of_integers k) P <= n}                  (\\P.                       inv                       (&1 -                        inv (&(ideal_norm (ring_of_integers k) P) rpow s)))) --->             Re (dedekind_zeta k (Cx s)))            sequentially"

-- FrobeniusDensity
#eval thm' "FrobeniusDensity.NUMBER_FIELD_FIXED_FIELD_PRIME_DEGREE_ONE" SessionANT.FrobeniusDensity.«NUMBER_FIELD_FIXED_FIELD_PRIME_DEGREE_ONE»
  "|- forall h k l H p Q g.        number_field l /\\        galois_extension (k,l) h /\\        H subgroup_of galois_group (k,l) h /\\        prime_ideal (ring_of_integers k) p /\\        ~(p = {ring_0 k}) /\\        unramified (ring_of_integers k,ring_of_integers l) h p /\\        prime_ideal (ring_of_integers l) Q /\\        IMAGE h p SUBSET Q /\\        g IN group_carrier (galois_group (k,l) h)        ==> prime_ideal            (ring_of_integers (subfield_generated l (fixed_field l H)))            (IMAGE g Q INTER fixed_field l H) /\\            ~(IMAGE g Q INTER fixed_field l H = {ring_0 l}) /\\            IMAGE h p SUBSET IMAGE g Q INTER fixed_field l H /\\            (residue_degree             (ring_of_integers k,              ring_of_integers (subfield_generated l (fixed_field l H)))             h             (IMAGE g Q INTER fixed_field l H) =             1 <=>             group_conjugation (galois_group (k,l) h) g             (frobenius_element (k,l) h (ring_of_integers l) Q) IN             H)"
#eval thm' "FrobeniusDensity.NUMBER_FIELD_NONPRIME_NORM_SERIES" SessionANT.FrobeniusDensity.«NUMBER_FIELD_NONPRIME_NORM_SERIES»
  "|- forall k S s.        number_field k /\\        (forall p.             p IN S             ==> prime_ideal (ring_of_integers k) p /\\ ~(p = {ring_0 k})) /\\        &1 < s        ==> real_summable (from 1)            (\\m.                 &(if prime m                   then 0                   else CARD                        {p | p IN S /\\ ideal_norm (ring_of_integers k) p = m}) /                 &m rpow s) /\\            &0 <=            real_infsum (from 1)            (\\m.                 &(if prime m                   then 0                   else CARD                        {p | p IN S /\\ ideal_norm (ring_of_integers k) p = m}) /                 &m rpow s) /\\            real_infsum (from 1)            (\\m.                 &(if prime m                   then 0                   else CARD                        {p | p IN S /\\ ideal_norm (ring_of_integers k) p = m}) /                 &m rpow s) <=            &2 * &(extension_degree (subfield_generated k {ring_0 k},k) I)"

end T
