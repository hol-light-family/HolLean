/- File: HolTest/ECGeometryTest.lean
Runtime test suite: EC/misc.ml, EC/weierstrass.ml, EC/montgomery.ml, EC/edwards.ml, EC/projective.ml, EC/jacobian.ml, EC/xzprojective.ml, EC/exprojective.ml, EC/formulary_projective.ml, EC/formulary_jacobian.ml, EC/edmont.ml, EC/montwe.ml
(HolEC/, wired by SessionEC/).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "EC/<file>.ml"`, then `string_of_thm`, newlines joined).
tools/ec<file>diff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here.  The files are
in one test module so that each SessionEC module replays once. -/

import HolTest.CommonTest
import SessionEC.Misc
import SessionEC.Weierstrass
import SessionEC.Montgomery
import SessionEC.Edwards
import SessionEC.Projective
import SessionEC.Jacobian
import SessionEC.XZProjective
import SessionEC.EXProjective
import SessionEC.FormularyProjective
import SessionEC.FormularyJacobian
import SessionEC.Edmont
import SessionEC.Montwe

open HolCore.Kernel HolTest.CommonTest

#eval SessionEC.Misc.ensureMisc
#eval SessionEC.Weierstrass.ensureWeierstrass
#eval SessionEC.Montgomery.ensureMontgomery
#eval SessionEC.Edwards.ensureEdwards
#eval SessionEC.Projective.ensureProjective
#eval SessionEC.Jacobian.ensureJacobian
#eval SessionEC.XZProjective.ensureXZProjective
#eval SessionEC.EXProjective.ensureEXProjective
#eval SessionEC.FormularyProjective.ensureFormularyProjective
#eval SessionEC.FormularyJacobian.ensureFormularyJacobian
#eval SessionEC.Edmont.ensureEdmont
#eval SessionEC.Montwe.ensureMontwe

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

-- Misc
#eval thm' "Misc.FINITE_QUADRATIC_CURVE" SessionEC.Misc.«FINITE_QUADRATIC_CURVE»
  "|- forall r h.        integral_domain r /\\ FINITE (ring_carrier r)        ==> FINITE            {x,y | x IN ring_carrier r /\\                   y IN ring_carrier r /\\                   ring_pow r y 2 = h x} /\\            CARD            {x,y | x IN ring_carrier r /\\                   y IN ring_carrier r /\\                   ring_pow r y 2 = h x} <=            2 * CARD (ring_carrier r)"
#eval thm' "Misc.FIELD_CHAR_NOT2" SessionEC.Misc.«FIELD_CHAR_NOT2»
  "|- forall f P.        field f /\\ ~(ring_char f = 2) /\\ P <=>        field f /\\ ~(ring_char f divides 2) /\\ P"
#eval thm' "Misc.FIELD_CHAR_NOT3" SessionEC.Misc.«FIELD_CHAR_NOT3»
  "|- forall f P.        field f /\\ ~(ring_char f = 3) /\\ P <=>        field f /\\ ~(ring_char f divides 3) /\\ P"
#eval thm' "Misc.FIELD_CHAR_NOT23" SessionEC.Misc.«FIELD_CHAR_NOT23»
  "|- forall f P.        field f /\\ ~(ring_char f = 2) /\\ ~(ring_char f = 3) /\\ P <=>        field f /\\ ~(ring_char f divides 2) /\\ ~(ring_char f divides 3) /\\ P"
#eval thm' "Misc.CAUCHY_GROUP_THEOREM_2" SessionEC.Misc.«CAUCHY_GROUP_THEOREM_2»
  "|- forall G.        FINITE (group_carrier G) /\\ EVEN (CARD (group_carrier G))        ==> (exists x. x IN group_carrier G /\\ group_element_order G x = 2)"
#eval thm' "Misc.GROUP_ADHOC_ORDER_UNIQUE_LEMMA" SessionEC.Misc.«GROUP_ADHOC_ORDER_UNIQUE_LEMMA»
  "|- forall G a p.        FINITE (group_carrier G) /\\        CARD (group_carrier G) < 3 * p /\\        (forall x.             x IN group_carrier G /\\ group_inv G x = x ==> x = group_id G) /\\        a IN group_carrier G /\\        group_element_order G a = p        ==> group_carrier G HAS_SIZE p"
#eval thm' "Misc.SYMMETRY_LEMMA" SessionEC.Misc.«SYMMETRY_LEMMA»
  "|- forall P eq add.        (forall x y. P x /\\ P y /\\ eq x y ==> eq y x) /\\        (forall x y. P x /\\ P y ==> P (add x y)) /\\        (forall x y. P x /\\ P y ==> add x y = add y x) /\\        (forall x y z.             P x /\\ P y /\\ P z /\\ (eq x y \\/ eq (add x y) z)             ==> add x (add y z) = add (add x y) z) /\\        (forall x y z.             P x /\\             P y /\\             P z /\\             ~eq x y /\\             ~eq y z /\\             ~eq x z /\\             ~eq (add x y) z /\\             ~eq (add y z) x             ==> add x (add y z) = add (add x y) z)        ==> (forall x y z.                 P x /\\ P y /\\ P z ==> add x (add y z) = add (add x y) z)"
#eval thm' "Misc.ASSOCIATIVITY_LEMMA" SessionEC.Misc.«ASSOCIATIVITY_LEMMA»
  "|- forall P add neg id.        P id /\\        (forall x. P x ==> P (neg x)) /\\        (forall x y. P x /\\ P y ==> P (add x y)) /\\        (forall x. P x ==> add id x = x) /\\        (forall x. P x ==> add (neg x) x = id) /\\        (forall x y. P x /\\ P y ==> add x y = add y x) /\\        (forall x. P x ==> neg (neg x) = x) /\\        (forall x y. P x /\\ P y ==> neg (add x y) = add (neg x) (neg y)) /\\        (forall x y. P x /\\ P y ==> add x (add x y) = add (add x x) y) /\\        (forall x y. P x /\\ P y ==> add (neg x) (add x y) = y) /\\        (forall x y z u v.             P x /\\ P y /\\ P z /\\ P u /\\ P v             ==> ~(x = id) /\\                 ~(y = id) /\\                 ~(z = id) /\\                 ~(u = id) /\\                 ~(v = id) /\\                 ~(y = x \\/ y = neg x) /\\                 ~(z = y \\/ z = neg y) /\\                 ~(z = x \\/ z = neg x) /\\                 ~(z = u \\/ z = neg u) /\\                 ~(x = v \\/ x = neg v)             ==> add x y = u /\\ add y z = v             ==> add x v = add u z)        ==> (forall x y z.                 P x /\\ P y /\\ P z ==> add x (add y z) = add (add x y) z)"
#eval thm' "Misc.INTEGER_MOD_RING_ROOT_EXISTS" SessionEC.Misc.«INTEGER_MOD_RING_ROOT_EXISTS»
  "|- forall n a k.        (exists b.             b IN ring_carrier (integer_mod_ring n) /\\             ring_pow (integer_mod_ring n) b k = &a) <=>        (n = 0 \\/ a < n) /\\ (exists b. (b EXP k == a) (mod n))"

-- Weierstrass
#eval thm' "Weierstrass.weierstrass_point" SessionEC.Weierstrass.«weierstrass_point»
  "|- (weierstrass_point f NONE <=> true) /\\    (weierstrass_point f (SOME (x,y)) <=>     x IN ring_carrier f /\\ y IN ring_carrier f)"
#eval thm' "Weierstrass.weierstrass_curve" SessionEC.Weierstrass.«weierstrass_curve»
  "|- (weierstrass_curve (f,a,b) NONE <=> true) /\\    (weierstrass_curve (f,a,b) (SOME (x,y)) <=>     x IN ring_carrier f /\\     y IN ring_carrier f /\\     ring_pow f y 2 =     ring_add f (ring_pow f x 3) (ring_add f (ring_mul f a x) b))"
#eval thm' "Weierstrass.weierstrass_add" SessionEC.Weierstrass.«weierstrass_add»
  "|- (forall y. weierstrass_add (f,a,b) NONE y = y) /\\    (forall x. weierstrass_add (f,a,b) x NONE = x) /\\    (forall x1 y1 x2 y2.         weierstrass_add (f,a,b) (SOME (x1,y1)) (SOME (x2,y2)) =         (if x1 = x2          then if y1 = y2 /\\ ~(y1 = ring_0 f)               then let m =                        ring_div f                        (ring_add f                         (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))                        a)                        (ring_mul f (ring_of_num f 2) y1) in                    let x3 =                        ring_sub f (ring_pow f m 2)                        (ring_mul f (ring_of_num f 2) x1) in                    let y3 = ring_sub f (ring_mul f m (ring_sub f x1 x3)) y1 in                    SOME (x3,y3)               else NONE          else let m = ring_div f (ring_sub f y2 y1) (ring_sub f x2 x1) in               let x3 = ring_sub f (ring_pow f m 2) (ring_add f x1 x2) in               let y3 = ring_sub f (ring_mul f m (ring_sub f x1 x3)) y1 in               SOME (x3,y3)))"
#eval thm' "Weierstrass.weierstrass_group" SessionEC.Weierstrass.«weierstrass_group»
  "|- weierstrass_group (f,a,b) =    group    (weierstrass_curve (f,a,b),     NONE,     weierstrass_neg (f,a,b),     weierstrass_add (f,a,b))"
#eval thm' "Weierstrass.CARD_BOUND_WEIERSTRASS_CURVE" SessionEC.Weierstrass.«CARD_BOUND_WEIERSTRASS_CURVE»
  "|- forall f a b.        field f /\\ FINITE (ring_carrier f)        ==> CARD (weierstrass_curve (f,a,b)) <= 2 * CARD (ring_carrier f) + 1"
#eval thm' "Weierstrass.WEIERSTRASS_POINT_NEG" SessionEC.Weierstrass.«WEIERSTRASS_POINT_NEG»
  "|- forall f a b p.        weierstrass_point f p        ==> weierstrass_point f (weierstrass_neg (f,a,b) p)"
#eval thm' "Weierstrass.WEIERSTRASS_CURVE_0" SessionEC.Weierstrass.«WEIERSTRASS_CURVE_0»
  "|- forall f a b. weierstrass_curve (f,a,b) NONE"
#eval thm' "Weierstrass.WEIERSTRASS_CURVE_ADD" SessionEC.Weierstrass.«WEIERSTRASS_CURVE_ADD»
  "|- forall f a b p q.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        weierstrass_curve (f,a,b) p /\\        weierstrass_curve (f,a,b) q        ==> weierstrass_curve (f,a,b) (weierstrass_add (f,a,b) p q)"
#eval thm' "Weierstrass.WEIERSTRASS_ADD_SYM" SessionEC.Weierstrass.«WEIERSTRASS_ADD_SYM»
  "|- forall f a b p q.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        weierstrass_curve (f,a,b) p /\\        weierstrass_curve (f,a,b) q        ==> weierstrass_add (f,a,b) p q = weierstrass_add (f,a,b) q p"
#eval thm' "Weierstrass.WEIERSTRASS_ADD_ASSOC" SessionEC.Weierstrass.«WEIERSTRASS_ADD_ASSOC»
  "|- forall f a b p q r.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        weierstrass_nonsingular (f,a,b) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        weierstrass_curve (f,a,b) p /\\        weierstrass_curve (f,a,b) q /\\        weierstrass_curve (f,a,b) r        ==> weierstrass_add (f,a,b) p (weierstrass_add (f,a,b) q r) =            weierstrass_add (f,a,b) (weierstrass_add (f,a,b) p q) r"
#eval thm' "Weierstrass.weierstrass_triplex" SessionEC.Weierstrass.«weierstrass_triplex»
  "|- weierstrass_triplex f c NONE = NONE /\\    weierstrass_triplex f c (SOME (x,y)) = SOME (ring_mul f c x,y)"
#eval thm' "Weierstrass.weierstrass_quady" SessionEC.Weierstrass.«weierstrass_quady»
  "|- weierstrass_quady f c NONE = NONE /\\    weierstrass_quady f c (SOME (x,y)) = SOME (ring_neg f x,ring_mul f c y)"

-- Montgomery
#eval thm' "Montgomery.montgomery_point" SessionEC.Montgomery.«montgomery_point»
  "|- (montgomery_point f NONE <=> true) /\\    (montgomery_point f (SOME (x,y)) <=>     x IN ring_carrier f /\\ y IN ring_carrier f)"
#eval thm' "Montgomery.montgomery_curve" SessionEC.Montgomery.«montgomery_curve»
  "|- (montgomery_curve (f,a,b) NONE <=> true) /\\    (montgomery_curve (f,a,b) (SOME (x,y)) <=>     x IN ring_carrier f /\\     y IN ring_carrier f /\\     ring_mul f b (ring_pow f y 2) =     ring_add f (ring_pow f x 3)     (ring_add f (ring_mul f a (ring_pow f x 2)) x))"
#eval thm' "Montgomery.montgomery_neg" SessionEC.Montgomery.«montgomery_neg»
  "|- montgomery_neg (f,a,b) NONE = NONE /\\    montgomery_neg (f,a,b) (SOME (x,y)) = SOME (x,ring_neg f y)"
#eval thm' "Montgomery.montgomery_group" SessionEC.Montgomery.«montgomery_group»
  "|- montgomery_group (f,a,b) =    group    (montgomery_curve (f,a,b),     NONE,     montgomery_neg (f,a,b),     montgomery_add (f,a,b))"
#eval thm' "Montgomery.CARD_BOUND_MONTGOMERY_CURVE" SessionEC.Montgomery.«CARD_BOUND_MONTGOMERY_CURVE»
  "|- forall f a b.        field f /\\        FINITE (ring_carrier f) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        ~(b = ring_0 f)        ==> CARD (montgomery_curve (f,a,b)) <= 2 * CARD (ring_carrier f) + 1"
#eval thm' "Montgomery.montgomery_strongly_nonsingular" SessionEC.Montgomery.«montgomery_strongly_nonsingular»
  "|- montgomery_strongly_nonsingular (f,a,b) <=>    ~(b = ring_0 f) /\\    ~(exists z.          z IN ring_carrier f /\\          ring_pow f z 2 = ring_sub f (ring_pow f a 2) (ring_of_num f 4))"
#eval thm' "Montgomery.MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR" SessionEC.Montgomery.«MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR»
  "|- forall f a b.        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_strongly_nonsingular (f,a,b)        ==> montgomery_nonsingular (f,a,b)"
#eval thm' "Montgomery.MONTGOMERY_POINT_ADD" SessionEC.Montgomery.«MONTGOMERY_POINT_ADD»
  "|- forall f a b p q.        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_point f p /\\        montgomery_point f q        ==> montgomery_point f (montgomery_add (f,a,b) p q)"
#eval thm' "Montgomery.MONTGOMERY_CURVE_NEG" SessionEC.Montgomery.«MONTGOMERY_CURVE_NEG»
  "|- forall f a b p.        integral_domain f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_curve (f,a,b) p        ==> montgomery_curve (f,a,b) (montgomery_neg (f,a,b) p)"
#eval thm' "Montgomery.MONTGOMERY_CURVE_ADD" SessionEC.Montgomery.«MONTGOMERY_CURVE_ADD»
  "|- forall f a b p q.        field f /\\        ~(ring_char f = 2) /\\        montgomery_nonsingular (f,a,b) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_curve (f,a,b) p /\\        montgomery_curve (f,a,b) q        ==> montgomery_curve (f,a,b) (montgomery_add (f,a,b) p q)"
#eval thm' "Montgomery.MONTGOMERY_ADD_SYM" SessionEC.Montgomery.«MONTGOMERY_ADD_SYM»
  "|- forall f a b p q.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_curve (f,a,b) p /\\        montgomery_curve (f,a,b) q        ==> montgomery_add (f,a,b) p q = montgomery_add (f,a,b) q p"
#eval thm' "Montgomery.MONTGOMERY_GROUP" SessionEC.Montgomery.«MONTGOMERY_GROUP»
  "|- forall f a b.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b)        ==> group_carrier (montgomery_group (f,a,b)) =            montgomery_curve (f,a,b) /\\            group_id (montgomery_group (f,a,b)) = NONE /\\            group_inv (montgomery_group (f,a,b)) = montgomery_neg (f,a,b) /\\            group_mul (montgomery_group (f,a,b)) = montgomery_add (f,a,b)"

-- Edwards
#eval thm' "Edwards.edwards_point" SessionEC.Edwards.«edwards_point»
  "|- edwards_point f (x,y) <=> x IN ring_carrier f /\\ y IN ring_carrier f"
#eval thm' "Edwards.edwards_nonsingular" SessionEC.Edwards.«edwards_nonsingular»
  "|- edwards_nonsingular (f,a,d) <=>    (exists b. b IN ring_carrier f /\\ ring_pow f b 2 = a) /\\    (d = ring_0 f \\/ ~(exists c. c IN ring_carrier f /\\ ring_pow f c 2 = d))"
#eval thm' "Edwards.edwards_neg" SessionEC.Edwards.«edwards_neg»
  "|- edwards_neg (f,a,d) (x,y) = ring_neg f x,y"
#eval thm' "Edwards.edwards_group" SessionEC.Edwards.«edwards_group»
  "|- edwards_group (f,a,d) =    group    (edwards_curve (f,a,d),     edwards_0 (f,a,d),     edwards_neg (f,a,d),     edwards_add (f,a,d))"
#eval thm' "Edwards.CARD_BOUND_EDWARDS_CURVE" SessionEC.Edwards.«CARD_BOUND_EDWARDS_CURVE»
  "|- forall f a d.        field f /\\        FINITE (ring_carrier f) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        edwards_nonsingular (f,a,d)        ==> CARD (edwards_curve (f,a,d)) <= 2 * CARD (ring_carrier f)"
#eval thm' "Edwards.EDWARDS_NONSINGULAR_DENOMINATORS_POINTS" SessionEC.Edwards.«EDWARDS_NONSINGULAR_DENOMINATORS_POINTS»
  "|- forall f a d z z'.        field f /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        edwards_nonsingular (f,a,d) /\\        edwards_curve (f,a,d) (FST z,SND z) /\\        edwards_curve (f,a,d) (FST z',SND z')        ==> ~(ring_add f (ring_1 f)              (ring_mul f d              (ring_mul f (FST z)              (ring_mul f (SND z) (ring_mul f (FST z') (SND z'))))) =              ring_0 f) /\\            ~(ring_sub f (ring_1 f)              (ring_mul f d              (ring_mul f (FST z)              (ring_mul f (SND z) (ring_mul f (FST z') (SND z'))))) =              ring_0 f)"
#eval thm' "Edwards.EDWARDS_POINT_ADD" SessionEC.Edwards.«EDWARDS_POINT_ADD»
  "|- forall f a d p q.        a IN ring_carrier f /\\        d IN ring_carrier f /\\        edwards_point f p /\\        edwards_point f q        ==> edwards_point f (edwards_add (f,a,d) p q)"
#eval thm' "Edwards.EDWARDS_CURVE_NEG" SessionEC.Edwards.«EDWARDS_CURVE_NEG»
  "|- forall f a d p.        integral_domain f /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        edwards_curve (f,a,d) p        ==> edwards_curve (f,a,d) (edwards_neg (f,a,d) p)"
#eval thm' "Edwards.EDWARDS_ADD_LNEG" SessionEC.Edwards.«EDWARDS_ADD_LNEG»
  "|- forall f a d p.        field f /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        edwards_nonsingular (f,a,d) /\\        edwards_curve (f,a,d) p        ==> edwards_add (f,a,d) (edwards_neg (f,a,d) p) p = edwards_0 (f,a,d)"
#eval thm' "Edwards.EDWARDS_ADD_ASSOC" SessionEC.Edwards.«EDWARDS_ADD_ASSOC»
  "|- forall f a d p q r.        field f /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        edwards_nonsingular (f,a,d) /\\        edwards_curve (f,a,d) p /\\        edwards_curve (f,a,d) q /\\        edwards_curve (f,a,d) r        ==> edwards_add (f,a,d) p (edwards_add (f,a,d) q r) =            edwards_add (f,a,d) (edwards_add (f,a,d) p q) r"
#eval thm' "Edwards.ABELIAN_EDWARDS_GROUP" SessionEC.Edwards.«ABELIAN_EDWARDS_GROUP»
  "|- forall f a d.        field f /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        edwards_nonsingular (f,a,d)        ==> abelian_group (edwards_group (f,a,d))"
#eval thm' "Edwards.EDWARDS_GROUP_ELEMENT_ORDER_EQ_4_EQUIV" SessionEC.Edwards.«EDWARDS_GROUP_ELEMENT_ORDER_EQ_4_EQUIV»
  "|- forall f a d x y.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        edwards_nonsingular (f,a,d) /\\        x,y IN group_carrier (edwards_group (f,a,d))        ==> (group_element_order (edwards_group (f,a,d)) (x,y) = 4 <=>             ring_mul f a (ring_pow f x 2) = ring_1 f /\\ y = ring_0 f)"

-- Projective
#eval thm' "Projective.projective_curve" SessionEC.Projective.«projective_curve»
  "|- projective_curve (f,a,b) (x,y,z) <=>    x IN ring_carrier f /\\    y IN ring_carrier f /\\    z IN ring_carrier f /\\    ring_mul f (ring_pow f y 2) z =    ring_add f (ring_pow f x 3)    (ring_add f (ring_mul f a (ring_mul f x (ring_pow f z 2)))    (ring_mul f b (ring_pow f z 3)))"
#eval thm' "Projective.projective_of_weierstrass" SessionEC.Projective.«projective_of_weierstrass»
  "|- projective_of_weierstrass f NONE = ring_0 f,ring_1 f,ring_0 f /\\    projective_of_weierstrass f (SOME (x,y)) = x,y,ring_1 f"
#eval thm' "Projective.projective_0" SessionEC.Projective.«projective_0»
  "|- forall a b f. projective_0 (f,a,b) = ring_0 f,ring_1 f,ring_0 f"
#eval thm' "Projective.PROJECTIVE_OF_WEIERSTRASS_POINT" SessionEC.Projective.«PROJECTIVE_OF_WEIERSTRASS_POINT»
  "|- forall f p.        weierstrass_point f p        ==> projective_point f (projective_of_weierstrass f p)"
#eval thm' "Projective.PROJECTIVE_OF_WEIERSTRASS_EQ" SessionEC.Projective.«PROJECTIVE_OF_WEIERSTRASS_EQ»
  "|- forall f p q.        field f        ==> (projective_of_weierstrass f p = projective_of_weierstrass f q <=>             p = q)"
#eval thm' "Projective.WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS" SessionEC.Projective.«WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS»
  "|- forall f p.        field f /\\ weierstrass_point f p        ==> weierstrass_of_projective f (projective_of_weierstrass f p) = p"
#eval thm' "Projective.PROJECTIVE_OF_WEIERSTRASS_CURVE" SessionEC.Projective.«PROJECTIVE_OF_WEIERSTRASS_CURVE»
  "|- forall f a b p.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        weierstrass_curve (f,a,b) p        ==> projective_curve (f,a,b) (projective_of_weierstrass f p)"
#eval thm' "Projective.PROJECTIVE_POINT_NEG" SessionEC.Projective.«PROJECTIVE_POINT_NEG»
  "|- forall f a b p.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        projective_point f p        ==> projective_point f (projective_neg (f,a,b) p)"
#eval thm' "Projective.WEIERSTRASS_OF_PROJECTIVE_NEG" SessionEC.Projective.«WEIERSTRASS_OF_PROJECTIVE_NEG»
  "|- forall f a b p.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        projective_point f p        ==> weierstrass_of_projective f (projective_neg (f,a,b) p) =            weierstrass_neg (f,a,b) (weierstrass_of_projective f p)"
#eval thm' "Projective.PROJECTIVE_OF_WEIERSTRASS_NEG" SessionEC.Projective.«PROJECTIVE_OF_WEIERSTRASS_NEG»
  "|- forall f a b p.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        weierstrass_point f p        ==> projective_eq f            (projective_of_weierstrass f (weierstrass_neg (f,a,b) p))            (projective_neg (f,a,b) (projective_of_weierstrass f p))"
#eval thm' "Projective.PROJECTIVE_CURVE_ADD" SessionEC.Projective.«PROJECTIVE_CURVE_ADD»
  "|- forall f a b p q.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        projective_curve (f,a,b) p /\\        projective_curve (f,a,b) q        ==> projective_curve (f,a,b) (projective_add (f,a,b) p q)"
#eval thm' "Projective.PROJECTIVE_EQ_ADD" SessionEC.Projective.«PROJECTIVE_EQ_ADD»
  "|- forall f a b p p' q q'.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        projective_point f p /\\        projective_point f p' /\\        projective_point f q /\\        projective_point f q' /\\        projective_eq f p p' /\\        projective_eq f q q'        ==> projective_eq f (projective_add (f,a,b) p q)            (projective_add (f,a,b) p' q')"

-- Jacobian
#eval thm' "Jacobian.jacobian_curve" SessionEC.Jacobian.«jacobian_curve»
  "|- jacobian_curve (f,a,b) (x,y,z) <=>    x IN ring_carrier f /\\    y IN ring_carrier f /\\    z IN ring_carrier f /\\    ring_pow f y 2 =    ring_add f (ring_pow f x 3)    (ring_add f (ring_mul f a (ring_mul f x (ring_pow f z 4)))    (ring_mul f b (ring_pow f z 6)))"
#eval thm' "Jacobian.jacobian_of_weierstrass" SessionEC.Jacobian.«jacobian_of_weierstrass»
  "|- jacobian_of_weierstrass f NONE = ring_1 f,ring_1 f,ring_0 f /\\    jacobian_of_weierstrass f (SOME (x,y)) = x,y,ring_1 f"
#eval thm' "Jacobian.jacobian_neg" SessionEC.Jacobian.«jacobian_neg»
  "|- forall a b x f y z. jacobian_neg (f,a,b) (x,y,z) = x,ring_neg f y,z"
#eval thm' "Jacobian.JACOBIAN_OF_WEIERSTRASS_POINT" SessionEC.Jacobian.«JACOBIAN_OF_WEIERSTRASS_POINT»
  "|- forall f p.        weierstrass_point f p        ==> jacobian_point f (jacobian_of_weierstrass f p)"
#eval thm' "Jacobian.WEIERSTRASS_OF_JACOBIAN_EQ" SessionEC.Jacobian.«WEIERSTRASS_OF_JACOBIAN_EQ»
  "|- forall f p q.        field f /\\ jacobian_point f p /\\ jacobian_point f q        ==> (weierstrass_of_jacobian f p = weierstrass_of_jacobian f q <=>             jacobian_eq f p q)"
#eval thm' "Jacobian.JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN" SessionEC.Jacobian.«JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN»
  "|- forall f p.        field f /\\ jacobian_point f p        ==> jacobian_eq f            (jacobian_of_weierstrass f (weierstrass_of_jacobian f p))            p"
#eval thm' "Jacobian.WEIERSTRASS_OF_JACOBIAN_CURVE" SessionEC.Jacobian.«WEIERSTRASS_OF_JACOBIAN_CURVE»
  "|- forall f a b p.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        jacobian_curve (f,a,b) p        ==> weierstrass_curve (f,a,b) (weierstrass_of_jacobian f p)"
#eval thm' "Jacobian.WEIERSTRASS_OF_JACOBIAN_NEG" SessionEC.Jacobian.«WEIERSTRASS_OF_JACOBIAN_NEG»
  "|- forall f a b p.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        jacobian_point f p        ==> weierstrass_of_jacobian f (jacobian_neg (f,a,b) p) =            weierstrass_neg (f,a,b) (weierstrass_of_jacobian f p)"
#eval thm' "Jacobian.JACOBIAN_OF_WEIERSTRASS_NEG" SessionEC.Jacobian.«JACOBIAN_OF_WEIERSTRASS_NEG»
  "|- forall f a b p.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        weierstrass_point f p        ==> jacobian_eq f            (jacobian_of_weierstrass f (weierstrass_neg (f,a,b) p))            (jacobian_neg (f,a,b) (jacobian_of_weierstrass f p))"
#eval thm' "Jacobian.JACOBIAN_CURVE_ADD" SessionEC.Jacobian.«JACOBIAN_CURVE_ADD»
  "|- forall f a b p q.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        jacobian_curve (f,a,b) p /\\        jacobian_curve (f,a,b) q        ==> jacobian_curve (f,a,b) (jacobian_add (f,a,b) p q)"
#eval thm' "Jacobian.WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS" SessionEC.Jacobian.«WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS»
  "|- forall f a b p q.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        weierstrass_point f p /\\        weierstrass_point f q        ==> weierstrass_of_jacobian f            (jacobian_add (f,a,b) (jacobian_of_weierstrass f p)            (jacobian_of_weierstrass f q)) =            weierstrass_add (f,a,b) p q"
#eval thm' "Jacobian.WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL" SessionEC.Jacobian.«WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL»
  "|- forall f a b p q.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        jacobian_point f p /\\        jacobian_point f q /\\        ~jacobian_eq f p q        ==> weierstrass_of_jacobian f (jacobian_add_unexceptional (f,a,b) p q) =            weierstrass_add (f,a,b) (weierstrass_of_jacobian f p)            (weierstrass_of_jacobian f q)"

-- XZProjective
#eval thm' "XZProjective.montgomery_xz" SessionEC.XZProjective.«montgomery_xz»
  "|- (montgomery_xz f NONE (X,Z) <=>     X IN ring_carrier f /\\     Z IN ring_carrier f /\\     ~(X = ring_0 f) /\\     Z = ring_0 f) /\\    (montgomery_xz f (SOME (x,y)) (X,Z) <=>     X IN ring_carrier f /\\     Z IN ring_carrier f /\\     ~(Z = ring_0 f) /\\     ring_div f X Z = x)"
#eval thm' "XZProjective.montgomery_xzdouble" SessionEC.XZProjective.«montgomery_xzdouble»
  "|- montgomery_xzdouble (f,a,b) (X,Z) =    ring_pow f (ring_sub f (ring_pow f X 2) (ring_pow f Z 2)) 2,    ring_mul f (ring_mul f (ring_of_num f 4) (ring_mul f X Z))    (ring_add f (ring_pow f X 2)    (ring_add f (ring_mul f a (ring_mul f X Z)) (ring_pow f Z 2)))"
#eval thm' "XZProjective.montgomery_xzdiffadd" SessionEC.XZProjective.«montgomery_xzdiffadd»
  "|- montgomery_xzdiffadd (f,a,b) (X,Z) (Xm,Zm) (Xn,Zn) =    ring_mul f (ring_mul f (ring_of_num f 4) Z)    (ring_pow f (ring_sub f (ring_mul f Xm Xn) (ring_mul f Zm Zn)) 2),    ring_mul f (ring_mul f (ring_of_num f 4) X)    (ring_pow f (ring_sub f (ring_mul f Xm Zn) (ring_mul f Xn Zm)) 2)"
#eval thm' "XZProjective.MONTGOMERY_XZDOUBLE" SessionEC.XZProjective.«MONTGOMERY_XZDOUBLE»
  "|- forall f a b p q.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b) /\\        montgomery_curve (f,a,b) p /\\        montgomery_xz f p q        ==> montgomery_xz f (montgomery_add (f,a,b) p p)            (montgomery_xzdouble (f,a,b) q)"
#eval thm' "XZProjective.MONTGOMERY_XZDIFFADD" SessionEC.XZProjective.«MONTGOMERY_XZDIFFADD»
  "|- forall f a b p q pm qm pn qn.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b) /\\        montgomery_curve (f,a,b) p /\\        montgomery_curve (f,a,b) pm /\\        montgomery_curve (f,a,b) pn /\\        montgomery_xz f p q /\\        montgomery_xz f pm qm /\\        montgomery_xz f pn qn /\\        ~(FST q = ring_0 f) /\\        ~(SND q = ring_0 f) /\\        montgomery_add (f,a,b) pm (montgomery_neg (f,a,b) pn) = p        ==> montgomery_xz f (montgomery_add (f,a,b) pm pn)            (montgomery_xzdiffadd (f,a,b) q qm qn)"
#eval thm' "XZProjective.MONTGOMERY_XZDOUBLE_GROUP" SessionEC.XZProjective.«MONTGOMERY_XZDOUBLE_GROUP»
  "|- forall f a b p n q.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b) /\\        p IN group_carrier (montgomery_group (f,a,b)) /\\        montgomery_xz f (group_pow (montgomery_group (f,a,b)) p n) q        ==> montgomery_xz f (group_pow (montgomery_group (f,a,b)) p (2 * n))            (montgomery_xzdouble (f,a,b) q)"
#eval thm' "XZProjective.MONTGOMERY_XZDIFFADD_GROUP" SessionEC.XZProjective.«MONTGOMERY_XZDIFFADD_GROUP»
  "|- forall f a b p n q qm qn.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b) /\\        ~(FST q = ring_0 f) /\\        ~(SND q = ring_0 f) /\\        p IN group_carrier (montgomery_group (f,a,b)) /\\        montgomery_xz f p q /\\        montgomery_xz f (group_pow (montgomery_group (f,a,b)) p (n + 1)) qm /\\        montgomery_xz f (group_pow (montgomery_group (f,a,b)) p n) qn        ==> montgomery_xz f            (group_pow (montgomery_group (f,a,b)) p (2 * n + 1))            (montgomery_xzdiffadd (f,a,b) q qm qn)"
#eval thm' "XZProjective.montgomery_xmap" SessionEC.XZProjective.«montgomery_xmap»
  "|- montgomery_xmap f NONE = ring_0 f /\\ montgomery_xmap f (SOME (x,y)) = x"
#eval thm' "XZProjective.MONTGOMERY_XZ_XMAP" SessionEC.XZProjective.«MONTGOMERY_XZ_XMAP»
  "|- forall f P X.        field f /\\ X IN ring_carrier f /\\ ~(X = ring_0 f)        ==> (montgomery_xz f P (X,ring_1 f) <=> montgomery_xmap f P = X)"
#eval thm' "XZProjective.MONTGOMERY_XMAP_EQ_0" SessionEC.XZProjective.«MONTGOMERY_XMAP_EQ_0»
  "|- forall f a b P.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b) /\\        P IN group_carrier (montgomery_group (f,a,b))        ==> (montgomery_xmap f P = ring_0 f <=>             P = NONE \\/ P = SOME (ring_0 f,ring_0 f))"
#eval thm' "XZProjective.MONTGOMERY_XMAP_EQ_0_POW" SessionEC.XZProjective.«MONTGOMERY_XMAP_EQ_0_POW»
  "|- forall f a b P n.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b) /\\        P IN group_carrier (montgomery_group (f,a,b)) /\\        montgomery_xmap f P = ring_0 f        ==> montgomery_xmap f (group_pow (montgomery_group (f,a,b)) P n) =            ring_0 f"
#eval thm' "XZProjective.MONTGOMERY_ADD_YRECOVERY" SessionEC.XZProjective.«MONTGOMERY_ADD_YRECOVERY»
  "|- forall f a b x y x1 y1 x2 y2.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        ~(b = ring_0 f) /\\        montgomery_curve (f,a,b) (SOME (x,y)) /\\        ~(y = ring_0 f) /\\        montgomery_curve (f,a,b) (SOME (x1,y1)) /\\        montgomery_add (f,a,b) (SOME (x,y)) (SOME (x1,y1)) = SOME (x2,y2)        ==> y1 =            ring_div f            (ring_sub f             (ring_sub f              (ring_mul f (ring_add f (ring_mul f x1 x) (ring_1 f))              (ring_add f x1 (ring_add f x (ring_mul f (ring_of_num f 2) a))))             (ring_mul f (ring_of_num f 2) a))            (ring_mul f (ring_pow f (ring_sub f x1 x) 2) x2))            (ring_mul f (ring_of_num f 2) (ring_mul f b y))"

-- EXProjective
#eval thm' "EXProjective.exprojective" SessionEC.EXProjective.«exprojective»
  "|- exprojective f (x,y) (X,Y,Z,W) <=>    x IN ring_carrier f /\\    y IN ring_carrier f /\\    X IN ring_carrier f /\\    Y IN ring_carrier f /\\    W IN ring_carrier f /\\    Z IN ring_carrier f /\\    ~(Z = ring_0 f) /\\    ring_div f X Z = x /\\    ring_div f Y Z = y /\\    ring_div f W Z = ring_mul f x y"
#eval thm' "EXProjective.EXPROJECTIVE_ALT" SessionEC.EXProjective.«EXPROJECTIVE_ALT»
  "|- forall f x y X Y Z W.        field f        ==> (exprojective f (x,y) (X,Y,Z,W) <=>             x IN ring_carrier f /\\             y IN ring_carrier f /\\             X IN ring_carrier f /\\             Y IN ring_carrier f /\\             W IN ring_carrier f /\\             Z IN ring_carrier f /\\             ~(Z = ring_0 f) /\\             ring_mul f x Z = X /\\             ring_mul f y Z = Y /\\             ring_mul f W Z = ring_mul f X Y)"
#eval thm' "EXProjective.PROJECTIVE_ALT" SessionEC.EXProjective.«PROJECTIVE_ALT»
  "|- forall f x y X Y Z.        field f        ==> (projective f (x,y) (X,Y,Z) <=>             x IN ring_carrier f /\\             y IN ring_carrier f /\\             X IN ring_carrier f /\\             Y IN ring_carrier f /\\             Z IN ring_carrier f /\\             ~(Z = ring_0 f) /\\             ring_mul f x Z = X /\\             ring_mul f y Z = Y)"
#eval thm' "EXProjective.EXPROJECTIVE_PROJECTIVE" SessionEC.EXProjective.«EXPROJECTIVE_PROJECTIVE»
  "|- forall f x y X Y Z W.        field f        ==> (exprojective f (x,y) (X,Y,Z,W) <=>             projective f (x,y) (X,Y,Z) /\\ ring_div f (ring_mul f X Y) Z = W)"
#eval thm' "EXProjective.EDWARDS_EXCURVE" SessionEC.EXProjective.«EDWARDS_EXCURVE»
  "|- forall f a d p Q.        field f /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        exprojective f p Q        ==> (edwards_curve (f,a,d) p <=> edwards_excurve (f,a,d) Q)"
#eval thm' "EXProjective.edwards_exprojadd" SessionEC.EXProjective.«edwards_exprojadd»
  "|- edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) =    ring_mul f (ring_add f (ring_mul f X1 Y2) (ring_mul f Y1 X2))    (ring_sub f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),    ring_mul f    (ring_sub f (ring_mul f Y1 Y2) (ring_mul f a (ring_mul f X1 X2)))    (ring_add f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),    ring_mul f    (ring_sub f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2)))    (ring_add f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),    ring_mul f    (ring_sub f (ring_mul f Y1 Y2) (ring_mul f a (ring_mul f X1 X2)))    (ring_add f (ring_mul f X1 Y2) (ring_mul f Y1 X2))"
#eval thm' "EXProjective.edwards_exprojadd4" SessionEC.EXProjective.«edwards_exprojadd4»
  "|- edwards_exprojadd4 (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) =    (let X3,Y3,Z3,T3 = edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) in     ring_mul f (ring_of_num f 4) X3,     ring_mul f (ring_of_num f 4) Y3,     ring_mul f (ring_of_num f 4) Z3,     ring_mul f (ring_of_num f 4) T3)"
#eval thm' "EXProjective.edwards_exprojaddn" SessionEC.EXProjective.«edwards_exprojaddn»
  "|- edwards_exprojaddn (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) =    (let X3,Y3,Z3,T3 = edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) in     ring_neg f X3,ring_neg f Y3,ring_neg f Z3,ring_neg f T3)"
#eval thm' "EXProjective.edwards_prexprojdouble" SessionEC.EXProjective.«edwards_prexprojdouble»
  "|- edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) =    ring_mul f (ring_of_num f 2)    (ring_mul f X1    (ring_mul f Y1    (ring_sub f     (ring_sub f (ring_mul f (ring_of_num f 2) (ring_pow f Z1 2))     (ring_pow f Y1 2))    (ring_mul f a (ring_pow f X1 2))))),    ring_mul f (ring_add f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2)))    (ring_sub f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2))),    ring_mul f (ring_add f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2)))    (ring_sub f     (ring_sub f (ring_mul f (ring_of_num f 2) (ring_pow f Z1 2))     (ring_pow f Y1 2))    (ring_mul f a (ring_pow f X1 2))),    ring_mul f (ring_of_num f 2)    (ring_mul f X1    (ring_mul f Y1    (ring_sub f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2)))))"
#eval thm' "EXProjective.edwards_exprojdouble" SessionEC.EXProjective.«edwards_exprojdouble»
  "|- edwards_exprojdouble (f,a,d) (X1,Y1,Z1,T1) =    edwards_prexprojdouble (f,a,d) (X1,Y1,Z1)"
#eval thm' "EXProjective.edwards_projdouble" SessionEC.EXProjective.«edwards_projdouble»
  "|- edwards_projdouble (f,a,d) (X1,Y1,Z1) =    (let X2,Y2,Z2,T2 = edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) in X2,Y2,Z2)"
#eval thm' "EXProjective.edwards_prexprojdoublen" SessionEC.EXProjective.«edwards_prexprojdoublen»
  "|- edwards_prexprojdoublen (f,a,d) (X1,Y1,Z1) =    (let X3,Y3,Z3,T3 = edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) in     ring_neg f X3,ring_neg f Y3,ring_neg f Z3,ring_neg f T3)"

-- FormularyProjective
#eval thm' "FormularyProjective.pr_dbl_2007_bl" SessionEC.FormularyProjective.«pr_dbl_2007_bl»
  "|- forall b y1 a z1 f x1.        pr_dbl_2007_bl (f,a,b) (x1,y1,z1) =        (let xx = ring_pow f x1 2 in         let zz = ring_pow f z1 2 in         let t0 = ring_mul f (ring_of_num f 3) xx in         let t1 = ring_mul f a zz in         let w = ring_add f t1 t0 in         let t2 = ring_mul f y1 z1 in         let s = ring_mul f (ring_of_num f 2) t2 in         let ss = ring_pow f s 2 in         let sss = ring_mul f s ss in         let r = ring_mul f y1 s in         let rr = ring_pow f r 2 in         let t3 = ring_add f x1 r in         let t4 = ring_pow f t3 2 in         let t5 = ring_sub f t4 xx in         let b = ring_sub f t5 rr in         let t6 = ring_pow f w 2 in         let t7 = ring_mul f (ring_of_num f 2) b in         let h = ring_sub f t6 t7 in         let x3 = ring_mul f h s in         let t8 = ring_sub f b h in         let t9 = ring_mul f (ring_of_num f 2) rr in         let t10 = ring_mul f w t8 in         let y3 = ring_sub f t10 t9 in let z3 = sss in x3,y3,z3)"
#eval thm' "FormularyProjective.PR_DBL_2007_BL" SessionEC.FormularyProjective.«PR_DBL_2007_BL»
  "|- forall f a b x1 y1 z1.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        projective_point f (x1,y1,z1)        ==> projective_eq f (pr_dbl_2007_bl (f,a,b) (x1,y1,z1))            (projective_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
#eval thm' "FormularyProjective.p3_dbl_2007_bl_2" SessionEC.FormularyProjective.«p3_dbl_2007_bl_2»
  "|- forall a b y1 f x1 z1.        p3_dbl_2007_bl_2 (f,a,b) (x1,y1,z1) =        (let t0 = ring_sub f x1 z1 in         let t1 = ring_add f x1 z1 in         let t2 = ring_mul f t0 t1 in         let w = ring_mul f (ring_of_num f 3) t2 in         let t3 = ring_mul f y1 z1 in         let s = ring_mul f (ring_of_num f 2) t3 in         let ss = ring_pow f s 2 in         let sss = ring_mul f s ss in         let r = ring_mul f y1 s in         let rr = ring_pow f r 2 in         let t4 = ring_mul f x1 r in         let b = ring_mul f (ring_of_num f 2) t4 in         let t5 = ring_pow f w 2 in         let t6 = ring_mul f (ring_of_num f 2) b in         let h = ring_sub f t5 t6 in         let x3 = ring_mul f h s in         let t7 = ring_sub f b h in         let t8 = ring_mul f (ring_of_num f 2) rr in         let t9 = ring_mul f w t7 in         let y3 = ring_sub f t9 t8 in let z3 = sss in x3,y3,z3)"
#eval thm' "FormularyProjective.P3_DBL_2007_BL_2" SessionEC.FormularyProjective.«P3_DBL_2007_BL_2»
  "|- forall f a b x1 y1 z1.        field f /\\        a = ring_of_int f (-- &3) /\\        b IN ring_carrier f /\\        projective_point f (x1,y1,z1)        ==> projective_eq f (p3_dbl_2007_bl_2 (f,a,b) (x1,y1,z1))            (projective_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
#eval thm' "FormularyProjective.p0_dbl_2007_bl" SessionEC.FormularyProjective.«p0_dbl_2007_bl»
  "|- forall a b y1 z1 f x1.        p0_dbl_2007_bl (f,a,b) (x1,y1,z1) =        (let xx = ring_pow f x1 2 in         let zz = ring_pow f z1 2 in         let w = ring_mul f (ring_of_num f 3) xx in         let t2 = ring_mul f y1 z1 in         let s = ring_mul f (ring_of_num f 2) t2 in         let ss = ring_pow f s 2 in         let sss = ring_mul f s ss in         let r = ring_mul f y1 s in         let rr = ring_pow f r 2 in         let t3 = ring_add f x1 r in         let t4 = ring_pow f t3 2 in         let t5 = ring_sub f t4 xx in         let b = ring_sub f t5 rr in         let t6 = ring_pow f w 2 in         let t7 = ring_mul f (ring_of_num f 2) b in         let h = ring_sub f t6 t7 in         let x3 = ring_mul f h s in         let t8 = ring_sub f b h in         let t9 = ring_mul f (ring_of_num f 2) rr in         let t10 = ring_mul f w t8 in         let y3 = ring_sub f t10 t9 in let z3 = sss in x3,y3,z3)"
#eval thm' "FormularyProjective.P0_DBL_2007_BL" SessionEC.FormularyProjective.«P0_DBL_2007_BL»
  "|- forall f a b x1 y1 z1.        field f /\\        a = ring_0 f /\\        b IN ring_carrier f /\\        projective_point f (x1,y1,z1)        ==> projective_eq f (p0_dbl_2007_bl (f,a,b) (x1,y1,z1))            (projective_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
#eval thm' "FormularyProjective.pr_add_1998_cmo_2" SessionEC.FormularyProjective.«pr_add_1998_cmo_2»
  "|- forall a b x2 y2 z1 x1 f y1 z2.        pr_add_1998_cmo_2 (f,a,b) (x1,y1,z1) (x2,y2,z2) =        (let y1z2 = ring_mul f y1 z2 in         let x1z2 = ring_mul f x1 z2 in         let z1z2 = ring_mul f z1 z2 in         let t0 = ring_mul f y2 z1 in         let u = ring_sub f t0 y1z2 in         let uu = ring_pow f u 2 in         let t1 = ring_mul f x2 z1 in         let v = ring_sub f t1 x1z2 in         let vv = ring_pow f v 2 in         let vvv = ring_mul f v vv in         let r = ring_mul f vv x1z2 in         let t2 = ring_mul f (ring_of_num f 2) r in         let t3 = ring_mul f uu z1z2 in         let t4 = ring_sub f t3 vvv in         let a = ring_sub f t4 t2 in         let x3 = ring_mul f v a in         let t5 = ring_sub f r a in         let t6 = ring_mul f vvv y1z2 in         let t7 = ring_mul f u t5 in         let y3 = ring_sub f t7 t6 in let z3 = ring_mul f vvv z1z2 in x3,y3,z3)"
#eval thm' "FormularyProjective.PR_ADD_1998_CMO_2" SessionEC.FormularyProjective.«PR_ADD_1998_CMO_2»
  "|- forall f a b x1 y1 z1 x2 y2 z2.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        projective_point f (x1,y1,z1) /\\        projective_point f (x2,y2,z2) /\\        ~(z1 = ring_0 f) /\\        ~(z2 = ring_0 f) /\\        ~projective_eq f (x1,y1,z1) (x2,y2,z2)        ==> projective_eq f (pr_add_1998_cmo_2 (f,a,b) (x1,y1,z1) (x2,y2,z2))            (projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2))"
#eval thm' "FormularyProjective.PR_MADD_1998_CMO" SessionEC.FormularyProjective.«PR_MADD_1998_CMO»
  "|- forall f a b x1 y1 z1 x2 y2 z2.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        projective_point f (x1,y1,z1) /\\        projective_point f (x2,y2,z2) /\\        z2 = ring_1 f /\\        ~(z1 = ring_0 f) /\\        ~projective_eq f (x1,y1,z1) (x2,y2,z2)        ==> projective_eq f (pr_madd_1998_cmo (f,a,b) (x1,y1,z1) (x2,y2,z2))            (projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2))"

-- FormularyJacobian
#eval thm' "FormularyJacobian.ja_dbl_2007_bl" SessionEC.FormularyJacobian.«ja_dbl_2007_bl»
  "|- forall b a z1 y1 f x1.        ja_dbl_2007_bl (f,a,b) (x1,y1,z1) =        (let xx = ring_pow f x1 2 in         let yy = ring_pow f y1 2 in         let yyyy = ring_pow f yy 2 in         let zz = ring_pow f z1 2 in         let t0 = ring_add f x1 yy in         let t1 = ring_pow f t0 2 in         let t2 = ring_sub f t1 xx in         let t3 = ring_sub f t2 yyyy in         let s = ring_mul f (ring_of_num f 2) t3 in         let t4 = ring_pow f zz 2 in         let t5 = ring_mul f a t4 in         let t6 = ring_mul f (ring_of_num f 3) xx in         let m = ring_add f t6 t5 in         let t7 = ring_pow f m 2 in         let t8 = ring_mul f (ring_of_num f 2) s in         let t = ring_sub f t7 t8 in         let x3 = t in         let t9 = ring_sub f s t in         let t10 = ring_mul f (ring_of_num f 8) yyyy in         let t11 = ring_mul f m t9 in         let y3 = ring_sub f t11 t10 in         let t12 = ring_add f y1 z1 in         let t13 = ring_pow f t12 2 in         let t14 = ring_sub f t13 yy in let z3 = ring_sub f t14 zz in x3,y3,z3)"
#eval thm' "FormularyJacobian.JA_DBL_2007_BL" SessionEC.FormularyJacobian.«JA_DBL_2007_BL»
  "|- forall f a b x1 y1 z1.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        jacobian_point f (x1,y1,z1)        ==> jacobian_eq f (ja_dbl_2007_bl (f,a,b) (x1,y1,z1))            (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
#eval thm' "FormularyJacobian.JA_DBL_2007_BL'" SessionEC.FormularyJacobian.«JA_DBL_2007_BL'»
  "|- forall f a b x1 y1 z1.        field f /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        jacobian_point f (x1,y1,z1) /\\        (z1 = ring_0 f ==> x1,y1,z1 = jacobian_0 (f,a,b))        ==> ja_dbl_2007_bl (f,a,b) (x1,y1,z1) =            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)"
#eval thm' "FormularyJacobian.j3_dbl_2001_b" SessionEC.FormularyJacobian.«j3_dbl_2001_b»
  "|- forall a b x1 y1 f z1.        j3_dbl_2001_b (f,a,b) (x1,y1,z1) =        (let delta = ring_pow f z1 2 in         let gamma = ring_pow f y1 2 in         let beta = ring_mul f x1 gamma in         let t0 = ring_sub f x1 delta in         let t1 = ring_add f x1 delta in         let t2 = ring_mul f t0 t1 in         let alpha = ring_mul f (ring_of_num f 3) t2 in         let t3 = ring_pow f alpha 2 in         let t4 = ring_mul f (ring_of_num f 8) beta in         let x3 = ring_sub f t3 t4 in         let t5 = ring_add f y1 z1 in         let t6 = ring_pow f t5 2 in         let t7 = ring_sub f t6 gamma in         let z3 = ring_sub f t7 delta in         let t8 = ring_mul f (ring_of_num f 4) beta in         let t9 = ring_sub f t8 x3 in         let t10 = ring_pow f gamma 2 in         let t11 = ring_mul f (ring_of_num f 8) t10 in         let t12 = ring_mul f alpha t9 in         let y3 = ring_sub f t12 t11 in x3,y3,z3)"
#eval thm' "FormularyJacobian.J3_DBL_2001_B" SessionEC.FormularyJacobian.«J3_DBL_2001_B»
  "|- forall f a b x1 y1 z1.        field f /\\        a = ring_of_int f (-- &3) /\\        b IN ring_carrier f /\\        jacobian_point f (x1,y1,z1)        ==> jacobian_eq f (j3_dbl_2001_b (f,a,b) (x1,y1,z1))            (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
#eval thm' "FormularyJacobian.J3_DBL_2001_B'" SessionEC.FormularyJacobian.«J3_DBL_2001_B'»
  "|- forall f a b x1 y1 z1.        field f /\\        a = ring_of_int f (-- &3) /\\        b IN ring_carrier f /\\        jacobian_point f (x1,y1,z1) /\\        (z1 = ring_0 f ==> x1,y1,z1 = jacobian_0 (f,a,b))        ==> j3_dbl_2001_b (f,a,b) (x1,y1,z1) =            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)"
#eval thm' "FormularyJacobian.j0_dbl_2009_l" SessionEC.FormularyJacobian.«j0_dbl_2009_l»
  "|- forall a b z1 y1 f x1.        j0_dbl_2009_l (f,a,b) (x1,y1,z1) =        (let a = ring_pow f x1 2 in         let b = ring_pow f y1 2 in         let c = ring_pow f b 2 in         let t0 = ring_add f x1 b in         let t1 = ring_pow f t0 2 in         let t2 = ring_sub f t1 a in         let t3 = ring_sub f t2 c in         let d = ring_mul f (ring_of_num f 2) t3 in         let e = ring_mul f (ring_of_num f 3) a in         let g = ring_pow f e 2 in         let t4 = ring_mul f (ring_of_num f 2) d in         let x3 = ring_sub f g t4 in         let t5 = ring_sub f d x3 in         let t6 = ring_mul f (ring_of_num f 8) c in         let t7 = ring_mul f e t5 in         let y3 = ring_sub f t7 t6 in         let t8 = ring_mul f y1 z1 in         let z3 = ring_mul f (ring_of_num f 2) t8 in x3,y3,z3)"
#eval thm' "FormularyJacobian.J0_DBL_2009_L" SessionEC.FormularyJacobian.«J0_DBL_2009_L»
  "|- forall f a b x1 y1 z1.        field f /\\        a = ring_0 f /\\        b IN ring_carrier f /\\        jacobian_point f (x1,y1,z1)        ==> jacobian_eq f (j0_dbl_2009_l (f,a,b) (x1,y1,z1))            (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
#eval thm' "FormularyJacobian.J0_DBL_2009_L'" SessionEC.FormularyJacobian.«J0_DBL_2009_L'»
  "|- forall f a b x1 y1 z1.        field f /\\        a = ring_0 f /\\        b IN ring_carrier f /\\        jacobian_point f (x1,y1,z1) /\\        (z1 = ring_0 f ==> x1,y1,z1 = jacobian_0 (f,a,b))        ==> j0_dbl_2009_l (f,a,b) (x1,y1,z1) =            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)"
#eval thm' "FormularyJacobian.ja_add_2007_bl" SessionEC.FormularyJacobian.«ja_add_2007_bl»
  "|- forall a b y2 y1 x2 x1 z2 f z1.        ja_add_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2) =        (let z1z1 = ring_pow f z1 2 in         let z2z2 = ring_pow f z2 2 in         let u1 = ring_mul f x1 z2z2 in         let u2 = ring_mul f x2 z1z1 in         let t0 = ring_mul f z2 z2z2 in         let s1 = ring_mul f y1 t0 in         let t1 = ring_mul f z1 z1z1 in         let s2 = ring_mul f y2 t1 in         let h = ring_sub f u2 u1 in         let t2 = ring_mul f (ring_of_num f 2) h in         let i = ring_pow f t2 2 in         let j = ring_mul f h i in         let t3 = ring_sub f s2 s1 in         let r = ring_mul f (ring_of_num f 2) t3 in         let v = ring_mul f u1 i in         let t4 = ring_pow f r 2 in         let t5 = ring_mul f (ring_of_num f 2) v in         let t6 = ring_sub f t4 j in         let x3 = ring_sub f t6 t5 in         let t7 = ring_sub f v x3 in         let t8 = ring_mul f s1 j in         let t9 = ring_mul f (ring_of_num f 2) t8 in         let t10 = ring_mul f r t7 in         let y3 = ring_sub f t10 t9 in         let t11 = ring_add f z1 z2 in         let t12 = ring_pow f t11 2 in         let t13 = ring_sub f t12 z1z1 in         let t14 = ring_sub f t13 z2z2 in         let z3 = ring_mul f t14 h in x3,y3,z3)"
#eval thm' "FormularyJacobian.JA_ADD_2007_BL" SessionEC.FormularyJacobian.«JA_ADD_2007_BL»
  "|- forall f a b x1 y1 z1 x2 y2 z2.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        jacobian_point f (x1,y1,z1) /\\        jacobian_point f (x2,y2,z2) /\\        ~(z1 = ring_0 f) /\\        ~(z2 = ring_0 f) /\\        ~jacobian_eq f (x1,y1,z1) (x2,y2,z2)        ==> jacobian_eq f (ja_add_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2))            (jacobian_add (f,a,b) (x1,y1,z1) (x2,y2,z2))"
#eval thm' "FormularyJacobian.JA_MADD_2007_BL" SessionEC.FormularyJacobian.«JA_MADD_2007_BL»
  "|- forall f a b x1 y1 z1 x2 y2 z2.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        jacobian_point f (x1,y1,z1) /\\        jacobian_point f (x2,y2,z2) /\\        z2 = ring_1 f /\\        ~(z1 = ring_0 f) /\\        ~jacobian_eq f (x1,y1,z1) (x2,y2,z2)        ==> jacobian_eq f (ja_madd_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2))            (jacobian_add (f,a,b) (x1,y1,z1) (x2,y2,z2))"

-- Edmont
#eval thm' "Edmont.mcurve_of_ecurve" SessionEC.Edmont.«mcurve_of_ecurve»
  "|- mcurve_of_ecurve (f,a,d) c =    f,    ring_div f (ring_mul f (ring_of_num f 2) (ring_add f a d))    (ring_sub f a d),    ring_div f (ring_div f (ring_of_num f 4) (ring_sub f a d))    (ring_pow f c 2)"
#eval thm' "Edmont.montgomery_of_edwards" SessionEC.Edmont.«montgomery_of_edwards»
  "|- montgomery_of_edwards f c (x,y) =    (if x,y = ring_0 f,ring_1 f     then NONE     else if x,y = ring_0 f,ring_neg f (ring_1 f)          then SOME (ring_0 f,ring_0 f)          else SOME               (ring_div f (ring_add f (ring_1 f) y) (ring_sub f (ring_1 f) y),                ring_mul f c                (ring_div f (ring_add f (ring_1 f) y)                (ring_mul f x (ring_sub f (ring_1 f) y)))))"
#eval thm' "Edmont.edwards_of_montgomery" SessionEC.Edmont.«edwards_of_montgomery»
  "|- edwards_of_montgomery f c NONE = ring_0 f,ring_1 f /\\    edwards_of_montgomery f c (SOME (x,y)) =    (if x,y = ring_0 f,ring_0 f     then ring_0 f,ring_neg f (ring_1 f)     else ring_mul f c (ring_div f x y),          ring_div f (ring_sub f x (ring_of_num f 1))          (ring_add f x (ring_of_num f 1)))"
#eval thm' "Edmont.MCURVE_OF_ECURVE_OF_MCURVE" SessionEC.Edmont.«MCURVE_OF_ECURVE_OF_MCURVE»
  "|- forall f A B c.        field f /\\        ~(ring_char f = 2) /\\        A IN ring_carrier f /\\        B IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(c = ring_0 f) /\\        ~(B = ring_0 f)        ==> mcurve_of_ecurve (ecurve_of_mcurve (f,A,B) c) c = f,A,B"
#eval thm' "Edmont.MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ" SessionEC.Edmont.«MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ»
  "|- forall f a d c.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(c = ring_0 f)        ==> (montgomery_strongly_nonsingular (mcurve_of_ecurve (f,a,d) c) <=>             ~(exists z.                   z IN ring_carrier f /\\ ring_pow f z 2 = ring_mul f a d))"
#eval thm' "Edmont.MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR" SessionEC.Edmont.«MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR»
  "|- forall f a d c.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(c = ring_0 f) /\\        ~(a = ring_0 f) /\\        ~(d = ring_0 f) /\\        edwards_nonsingular (f,a,d)        ==> montgomery_strongly_nonsingular (mcurve_of_ecurve (f,a,d) c)"
#eval thm' "Edmont.MONTGOMERY_OF_EDWARDS" SessionEC.Edmont.«MONTGOMERY_OF_EDWARDS»
  "|- forall f a d c p.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(a = d) /\\        ~(c = ring_0 f) /\\        edwards_curve (f,a,d) p        ==> montgomery_curve (mcurve_of_ecurve (f,a,d) c)            (montgomery_of_edwards f c p)"
#eval thm' "Edmont.EDWARDS_OF_MONTGOMERY_OF_EDWARDS" SessionEC.Edmont.«EDWARDS_OF_MONTGOMERY_OF_EDWARDS»
  "|- forall f a d c p.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(a = d) /\\        ~(c = ring_0 f) /\\        edwards_curve (f,a,d) p        ==> edwards_of_montgomery f c (montgomery_of_edwards f c p) = p"
#eval thm' "Edmont.MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY" SessionEC.Edmont.«MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY»
  "|- forall f A B c p.        field f /\\        ~(ring_char f = 2) /\\        A IN ring_carrier f /\\        B IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(B = ring_0 f) /\\        ~(c = ring_0 f) /\\        montgomery_strongly_nonsingular (f,A,B) /\\        edwards_nonsingular (ecurve_of_mcurve (f,A,B) c) /\\        montgomery_curve (f,A,B) p        ==> montgomery_of_edwards f c (edwards_of_montgomery f c p) = p"
#eval thm' "Edmont.GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP" SessionEC.Edmont.«GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP»
  "|- forall f a d c.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(a = d) /\\        ~(a = ring_0 f) /\\        ~(d = ring_0 f) /\\        ~(c = ring_0 f) /\\        edwards_nonsingular (f,a,d)        ==> group_isomorphisms            (edwards_group (f,a,d),             montgomery_group (mcurve_of_ecurve (f,a,d) c))            (montgomery_of_edwards f c,edwards_of_montgomery f c)"
#eval thm' "Edmont.MONTGOMERY_OF_EDWARDS_ADD" SessionEC.Edmont.«MONTGOMERY_OF_EDWARDS_ADD»
  "|- forall f a d c p q.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(a = d) /\\        ~(a = ring_0 f) /\\        ~(d = ring_0 f) /\\        ~(c = ring_0 f) /\\        edwards_nonsingular (f,a,d) /\\        edwards_curve (f,a,d) p /\\        edwards_curve (f,a,d) q        ==> montgomery_of_edwards f c (edwards_add (f,a,d) p q) =            montgomery_add (mcurve_of_ecurve (f,a,d) c)            (montgomery_of_edwards f c p)            (montgomery_of_edwards f c q)"
#eval thm' "Edmont.ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP" SessionEC.Edmont.«ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP»
  "|- forall f a d c.        field f /\\        ~(ring_char f = 2) /\\        a IN ring_carrier f /\\        d IN ring_carrier f /\\        c IN ring_carrier f /\\        ~(a = d) /\\        ~(a = ring_0 f) /\\        ~(d = ring_0 f) /\\        ~(c = ring_0 f) /\\        edwards_nonsingular (f,a,d)        ==> edwards_group (f,a,d) isomorphic_group            montgomery_group (mcurve_of_ecurve (f,a,d) c)"

-- Montwe
#eval thm' "Montwe.wcurve_of_mcurve" SessionEC.Montwe.«wcurve_of_mcurve»
  "|- wcurve_of_mcurve (f,a,b) =    f,    ring_div f    (ring_sub f (ring_of_num f 1)    (ring_div f (ring_pow f a 2) (ring_of_num f 3)))    (ring_pow f b 2),    ring_div f    (ring_mul f a    (ring_sub f (ring_mul f (ring_of_num f 2) (ring_pow f a 2))    (ring_of_num f 9)))    (ring_mul f (ring_of_num f 27) (ring_pow f b 3))"
#eval thm' "Montwe.WCURVE_OF_MCURVE_NONSINGULAR_EQ" SessionEC.Montwe.«WCURVE_OF_MCURVE_NONSINGULAR_EQ»
  "|- forall f a b.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        ~(b = ring_0 f)        ==> (weierstrass_nonsingular (wcurve_of_mcurve (f,a,b)) <=>             ~(ring_pow f a 2 = ring_of_num f 4))"
#eval thm' "Montwe.WCURVE_OF_MCURVE_NONSINGULAR" SessionEC.Montwe.«WCURVE_OF_MCURVE_NONSINGULAR»
  "|- forall f a b.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b)        ==> weierstrass_nonsingular (wcurve_of_mcurve (f,a,b))"
#eval thm' "Montwe.weierstrass_of_montgomery" SessionEC.Montwe.«weierstrass_of_montgomery»
  "|- weierstrass_of_montgomery (f,a,b) NONE = NONE /\\    weierstrass_of_montgomery (f,a,b) (SOME (x,y)) =    SOME    (ring_div f (ring_add f x (ring_div f a (ring_of_num f 3))) b,     ring_div f y b)"
#eval thm' "Montwe.MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY" SessionEC.Montwe.«MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY»
  "|- forall f a b p.        field f /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        ~(b = ring_0 f) /\\        montgomery_point f p        ==> montgomery_of_weierstrass (f,a,b)            (weierstrass_of_montgomery (f,a,b) p) =            p"
#eval thm' "Montwe.WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS" SessionEC.Montwe.«WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS»
  "|- forall f a b p.        field f /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        ~(b = ring_0 f) /\\        weierstrass_point f p        ==> weierstrass_of_montgomery (f,a,b)            (montgomery_of_weierstrass (f,a,b) p) =            p"
#eval thm' "Montwe.WEIERSTRASS_OF_MONTGOMERY" SessionEC.Montwe.«WEIERSTRASS_OF_MONTGOMERY»
  "|- forall f a b p.        field f /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_curve (f,a,b) p        ==> weierstrass_curve (wcurve_of_mcurve (f,a,b))            (weierstrass_of_montgomery (f,a,b) p)"
#eval thm' "Montwe.MONTGOMERY_OF_WEIERSTRASS" SessionEC.Montwe.«MONTGOMERY_OF_WEIERSTRASS»
  "|- forall f a b p.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        ~(b = ring_0 f) /\\        weierstrass_curve (wcurve_of_mcurve (f,a,b)) p        ==> montgomery_curve (f,a,b) (montgomery_of_weierstrass (f,a,b) p)"
#eval thm' "Montwe.WEIERSTRASS_OF_MONTGOMERY_ADD" SessionEC.Montwe.«WEIERSTRASS_OF_MONTGOMERY_ADD»
  "|- forall f a b p q.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        ~(b = ring_0 f) /\\        montgomery_curve (f,a,b) p /\\        montgomery_curve (f,a,b) q        ==> weierstrass_of_montgomery (f,a,b) (montgomery_add (f,a,b) p q) =            weierstrass_add (wcurve_of_mcurve (f,a,b))            (weierstrass_of_montgomery (f,a,b) p)            (weierstrass_of_montgomery (f,a,b) q)"
#eval thm' "Montwe.GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP" SessionEC.Montwe.«GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP»
  "|- forall f a b.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b)        ==> group_isomorphisms            (montgomery_group (f,a,b),             weierstrass_group (wcurve_of_mcurve (f,a,b)))            (weierstrass_of_montgomery (f,a,b),             montgomery_of_weierstrass (f,a,b))"
#eval thm' "Montwe.GROUP_ISOMORPHISMS_WEIERSTRASS_MONTGOMERY_GROUP" SessionEC.Montwe.«GROUP_ISOMORPHISMS_WEIERSTRASS_MONTGOMERY_GROUP»
  "|- forall f a b.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b)        ==> group_isomorphisms            (weierstrass_group (wcurve_of_mcurve (f,a,b)),             montgomery_group (f,a,b))            (montgomery_of_weierstrass (f,a,b),             weierstrass_of_montgomery (f,a,b))"
#eval thm' "Montwe.ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP" SessionEC.Montwe.«ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP»
  "|- forall f a b.        field f /\\        ~(ring_char f = 2) /\\        ~(ring_char f = 3) /\\        a IN ring_carrier f /\\        b IN ring_carrier f /\\        montgomery_nonsingular (f,a,b)        ==> montgomery_group (f,a,b) isomorphic_group            weierstrass_group (wcurve_of_mcurve (f,a,b))"

end T
