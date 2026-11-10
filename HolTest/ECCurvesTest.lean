/- File: HolTest/ECCurvesTest.lean
Runtime test suite: EC/excluderoots.ml, EC/computegroup.ml, EC/nistp192.ml, EC/nistp224.ml, EC/nistp256.ml, EC/nistp384.ml, EC/nistp521.ml, EC/secp192k1.ml, EC/secp224k1.ml, EC/secp256k1.ml, EC/ccsm2.ml, EC/edwards25519.ml, EC/curve25519.ml, EC/wei25519.ml, EC/family25519.ml, EC/x25519.ml, EC/edwards448.ml
(HolEC/, wired by SessionEC/).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "EC/<file>.ml"`, then `string_of_thm`, newlines joined).
tools/ec<file>diff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here.  The files are
in one test module so that each SessionEC module replays once. -/

import HolTest.CommonTest
import SessionEC.ExcludeRoots
import SessionEC.ComputeGroup
import SessionEC.NistP192
import SessionEC.NistP224
import SessionEC.NistP256
import SessionEC.NistP384
import SessionEC.NistP521
import SessionEC.Secp192k1
import SessionEC.Secp224k1
import SessionEC.Secp256k1
import SessionEC.CCSM2
import SessionEC.Edwards25519
import SessionEC.Curve25519
import SessionEC.Wei25519
import SessionEC.Family25519
import SessionEC.X25519
import SessionEC.Edwards448

open HolCore.Kernel HolTest.CommonTest

#eval SessionEC.ExcludeRoots.ensureExcludeRoots
#eval SessionEC.ComputeGroup.ensureComputeGroup
#eval SessionEC.NistP192.ensureNistP192
#eval SessionEC.NistP224.ensureNistP224
#eval SessionEC.NistP256.ensureNistP256
#eval SessionEC.NistP384.ensureNistP384
#eval SessionEC.NistP521.ensureNistP521
#eval SessionEC.Secp192k1.ensureSecp192k1
#eval SessionEC.Secp224k1.ensureSecp224k1
#eval SessionEC.Secp256k1.ensureSecp256k1
#eval SessionEC.CCSM2.ensureCCSM2
#eval SessionEC.Edwards25519.ensureEdwards25519
#eval SessionEC.Curve25519.ensureCurve25519
#eval SessionEC.Wei25519.ensureWei25519
#eval SessionEC.Family25519.ensureFamily25519
#eval SessionEC.X25519.ensureX25519
#eval SessionEC.Edwards448.ensureEdwards448

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

-- ExcludeRoots

-- ComputeGroup

-- NistP192
#eval thm' "NistP192.p_192" SessionEC.NistP192.«p_192»
  "|- p_192 = 6277101735386680763835789423207666416083908700390324961279"
#eval thm' "NistP192.c_192" SessionEC.NistP192.«c_192»
  "|- c_192 = 1191689908718309326471930603292001425137626342642504031845"
#eval thm' "NistP192.PRIME_P192" SessionEC.NistP192.«PRIME_P192»
  "|- prime p_192"
#eval thm' "NistP192.P192_GROUP" SessionEC.NistP192.«P192_GROUP»
  "|- group_carrier p192_group =    weierstrass_curve    (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192) /\\    group_id p192_group = NONE /\\    group_inv p192_group =    weierstrass_neg    (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192) /\\    group_mul p192_group =    weierstrass_add    (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192)"
#eval thm' "NistP192.GROUP_ELEMENT_ORDER_G192" SessionEC.NistP192.«GROUP_ELEMENT_ORDER_G192»
  "|- group_element_order p192_group G_192 = n_192"
#eval thm' "NistP192.P192_GROUP_ELEMENT_ORDER" SessionEC.NistP192.«P192_GROUP_ELEMENT_ORDER»
  "|- forall P.        P IN group_carrier p192_group        ==> group_element_order p192_group P =            (if P = group_id p192_group then 1 else n_192)"

-- NistP224
#eval thm' "NistP224.p_224" SessionEC.NistP224.«p_224»
  "|- p_224 =    26959946667150639794667015087019630673557916260026308143510066298881"
#eval thm' "NistP224.c_224" SessionEC.NistP224.«c_224»
  "|- c_224 =    9585649763196999776159690989286240671136085803543320687376622326267"
#eval thm' "NistP224.PRIME_P224" SessionEC.NistP224.«PRIME_P224»
  "|- prime p_224"
#eval thm' "NistP224.P224_GROUP" SessionEC.NistP224.«P224_GROUP»
  "|- group_carrier p224_group =    weierstrass_curve    (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224) /\\    group_id p224_group = NONE /\\    group_inv p224_group =    weierstrass_neg    (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224) /\\    group_mul p224_group =    weierstrass_add    (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224)"
#eval thm' "NistP224.GROUP_ELEMENT_ORDER_G224" SessionEC.NistP224.«GROUP_ELEMENT_ORDER_G224»
  "|- group_element_order p224_group G_224 = n_224"
#eval thm' "NistP224.P224_GROUP_ELEMENT_ORDER" SessionEC.NistP224.«P224_GROUP_ELEMENT_ORDER»
  "|- forall P.        P IN group_carrier p224_group        ==> group_element_order p224_group P =            (if P = group_id p224_group then 1 else n_224)"

-- NistP256
#eval thm' "NistP256.p_256" SessionEC.NistP256.«p_256»
  "|- p_256 =    115792089210356248762697446949407573530086143415290314195533631308867097853951"
#eval thm' "NistP256.c_256" SessionEC.NistP256.«c_256»
  "|- c_256 =    57436011470200155964173534038266061871440426244159038175955947309464595790349"
#eval thm' "NistP256.P_256" SessionEC.NistP256.«P_256»
  "|- p_256 = 2 EXP 256 - 2 EXP 224 + 2 EXP 192 + 2 EXP 96 - 1"
#eval thm' "NistP256.p256_group" SessionEC.NistP256.«p256_group»
  "|- p256_group =    weierstrass_group    (integer_mod_ring p_256,ring_neg (integer_mod_ring p_256) (&3),&b_256)"
#eval thm' "NistP256.GROUP_ELEMENT_ORDER_G256" SessionEC.NistP256.«GROUP_ELEMENT_ORDER_G256»
  "|- group_element_order p256_group G_256 = n_256"
#eval thm' "NistP256.P256_GROUP_ELEMENT_ORDER" SessionEC.NistP256.«P256_GROUP_ELEMENT_ORDER»
  "|- forall P.        P IN group_carrier p256_group        ==> group_element_order p256_group P =            (if P = group_id p256_group then 1 else n_256)"

-- NistP384
#eval thm' "NistP384.p_384" SessionEC.NistP384.«p_384»
  "|- p_384 =    39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319"
#eval thm' "NistP384.c_384" SessionEC.NistP384.«c_384»
  "|- c_384 =    18749801867098873471821070971353888788690339003065439021780101954060871745882341382251168574711376101826101037376643"
#eval thm' "NistP384.P_384" SessionEC.NistP384.«P_384»
  "|- p_384 = 2 EXP 384 - 2 EXP 128 - 2 EXP 96 + 2 EXP 32 - 1"
#eval thm' "NistP384.p384_group" SessionEC.NistP384.«p384_group»
  "|- p384_group =    weierstrass_group    (integer_mod_ring p_384,ring_neg (integer_mod_ring p_384) (&3),&b_384)"
#eval thm' "NistP384.GROUP_ELEMENT_ORDER_G384" SessionEC.NistP384.«GROUP_ELEMENT_ORDER_G384»
  "|- group_element_order p384_group G_384 = n_384"
#eval thm' "NistP384.P384_GROUP_ELEMENT_ORDER" SessionEC.NistP384.«P384_GROUP_ELEMENT_ORDER»
  "|- forall P.        P IN group_carrier p384_group        ==> group_element_order p384_group P =            (if P = group_id p384_group then 1 else n_384)"

-- NistP521
#eval thm' "NistP521.p_521" SessionEC.NistP521.«p_521»
  "|- p_521 =    6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151"
#eval thm' "NistP521.c_521" SessionEC.NistP521.«c_521»
  "|- c_521 =    2420736670956961470587751833778383872272949280174637971106318223956010636355557333899035866342650378575221277268886182704643828850020061383251826928984446519"
#eval thm' "NistP521.P_521" SessionEC.NistP521.«P_521»
  "|- p_521 = 2 EXP 521 - 1"
#eval thm' "NistP521.p521_group" SessionEC.NistP521.«p521_group»
  "|- p521_group =    weierstrass_group    (integer_mod_ring p_521,ring_neg (integer_mod_ring p_521) (&3),&b_521)"
#eval thm' "NistP521.GROUP_ELEMENT_ORDER_G521" SessionEC.NistP521.«GROUP_ELEMENT_ORDER_G521»
  "|- group_element_order p521_group G_521 = n_521"
#eval thm' "NistP521.P521_GROUP_ELEMENT_ORDER" SessionEC.NistP521.«P521_GROUP_ELEMENT_ORDER»
  "|- forall P.        P IN group_carrier p521_group        ==> group_element_order p521_group P =            (if P = group_id p521_group then 1 else n_521)"

-- Secp192k1
#eval thm' "Secp192k1.p_192k1" SessionEC.Secp192k1.«p_192k1»
  "|- p_192k1 = 6277101735386680763835789423207666416102355444459739541047"
#eval thm' "Secp192k1.P_192K1" SessionEC.Secp192k1.«P_192K1»
  "|- p_192k1 = 2 EXP 192 - 2 EXP 32 - 4553"
#eval thm' "Secp192k1.PRIME_N192K1" SessionEC.Secp192k1.«PRIME_N192K1»
  "|- prime n_192k1"
#eval thm' "Secp192k1.NO_ROOTS_192K1" SessionEC.Secp192k1.«NO_ROOTS_192K1»
  "|- forall x. ~(x pow 3 + &3 == &0) (mod &p_192k1)"
#eval thm' "Secp192k1.FINITE_GROUP_CARRIER_P192K1" SessionEC.Secp192k1.«FINITE_GROUP_CARRIER_P192K1»
  "|- FINITE (group_carrier p192k1_group)"
#eval thm' "Secp192k1.P192K1_GROUP_ELEMENT_ORDER" SessionEC.Secp192k1.«P192K1_GROUP_ELEMENT_ORDER»
  "|- forall P.        P IN group_carrier p192k1_group        ==> group_element_order p192k1_group P =            (if P = group_id p192k1_group then 1 else n_192k1)"

-- Secp224k1
#eval thm' "Secp224k1.p_224k1" SessionEC.Secp224k1.«p_224k1»
  "|- p_224k1 =    26959946667150639794667015087019630673637144422540572481099315275117"
#eval thm' "Secp224k1.P_224K1" SessionEC.Secp224k1.«P_224K1»
  "|- p_224k1 = 2 EXP 224 - 2 EXP 32 - 6803"
#eval thm' "Secp224k1.PRIME_N224K1" SessionEC.Secp224k1.«PRIME_N224K1»
  "|- prime n_224k1"
#eval thm' "Secp224k1.NO_ROOTS_224K1" SessionEC.Secp224k1.«NO_ROOTS_224K1»
  "|- forall x. ~(x pow 3 + &5 == &0) (mod &p_224k1)"
#eval thm' "Secp224k1.FINITE_GROUP_CARRIER_P224K1" SessionEC.Secp224k1.«FINITE_GROUP_CARRIER_P224K1»
  "|- FINITE (group_carrier p224k1_group)"
#eval thm' "Secp224k1.P224K1_GROUP_ELEMENT_ORDER" SessionEC.Secp224k1.«P224K1_GROUP_ELEMENT_ORDER»
  "|- forall P.        P IN group_carrier p224k1_group        ==> group_element_order p224k1_group P =            (if P = group_id p224k1_group then 1 else n_224k1)"

-- Secp256k1
#eval thm' "Secp256k1.p_256k1" SessionEC.Secp256k1.«p_256k1»
  "|- p_256k1 =    115792089237316195423570985008687907853269984665640564039457584007908834671663"
#eval thm' "Secp256k1.p256k1_beta" SessionEC.Secp256k1.«p256k1_beta»
  "|- p256k1_beta =    55594575648329892869085402983802832744385952214688224221778511981742606582254"
#eval thm' "Secp256k1.PRIME_P256K1" SessionEC.Secp256k1.«PRIME_P256K1»
  "|- prime p_256k1"
#eval thm' "Secp256k1.NO_ROOTS_256K1" SessionEC.Secp256k1.«NO_ROOTS_256K1»
  "|- forall x. ~(x pow 3 + &7 == &0) (mod &p_256k1)"
#eval thm' "Secp256k1.SIZE_P256K1_GROUP" SessionEC.Secp256k1.«SIZE_P256K1_GROUP»
  "|- group_carrier p256k1_group HAS_SIZE n_256k1"
#eval thm' "Secp256k1.CYCLIC_P256K1_GROUP" SessionEC.Secp256k1.«CYCLIC_P256K1_GROUP»
  "|- cyclic_group p256k1_group"

-- CCSM2
#eval thm' "CCSM2.p_sm2" SessionEC.CCSM2.«p_sm2»
  "|- p_sm2 =    115792089210356248756420345214020892766250353991924191454421193933289684991999"
#eval thm' "CCSM2.g_sm2" SessionEC.CCSM2.«g_sm2»
  "|- g_sm2 =    SOME    (&22963146547237050559479531362550074578802567295341616970375194840604139615431,     &85132369209828568825618990617112496413088388631904505083283536607588877201568)"
#eval thm' "CCSM2.PRIME_PSM2" SessionEC.CCSM2.«PRIME_PSM2»
  "|- prime p_sm2"
#eval thm' "CCSM2.NO_ROOTS_SM2" SessionEC.CCSM2.«NO_ROOTS_SM2»
  "|- forall x. ~(x pow 3 - &3 * x + &b_sm2 == &0) (mod &p_sm2)"
#eval thm' "CCSM2.FINITE_GROUP_CARRIER_SM2" SessionEC.CCSM2.«FINITE_GROUP_CARRIER_SM2»
  "|- FINITE (group_carrier sm2_group)"
#eval thm' "CCSM2.SM2_GROUP_ELEMENT_ORDER" SessionEC.CCSM2.«SM2_GROUP_ELEMENT_ORDER»
  "|- forall P.        P IN group_carrier sm2_group        ==> group_element_order sm2_group P =            (if P = group_id sm2_group then 1 else n_sm2)"

-- Edwards25519
#eval thm' "Edwards25519.p_25519" SessionEC.Edwards25519.«p_25519»
  "|- p_25519 =    57896044618658097711785492504343953926634992332820282019728792003956564819949"
#eval thm' "Edwards25519.d_25519" SessionEC.Edwards25519.«d_25519»
  "|- d_25519 =    37095705934669439343138083508754565189542113879843219016388785533085940283555"
#eval thm' "Edwards25519.P_25519" SessionEC.Edwards25519.«P_25519»
  "|- p_25519 = 2 EXP 255 - 19"
#eval thm' "Edwards25519.edwards25519_group" SessionEC.Edwards25519.«edwards25519_group»
  "|- edwards25519_group =    edwards_group (integer_mod_ring p_25519,&e_25519,&d_25519)"
#eval thm' "Edwards25519.GENERATOR_IN_GROUP_CARRIER_EDWARDS25519" SessionEC.Edwards25519.«GENERATOR_IN_GROUP_CARRIER_EDWARDS25519»
  "|- E_25519 IN group_carrier edwards25519_group"
#eval thm' "Edwards25519.SIZE_EDWARDS25519_GROUP" SessionEC.Edwards25519.«SIZE_EDWARDS25519_GROUP»
  "|- group_carrier edwards25519_group HAS_SIZE 8 * n_25519"

-- Curve25519
#eval thm' "Curve25519.p_25519" SessionEC.Curve25519.«p_25519»
  "|- p_25519 =    57896044618658097711785492504343953926634992332820282019728792003956564819949"
#eval thm' "Curve25519.C_25519" SessionEC.Curve25519.«C_25519»
  "|- C_25519 =    SOME    (&9,     &14781619447589544791020593568409986887264606134616475288964881837755586237401)"
#eval thm' "Curve25519.N_25519" SessionEC.Curve25519.«N_25519»
  "|- n_25519 = 2 EXP 252 + 27742317777372353535851937790883648493"
#eval thm' "Curve25519.MONTGOMERY_NONSINGULAR_CURVE25519" SessionEC.Curve25519.«MONTGOMERY_NONSINGULAR_CURVE25519»
  "|- montgomery_nonsingular curve25519"
#eval thm' "Curve25519.GENERATOR_IN_GROUP_CARRIER_CURVE25519" SessionEC.Curve25519.«GENERATOR_IN_GROUP_CARRIER_CURVE25519»
  "|- C_25519 IN group_carrier curve25519_group"
#eval thm' "Curve25519.SIZE_CURVE25519_GROUP" SessionEC.Curve25519.«SIZE_CURVE25519_GROUP»
  "|- group_carrier curve25519_group HAS_SIZE 8 * n_25519"

-- Wei25519
#eval thm' "Wei25519.p_25519" SessionEC.Wei25519.«p_25519»
  "|- p_25519 =    57896044618658097711785492504343953926634992332820282019728792003956564819949"
#eval thm' "Wei25519.b_25519" SessionEC.Wei25519.«b_25519»
  "|- b_25519 =    55751746669818908907645289078257140818241103727901012315294400837956729358436"
#eval thm' "Wei25519.N_25519" SessionEC.Wei25519.«N_25519»
  "|- n_25519 = 2 EXP 252 + 27742317777372353535851937790883648493"
#eval thm' "Wei25519.wei25519_group" SessionEC.Wei25519.«wei25519_group»
  "|- wei25519_group =    weierstrass_group (integer_mod_ring p_25519,&a_25519,&b_25519)"
#eval thm' "Wei25519.GROUP_ELEMENT_ORDER_WEI25519_G25519" SessionEC.Wei25519.«GROUP_ELEMENT_ORDER_WEI25519_G25519»
  "|- group_element_order wei25519_group G_25519 = n_25519"
#eval thm' "Wei25519.SIZE_WEI25519_GROUP" SessionEC.Wei25519.«SIZE_WEI25519_GROUP»
  "|- group_carrier wei25519_group HAS_SIZE 8 * n_25519"

-- Family25519
#eval thm' "Family25519.c_25519" SessionEC.Family25519.«c_25519»
  "|- c_25519 =    51042569399160536130206135233146329284152202253034631822681833788666877215207"
#eval thm' "Family25519.MCURVE_OF_ECURVE_25519" SessionEC.Family25519.«MCURVE_OF_ECURVE_25519»
  "|- mcurve_of_ecurve (integer_mod_ring p_25519,&e_25519,&d_25519) (&c_25519) =    integer_mod_ring p_25519,&A_25519,&1"
#eval thm' "Family25519.CURVE25519_OF_EDWARDS25519_E25519" SessionEC.Family25519.«CURVE25519_OF_EDWARDS25519_E25519»
  "|- curve25519_of_edwards25519 E_25519 = C_25519"
#eval thm' "Family25519.EDWARDS25519_OF_CURVE25519_CC25519" SessionEC.Family25519.«EDWARDS25519_OF_CURVE25519_CC25519»
  "|- edwards25519_of_curve25519 CC_25519 = EE_25519"
#eval thm' "Family25519.GROUP_ISOMORPHISMS_CURVE25519_WEI25519" SessionEC.Family25519.«GROUP_ISOMORPHISMS_CURVE25519_WEI25519»
  "|- group_isomorphisms (curve25519_group,wei25519_group)    (wei25519_of_curve25519,curve25519_of_wei25519)"
#eval thm' "Family25519.WEI25519_OF_CURVE25519_C25519" SessionEC.Family25519.«WEI25519_OF_CURVE25519_C25519»
  "|- wei25519_of_curve25519 C_25519 = G_25519"

-- X25519
#eval thm' "X25519.curve25519x" SessionEC.X25519.«curve25519x»
  "|- curve25519x f = f,ring_of_num f A_25519,ring_of_num f 1"
#eval thm' "X25519.curve25519x_group" SessionEC.X25519.«curve25519x_group»
  "|- curve25519x_group f = montgomery_group (curve25519x f)"
#eval thm' "X25519.QUADRATIC_EXTENSION" SessionEC.X25519.«QUADRATIC_EXTENSION»
  "|- (forall r a.         ring_carrier (quadratic_extension r a) =         ring_carrier r CROSS ring_carrier r) /\\    (forall r a. ring_0 (quadratic_extension r a) = ring_0 r,ring_0 r) /\\    (forall r a. ring_1 (quadratic_extension r a) = ring_1 r,ring_0 r) /\\    (forall r a.         ring_neg (quadratic_extension r a) =         (\\(x,y). ring_neg r x,ring_neg r y)) /\\    (forall r a.         ring_add (quadratic_extension r a) =         (\\(x1,y1) (x2,y2). ring_add r x1 x2,ring_add r y1 y2)) /\\    (forall r a.         ring_mul (quadratic_extension r a) =         (\\(x1,y1) (x2,y2).              ring_add r (ring_mul r x1 x2)              (ring_mul r (ring_of_num r a) (ring_mul r y1 y2)),              ring_add r (ring_mul r x1 y2) (ring_mul r x2 y1)))"
#eval thm' "X25519.FIELD_QUADRATIC_EXTENSION" SessionEC.X25519.«FIELD_QUADRATIC_EXTENSION»
  "|- forall r a.        field r /\\        (forall d.             d IN ring_carrier r ==> ~(ring_pow r d 2 = ring_of_num r a))        ==> field (quadratic_extension r a)"
#eval thm' "X25519.x25519_ladder" SessionEC.X25519.«x25519_ladder»
  "|- x25519_ladder n P =    (if n = 0     then (&1,&0),P     else x25519_ladderstep (n MOD 2 = 1) P (x25519_ladder (n DIV 2) P))"
#eval thm' "X25519.purex25519" SessionEC.X25519.«purex25519»
  "|- forall n q.        purex25519 (n,q) =        (@s.             s < p_25519 /\\             (forall Q.                  Q IN group_carrier (curve25519x_group sqintmod_field) /\\                  montgomery_xmap sqintmod_field Q =                  ring_of_num sqintmod_field q                  ==> montgomery_xmap sqintmod_field                      (group_pow (curve25519x_group sqintmod_field) Q n) =                      ring_of_num sqintmod_field s))"

-- Edwards448
#eval thm' "Edwards448.p_448" SessionEC.Edwards448.«p_448»
  "|- p_448 =    726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439"
#eval thm' "Edwards448.EE_448" SessionEC.Edwards448.«EE_448»
  "|- EE_448 =    &494088759867433727674302672526735089350544552303727723746126484473087719117037293890093462157703888342865036477787453078312060500281069,    &242279574765202296849774602629334844784547120229106020093830066393555416020021691321995239242950195063812052916896239502005235079621290"
#eval thm' "Edwards448.PRIME_P448" SessionEC.Edwards448.«PRIME_P448»
  "|- prime p_448"
#eval thm' "Edwards448.GENERATOR_IN_GROUP_CARRIER_EDWARDS448" SessionEC.Edwards448.«GENERATOR_IN_GROUP_CARRIER_EDWARDS448»
  "|- E_448 IN group_carrier edwards448_group"
#eval thm' "Edwards448.GROUP_ELEMENT_ORDER_EDWARDS448_H448" SessionEC.Edwards448.«GROUP_ELEMENT_ORDER_EDWARDS448_H448»
  "|- group_element_order edwards448_group H_448 = n_448"
#eval thm' "Edwards448.FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448" SessionEC.Edwards448.«FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448»
  "|- EE_448 IN group_carrier edwards448_group"

end T
