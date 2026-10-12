/- File: Lists.lean
Theory of lists, plus characters and strings as lists of characters.

Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Marco Maggesi 2014
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Printer
import HolCore.Nets
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Canon
import HolCore.Meson
import HolCore.Trivia
import HolMath.Pair
import HolMath.Nums
import HolMath.Recursion
import HolMath.Arith
import HolMath.Wf
import HolMath.CalcNum
import HolMath.Normalizer
import HolMath.Grobner
import HolMath.IndTypes
import HolMath.Base

namespace HolMath.Lists

set_option maxRecDepth 8000

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The `list_INDUCT` that `LIST_INDUCT_TAC` proves for itself (lists.ml
    18-20), with binders `h`, `t` in place of the stored theorem's. -/
def prove_list_INDUCT' [HolBase] (list_INDUCT : thm) : ExceptT String IO thm := do
  prove r"!P:(A)list->bool. P [] /\ (!h t. P t ==> P (CONS h t)) ==> !l. P l"
    (MATCH_ACCEPT_TAC list_INDUCT)

/-- `LIST_INDUCT_TAC` (lists.ml 17-21), given the theorem
    `prove_list_INDUCT'` proves. -/
def LIST_INDUCT_TAC [HolBase] (list_INDUCT' : thm) : tactic :=
  MATCH_MP_TAC list_INDUCT' THEN
  CONJ_TAC THENL [ALL_TAC, GEN_TAC THEN GEN_TAC THEN DISCH_TAC]

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The recursive definitions of `lists.ml` lines 28-143.  Field names match
    the OCaml identifiers exactly, in OCaml order.

    All are `new_recursive_definition list_RECURSION` except `REPLICATE`,
    `list_of_seq` (both `num_RECURSION`) and the six `_DEF`/derived pairs
    `ALL2_DEF`/`ALL2`, `MAP2_DEF`/`MAP2`, `ITLIST2_DEF`/`ITLIST2`,
    `ZIP_DEF`/`ZIP`, where the `_DEF` is the raw recursion and the plain name
    is a derived `prove`. -/
structure ListDefs where
  HD          : thm
  TL          : thm
  APPEND      : thm
  REVERSE     : thm
  LENGTH      : thm
  MAP         : thm
  LAST        : thm
  BUTLAST     : thm
  REPLICATE   : thm
  NULL        : thm
  ALL         : thm
  EX          : thm
  ITLIST      : thm
  MEM         : thm
  ALL2_DEF    : thm
  ALL2        : thm
  MAP2_DEF    : thm
  MAP2        : thm
  EL          : thm
  FILTER      : thm
  ASSOC       : thm
  ITLIST2_DEF : thm
  ITLIST2     : thm
  ZIP_DEF     : thm
  ZIP         : thm
  ALLPAIRS    : thm
  PAIRWISE    : thm
  list_of_seq : thm
  deriving Inhabited

/-- The basic list definitions of lists.ml 25-143.  `distinctness "list"`
    is passed in as `distinctness_list`. -/
@[nospecialize]
def setupListDefs [HolBase]
    (list_RECURSION num_RECURSION : thm) (distinctness_list : thm)
    (new_recursive_definition' : thm → term → IO (Except String thm)) :
    ExceptT String IO ListDefs := do
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)

  /- Basic definitions. -/

  let HD ← new_recursive_definition list_RECURSION
   r"HD(CONS (h:A) t) = h"

  let TL ← new_recursive_definition list_RECURSION
   r"TL(CONS (h:A) t) = t"

  let APPEND ← new_recursive_definition list_RECURSION
   r"(!l:(A)list. APPEND [] l = l) /\
   (!h t l. APPEND (CONS h t) l = CONS h (APPEND t l))"

  let REVERSE ← new_recursive_definition list_RECURSION
   r"(REVERSE [] = []) /\
   (REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x])"

  let LENGTH ← new_recursive_definition list_RECURSION
   r"(LENGTH [] = 0) /\
   (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t))"

  let MAP ← new_recursive_definition list_RECURSION
   r"(!f:A->B. MAP f NIL = NIL) /\
   (!f h t. MAP f (CONS h t) = CONS (f h) (MAP f t))"

  let LAST ← new_recursive_definition list_RECURSION
   r"LAST (CONS (h:A) t) = if t = [] then h else LAST t"

  let BUTLAST ← new_recursive_definition list_RECURSION
   r"(BUTLAST [] = []) /\
  (BUTLAST (CONS (h:A) t) = if t = [] then [] else CONS h (BUTLAST t))"

  let REPLICATE ← new_recursive_definition num_RECURSION
   r"(REPLICATE 0 (x:A) = []) /\
   (REPLICATE (SUC n) x = CONS x (REPLICATE n x))"

  let NULL ← new_recursive_definition list_RECURSION
   r"(NULL [] = T) /\
   (NULL (CONS (h:A) t) = F)"

  let ALL ← new_recursive_definition list_RECURSION
   r"(ALL P [] = T) /\
   (ALL P (CONS (h:A) t) <=> P h /\ ALL P t)"

  let EX ← new_recursive_definition list_RECURSION
   r"(EX P [] = F) /\
   (EX P (CONS (h:A) t) <=> P h \/ EX P t)"

  let ITLIST ← new_recursive_definition list_RECURSION
   r"(ITLIST (f:A->B->B) [] b = b) /\
   (ITLIST f (CONS h t) b = f h (ITLIST f t b))"

  let MEM ← new_recursive_definition list_RECURSION
   r"(MEM (x:A) [] <=> F) /\
   (MEM x (CONS h t) <=> (x = h) \/ MEM x t)"

  let ALL2_DEF ← new_recursive_definition list_RECURSION
   r"(ALL2 (P:A->B->bool) [] l2 <=> (l2 = [])) /\
   (ALL2 P (CONS h1 t1) l2 <=>
        if l2 = [] then F
        else P h1 (HD l2) /\ ALL2 P t1 (TL l2))"

  let ALL2 ← prove
   r"(ALL2 (P:A->B->bool) [] [] <=> T) /\
   (ALL2 P (CONS h1 t1) [] <=> F) /\
   (ALL2 P [] (CONS h2 t2) <=> F) /\
   (ALL2 P (CONS h1 t1) (CONS h2 t2) <=> P h1 h2 /\ ALL2 P t1 t2)"
   (REWRITE_TAC [distinctness_list, ALL2_DEF, HD, TL])

  let MAP2_DEF ← new_recursive_definition list_RECURSION
   r"(MAP2 (f:A->B->C) [] l = []) /\
   (MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l)))"

  let MAP2 ← prove
   r"(MAP2 (f:A->B->C) [] [] = []) /\
   (MAP2 f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (MAP2 f t1 t2))"
   (REWRITE_TAC [MAP2_DEF, HD, TL])

  let EL ← new_recursive_definition num_RECURSION
   r"(EL 0 l :A = HD l) /\
   (EL (SUC n) l = EL n (TL l))"

  let FILTER ← new_recursive_definition list_RECURSION
   r"(FILTER (P:A->bool) [] = []) /\
   (FILTER P (CONS h t) = if P h then CONS h (FILTER P t) else FILTER P t)"

  let ASSOC ← new_recursive_definition list_RECURSION
   r"ASSOC a (CONS (h:A#B) t) = if FST h = a then SND h else ASSOC a t"

  let ITLIST2_DEF ← new_recursive_definition list_RECURSION
   r"(ITLIST2 (f:A->B->C->C) [] l2 b = b) /\
   (ITLIST2 f (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b))"

  let ITLIST2 ← prove
   r"(ITLIST2 (f:A->B->C->C) [] [] b = b) /\
   (ITLIST2 f (CONS h1 t1) (CONS h2 t2) b = f h1 h2 (ITLIST2 f t1 t2 b))"
   (REWRITE_TAC [ITLIST2_DEF, HD, TL])

  let ZIP_DEF ← new_recursive_definition list_RECURSION
   r"(ZIP [] l2 :(A#B)list = []) /\
   (ZIP (CONS h1 t1) l2:(A#B)list = CONS (h1,HD l2) (ZIP t1 (TL l2)))"

  let ZIP ← prove
   r"(ZIP [] [] :(A#B)list = []) /\
   (ZIP (CONS h1 t1) (CONS h2 t2) :(A#B)list = CONS (h1,h2) (ZIP t1 t2))"
   (REWRITE_TAC [ZIP_DEF, HD, TL])

  let ALLPAIRS ← new_recursive_definition list_RECURSION
   r"(ALLPAIRS (f:A->B->bool) [] l <=> T) /\
   (ALLPAIRS f (CONS h t) l <=> ALL (f h) l /\ ALLPAIRS f t l)"

  let PAIRWISE ← new_recursive_definition list_RECURSION
   r"(PAIRWISE (r:A->A->bool) [] <=> T) /\
   (PAIRWISE (r:A->A->bool) (CONS h t) <=> ALL (r h) t /\ PAIRWISE r t)"

  let list_of_seq ← new_recursive_definition num_RECURSION
   r"list_of_seq (s:num->A) 0 = [] /\
  list_of_seq s (SUC n) = APPEND (list_of_seq s n) [s n]"

  return {
    HD, TL, APPEND, REVERSE, LENGTH, MAP, LAST, BUTLAST, REPLICATE, NULL, ALL,
    EX, ITLIST, MEM, ALL2_DEF, ALL2, MAP2_DEF, MAP2, EL, FILTER, ASSOC,
    ITLIST2_DEF, ITLIST2, ZIP_DEF, ZIP, ALLPAIRS, PAIRWISE, list_of_seq }

/- Various trivial theorems. -/

/-- The first 50 `lists.ml` theorems (lines 147-400), in OCaml order.  These
    are the small "trivial" results proved by list induction plus rewriting,
    occasionally finished with `MESON_TAC`/`ASM_MESON_TAC`. -/
structure ListThms1 where
  NOT_CONS_NIL    : thm
  LAST_CLAUSES    : thm
  APPEND_NIL      : thm
  APPEND_ASSOC    : thm
  REVERSE_APPEND  : thm
  REVERSE_REVERSE : thm
  REVERSE_EQ_EMPTY : thm
  CONS_11         : thm
  list_CASES      : thm
  LIST_EQ         : thm
  LENGTH_APPEND   : thm
  MAP_APPEND      : thm
  LENGTH_MAP      : thm
  LENGTH_EQ_NIL   : thm
  LENGTH_EQ_CONS  : thm
  LENGTH_REVERSE  : thm
  MAP_o           : thm
  MAP_EQ          : thm
  ALL_IMP         : thm
  NOT_EX          : thm
  NOT_ALL         : thm
  ALL_MAP         : thm
  ALL_EQ          : thm
  ALL_T           : thm
  MAP_EQ_ALL2     : thm
  ALL2_MAP        : thm
  MAP_EQ_DEGEN    : thm
  ALL2_AND_RIGHT  : thm
  ITLIST_APPEND   : thm
  ITLIST_EXTRA    : thm
  ALL_MP          : thm
  AND_ALL         : thm
  EX_IMP          : thm
  ALL_MEM         : thm
  LENGTH_REPLICATE : thm
  MEM_REPLICATE   : thm
  EX_MAP          : thm
  EXISTS_EX       : thm
  FORALL_ALL      : thm
  MEM_APPEND      : thm
  MEM_MAP         : thm
  FILTER_APPEND   : thm
  FILTER_MAP      : thm
  MEM_FILTER      : thm
  LENGTH_FILTER   : thm
  EX_MEM          : thm
  MAP_FST_ZIP     : thm
  MAP_SND_ZIP     : thm
  LENGTH_ZIP      : thm
  MEM_ASSOC       : thm
  deriving Inhabited

@[nospecialize]
def setupListThms1 [HolBase] (D : ListDefs)
    (distinctness_list injectivity_list : thm) (list_INDUCT' : thm)
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (N : HolMath.Nums.NumsThms)
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3)
    (Tr : HolCore.Trivia.TriviaThms)
    (Pr : HolMath.Pair.PairThms) :
    ExceptT String IO ListThms1 := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let LIST_INDUCT_TAC := LIST_INDUCT_TAC list_INDUCT'
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, SUC_INJ, num_CASES, .. } := N
  let { ADD_CLAUSES, .. } := A1
  let { MULT_CLAUSES, LT, LE, LT_0, LT_SUC, LE_SUC, .. } := A2
  let { LE_REFL, LE_TRANS, .. } := A3
  let { o_THM, .. } := Tr
  let { PAIR, FST, .. } := Pr
  let { CONJ_ACI, DISJ_ACI, .. } := HolBase.T
  let { DE_MORGAN_THM, .. } := HolBase.C
  let { HD, TL, APPEND, REVERSE, LENGTH, MAP, LAST, REPLICATE, ALL, EX, ITLIST,
        MEM, ALL2, EL, FILTER, ASSOC, ZIP, .. } := D

  let NOT_CONS_NIL ← prove
   r"!(h:A) t. ~(CONS h t = [])"
   (REWRITE_TAC [distinctness_list])

  let LAST_CLAUSES ← prove
   r"(LAST [h:A] = h) /\
   (LAST (CONS h (CONS k t)) = LAST (CONS k t))"
   (REWRITE_TAC [LAST, NOT_CONS_NIL])

  let APPEND_NIL ← prove
   r"!l:A list. APPEND l [] = l"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND])

  let APPEND_ASSOC ← prove
   r"!(l:A list) m n. APPEND l (APPEND m n) = APPEND (APPEND l m) n"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND])

  let REVERSE_APPEND ← prove
   r"!(l:A list) m. REVERSE (APPEND l m) = APPEND (REVERSE m) (REVERSE l)"
   (LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [APPEND, REVERSE, APPEND_NIL, APPEND_ASSOC])

  let REVERSE_REVERSE ← prove
   r"!l:A list. REVERSE(REVERSE l) = l"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [REVERSE, REVERSE_APPEND, APPEND])

  let REVERSE_EQ_EMPTY ← prove
   r"!l:A list. REVERSE l = [] <=> l = []"
   (MESON_TAC [REVERSE_REVERSE, REVERSE])

  let CONS_11 ← prove
   r"!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)"
   (REWRITE_TAC [injectivity_list])

  let list_CASES ← prove
   r"!l:(A)list. (l = []) \/ ?h t. l = CONS h t"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [CONS_11, NOT_CONS_NIL] THEN
    MESON_TAC [])

  let LIST_EQ ← prove
   r"!l1 l2:A list.
        l1 = l2 <=>
        LENGTH l1 = LENGTH l2 /\ !n. n < LENGTH l2 ==> EL n l1 = EL n l2"
   (REPEAT LIST_INDUCT_TAC THEN
    REWRITE_TAC [NOT_CONS_NIL, CONS_11, LENGTH, ← CONJUNCT1 LT, NOT_SUC] THEN
    ASM_REWRITE_TAC [SUC_INJ] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [← MESON [num_CASES] (← q r"(!n. P n) <=> P 0 /\ (!n. P(SUC n))")] THEN
    REWRITE_TAC [EL, HD, TL, LT_0, LT_SUC, CONJ_ACI])

  let LENGTH_APPEND ← prove
   r"!(l:A list) m. LENGTH(APPEND l m) = LENGTH l + LENGTH m"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND, LENGTH, ADD_CLAUSES])

  let MAP_APPEND ← prove
   r"!f:A->B. !l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, APPEND])

  let LENGTH_MAP ← prove
   r"!l. !f:A->B. LENGTH (MAP f l) = LENGTH l"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, LENGTH])

  let LENGTH_EQ_NIL ← prove
   r"!l:A list. (LENGTH l = 0) <=> (l = [])"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH, NOT_CONS_NIL, NOT_SUC])

  let LENGTH_EQ_CONS ← prove
   r"!(l:A list) n. LENGTH l = SUC n <=> ?h t. (l = CONS h t) /\ (LENGTH t = n)"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH, NOT_SUC, NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC [SUC_INJ, CONS_11] THEN MESON_TAC [])

  let LENGTH_REVERSE ← prove
   r"!l:A list. LENGTH(REVERSE l) = LENGTH l"
   (LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [REVERSE, LENGTH_APPEND, LENGTH] THEN
    REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES])

  let MAP_o ← prove
   r"!f:A->B. !g:B->C. !l. MAP (g o f) l = MAP g (MAP f l)"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, o_THM])

  let MAP_EQ ← prove
   r"!(f:A->B) g l. ALL (\x. f x = g x) l ==> (MAP f l = MAP g l)"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [MAP, ALL] THEN ASM_MESON_TAC [])

  let ALL_IMP ← prove
   r"!P Q l:A list. (!x. MEM x l /\ P x ==> Q x) /\ ALL P l ==> ALL Q l"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [MEM, ALL] THEN ASM_MESON_TAC [])

  let NOT_EX ← prove
   r"!P l:A list. ~(EX P l) <=> ALL (\x. ~(P x)) l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [EX, ALL, DE_MORGAN_THM])

  let NOT_ALL ← prove
   r"!P l:A list. ~(ALL P l) <=> EX (\x. ~(P x)) l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [EX, ALL, DE_MORGAN_THM])

  let ALL_MAP ← prove
   r"!P (f:A->B) l. ALL P (MAP f l) <=> ALL (P o f) l"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [ALL, MAP, o_THM])

  let ALL_EQ ← prove
   r"!l:A list.
        ALL R l /\ (!x. R x ==> (P x <=> Q x)) ==> (ALL P l <=> ALL Q l)"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [ALL] THEN
    STRIP_TAC THEN BINOP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [])

  let ALL_T ← prove
   r"!l:A list. ALL (\x. T) l"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL])

  let MAP_EQ_ALL2 ← prove
   r"!(f:A->B) l m. ALL2 (\x y. f x = f y) l m ==> MAP f l = MAP f m"
   (GEN_TAC THEN
    REPEAT LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, ALL2, CONS_11] THEN
    ASM_MESON_TAC [])

  let ALL2_MAP ← prove
   r"!P (f:A->B) l. ALL2 P (MAP f l) l <=> ALL (\a. P (f a) a) l"
   (GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2, MAP, ALL])

  let MAP_EQ_DEGEN ← prove
   r"!l (f:A->A). ALL (\x. f(x) = x) l ==> (MAP f l = l)"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, MAP, CONS_11] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  let ALL2_AND_RIGHT ← prove
   r"!l m P Q. ALL2 (\(x:A) (y:B). P x /\ Q x y) l m <=> ALL P l /\ ALL2 Q l m"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL, ALL2] THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL, ALL2] THEN
    REWRITE_TAC [CONJ_ACI])

  let ITLIST_APPEND ← prove
   r"!(f:A->B->B) a l1 l2.
        ITLIST f (APPEND l1 l2) a = ITLIST f l1 (ITLIST f l2 a)"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [ITLIST, APPEND])

  let ITLIST_EXTRA ← prove
   r"!(f:A->B->B) l. ITLIST f (APPEND l [a]) b = ITLIST f l (f a b)"
   (REWRITE_TAC [ITLIST_APPEND, ITLIST])

  let ALL_MP ← prove
   r"!P Q (l:A list). ALL (\x. P x ==> Q x) l /\ ALL P l ==> ALL Q l"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [ALL] THEN ASM_MESON_TAC [])

  let AND_ALL ← prove
   r"!l:A list. ALL P l /\ ALL Q l <=> ALL (\x. P x /\ Q x) l"
   (CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL, CONJ_ACI])

  let EX_IMP ← prove
   r"!P Q (l:A list). (!x. MEM x l /\ P x ==> Q x) /\ EX P l ==> EX Q l"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [MEM, EX] THEN ASM_MESON_TAC [])

  let ALL_MEM ← prove
   r"!P (l:A list). (!x. MEM x l ==> P x) <=> ALL P l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, MEM] THEN
    ASM_MESON_TAC [])

  let LENGTH_REPLICATE ← prove
   r"!n x:A. LENGTH(REPLICATE n x) = n"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, REPLICATE])

  let MEM_REPLICATE ← prove
   r"!n x y:A. MEM x (REPLICATE n y) <=> x = y /\ ~(n = 0)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [MEM, REPLICATE, NOT_SUC] THEN
    MESON_TAC [])

  let EX_MAP ← prove
   r"!P (f:A->B) l. EX P (MAP f l) <=> EX (P o f) l"
   (GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, EX, o_THM])

  let EXISTS_EX ← prove
   r"!(P:A->B->bool) l. (?x. EX (P x) l) <=> EX (\s. ?x. P x s) l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [EX] THEN
    ASM_MESON_TAC [])

  let FORALL_ALL ← prove
   r"!(P:A->B->bool) l. (!x. ALL (P x) l) <=> ALL (\s. !x. P x s) l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL] THEN
    ASM_MESON_TAC [])

  let MEM_APPEND ← prove
   r"!(x:A) l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \/ MEM x l2"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MEM, APPEND, DISJ_ACI])

  let MEM_MAP ← prove
   r"!(f:A->B) y l. MEM y (MAP f l) <=> ?x. MEM x l /\ (y = f x)"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MEM, MAP] THEN MESON_TAC [])

  let FILTER_APPEND ← prove
   r"!(P:A->bool) l1 l2.
        FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [FILTER, APPEND] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [APPEND])

  let FILTER_MAP ← prove
   r"!P (f:A->B) l. FILTER P (MAP f l) = MAP f (FILTER (P o f) l)"
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, FILTER, o_THM] THEN COND_CASES_TAC THEN
    REWRITE_TAC [MAP])

  let MEM_FILTER ← prove
   r"!P l (x:A). MEM x (FILTER P l) <=> P x /\ MEM x l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MEM, FILTER] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [MEM] THEN
    ASM_MESON_TAC [])

  let LENGTH_FILTER ← prove
   r"!P l:A list. LENGTH(FILTER P l) <= LENGTH l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [FILTER, LE_REFL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH, LE_SUC] THEN
    ASM_MESON_TAC [LE_TRANS, LE])

  let EX_MEM ← prove
   r"!P (l:A list). (?x. P x /\ MEM x l) <=> EX P l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [EX, MEM] THEN
    ASM_MESON_TAC [])

  let MAP_FST_ZIP ← prove
   r"!(l1:A list) (l2:B list).
    LENGTH l1 = LENGTH l2 ==> MAP FST (ZIP l1 l2) = l1"
   (LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC [LENGTH, SUC_INJ, MAP, FST, ZIP, NOT_SUC])

  let MAP_SND_ZIP ← prove
   r"!(l1:A list) (l2:B list).
    LENGTH l1 = LENGTH l2 ==> MAP SND (ZIP l1 l2) = l2"
   (LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC [LENGTH, SUC_INJ, MAP, FST, ZIP, NOT_SUC])

  let LENGTH_ZIP ← prove
   r"!(l1:A list) (l2:B list).
    LENGTH l1 = LENGTH l2 ==> LENGTH(ZIP l1 l2) = LENGTH l2"
   (REPEAT (LIST_INDUCT_TAC ORELSE GEN_TAC) THEN
    ASM_SIMP_TAC [LENGTH, NOT_SUC, ZIP, SUC_INJ])

  let MEM_ASSOC ← prove
   r"!(l:(A#B)list) x. MEM (x,ASSOC x l) l <=> MEM x (MAP FST l)"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MEM, MAP, ASSOC] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [PAIR, FST])

  return {
    NOT_CONS_NIL, LAST_CLAUSES, APPEND_NIL, APPEND_ASSOC, REVERSE_APPEND,
    REVERSE_REVERSE, REVERSE_EQ_EMPTY, CONS_11, list_CASES, LIST_EQ,
    LENGTH_APPEND, MAP_APPEND, LENGTH_MAP, LENGTH_EQ_NIL, LENGTH_EQ_CONS,
    LENGTH_REVERSE, MAP_o, MAP_EQ, ALL_IMP, NOT_EX, NOT_ALL, ALL_MAP, ALL_EQ,
    ALL_T, MAP_EQ_ALL2, ALL2_MAP, MAP_EQ_DEGEN, ALL2_AND_RIGHT, ITLIST_APPEND,
    ITLIST_EXTRA, ALL_MP, AND_ALL, EX_IMP, ALL_MEM, LENGTH_REPLICATE,
    MEM_REPLICATE, EX_MAP, EXISTS_EX, FORALL_ALL, MEM_APPEND, MEM_MAP,
    FILTER_APPEND, FILTER_MAP, MEM_FILTER, LENGTH_FILTER, EX_MEM, MAP_FST_ZIP,
    MAP_SND_ZIP, LENGTH_ZIP, MEM_ASSOC }

/-- The second 51 `lists.ml` theorems (lines 405-697), in OCaml order.  Like
    `ListThms1` these are the small "trivial" results proved by list (or
    numeric) induction plus rewriting, occasionally finished with
    `MESON_TAC`/`ASM_MESON_TAC`, a few doing explicit case splits. -/
structure ListThms2 where
  ALL_APPEND                : thm
  MEM_EL                    : thm
  MEM_EXISTS_EL             : thm
  ALL_EL                    : thm
  ALL2_MAP2                 : thm
  AND_ALL2                  : thm
  ALLPAIRS_SYM              : thm
  ALLPAIRS_MEM              : thm
  ALLPAIRS_MAP              : thm
  ALLPAIRS_EQ               : thm
  ALL2_ALL                  : thm
  APPEND_EQ_NIL             : thm
  APPEND_LCANCEL            : thm
  APPEND_RCANCEL            : thm
  LENGTH_MAP2               : thm
  EL_MAP2                   : thm
  MAP_EQ_NIL                : thm
  INJECTIVE_MAP             : thm
  SURJECTIVE_MAP            : thm
  MAP_ID                    : thm
  MAP_I                     : thm
  BUTLAST_CLAUSES           : thm
  BUTLAST_APPEND            : thm
  APPEND_BUTLAST_LAST       : thm
  LAST_APPEND               : thm
  LENGTH_TL                 : thm
  LAST_REVERSE              : thm
  HD_REVERSE                : thm
  EL_APPEND                 : thm
  EL_TL                     : thm
  EL_CONS                   : thm
  LAST_EL                   : thm
  HD_APPEND                 : thm
  CONS_HD_TL                : thm
  EL_MAP                    : thm
  MAP_REVERSE               : thm
  ALL_FILTER                : thm
  APPEND_SING               : thm
  MEM_APPEND_DECOMPOSE_LEFT : thm
  MEM_APPEND_DECOMPOSE      : thm
  PAIRWISE_APPEND           : thm
  PAIRWISE_MAP              : thm
  PAIRWISE_IMPLIES          : thm
  PAIRWISE_TRANSITIVE       : thm
  LENGTH_LIST_OF_SEQ        : thm
  EL_LIST_OF_SEQ            : thm
  LIST_OF_SEQ_EQ_NIL        : thm
  LIST_OF_SEQ_EQ_SELF       : thm
  LENGTH_EQ_LIST_OF_SEQ     : thm
  MAP_LIST_OF_SEQ           : thm
  LIST_OF_SEQ               : thm
  deriving Inhabited

/-- lists.ml 405-697.  `list_INDUCT` is the theorem from the list type
    definition, used directly by `MATCH_MP_TAC list_INDUCT` as in OCaml;
    `list_INDUCT'` is LIST_INDUCT_TAC's own restatement. -/
@[nospecialize]
def setupListThms2 [HolBase] (D : ListDefs) (T1 : ListThms1)
    (list_INDUCT list_INDUCT' : thm)
    (MESON_TAC ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (N : HolMath.Nums.NumsThms)
    (A1 : HolMath.Arith.ArithThms1) (A2 : HolMath.Arith.ArithThms2)
    (A3 : HolMath.Arith.ArithThms3) (A5 : HolMath.Arith.ArithThms5)
    (Tr : HolCore.Trivia.TriviaThms)
    (Cn : HolMath.CalcNum.ArithRewrites)
    (o_DEF I_DEF : thm) :
    ExceptT String IO ListThms2 := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let LIST_INDUCT_TAC := LIST_INDUCT_TAC list_INDUCT'
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, SUC_INJ, num_CASES, .. } := N
  let { ADD_CLAUSES, ADD_EQ_0, ADD1, .. } := A1
  let { LT, LT_0, LT_SUC, .. } := A2
  let { LT_REFL, .. } := A3
  let { SUB_0, SUB_SUC, SUB_REFL, SUC_SUB1, .. } := A5
  let { o_THM, .. } := Tr
  let { ARITH, .. } := Cn
  let { CONJ_ACI, CONJ_ASSOC, IMP_CONJ, SWAP_FORALL_THM, LEFT_IMP_EXISTS_THM, .. } := HolBase.T
  let { FUN_EQ_THM, COND_RAND, .. } := HolBase.C
  let { HD, TL, APPEND, REVERSE, LENGTH, MAP, LAST, BUTLAST, ALL, MEM, ALL2,
        MAP2, EL, FILTER, ALLPAIRS, PAIRWISE, list_of_seq, .. } := D
  let { NOT_CONS_NIL, APPEND_NIL, REVERSE_APPEND, REVERSE_REVERSE,
        REVERSE_EQ_EMPTY, CONS_11, LIST_EQ, LENGTH_APPEND, MAP_APPEND,
        LENGTH_EQ_NIL, ALL_IMP, ALL_MAP, ALL_MEM, MEM_APPEND, MEM_MAP, .. } := T1

  let ALL_APPEND ← prove
   r"!P l1 l2:A list. ALL P (APPEND l1 l2) <=> ALL P l1 /\ ALL P l2"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [ALL, APPEND, ← GSYM CONJ_ASSOC])

  let MEM_EL ← prove
   r"!(l:A list) n. n < LENGTH l ==> MEM (EL n l) l"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, ← CONJUNCT1 LT, LENGTH] THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [EL, HD, LT_SUC, TL])

  let MEM_EXISTS_EL ← prove
   r"!(l:A list) x. MEM x l <=> ?i. i < LENGTH l /\ x = EL i l"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, EL, MEM, ← CONJUNCT1 LT] THEN
    GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV
     [← MESON [num_CASES] (← q r"(?i. P i) <=> P 0 \/ (?i. P(SUC i))")] THEN
    REWRITE_TAC [LT_SUC, LT_0, EL, HD, TL])

  let ALL_EL ← prove
   r"!P (l:A list). (!i. i < LENGTH l ==> P (EL i l)) <=> ALL P l"
   (REWRITE_TAC [← GSYM ALL_MEM, MEM_EXISTS_EL] THEN MESON_TAC [])

  let ALL2_MAP2 ← prove
   r"!(f:A->B) (g:C->D) l m.
        ALL2 P (MAP f l) (MAP g m) = ALL2 (\x y. P (f x) (g y)) l m"
   (GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2, MAP])

  let AND_ALL2 ← prove
   r"!(P:A->B->bool) Q l m.
        ALL2 P l m /\ ALL2 Q l m <=> ALL2 (\x y. P x y /\ Q x y) l m"
   (GEN_TAC THEN GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL2] THEN
    REWRITE_TAC [CONJ_ACI])

  let ALLPAIRS_SYM ← prove
   r"!(P:A->B->bool) l m. ALLPAIRS P l m <=> ALLPAIRS (\x y. P y x) m l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [ALLPAIRS] THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALLPAIRS, ALL] THEN
    ASM_MESON_TAC [])

  let ALLPAIRS_MEM ← prove
   r"!(P:A->B->bool) l m.
        (!x y. MEM x l /\ MEM y m ==> P x y) <=> ALLPAIRS P l m"
   (GEN_TAC THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ALLPAIRS, ← GSYM ALL_MEM, MEM] THEN
    ASM_MESON_TAC [])

  let ALLPAIRS_MAP ← prove
   r"!P (f:A->B) (g:C->D) l m.
        ALLPAIRS P (MAP f l) (MAP g m) <=>
        ALLPAIRS (\x y. P (f x) (g y)) l m"
   (REWRITE_TAC [← GSYM ALLPAIRS_MEM, MEM_MAP] THEN MESON_TAC [])

  let ALLPAIRS_EQ ← prove
   r"!l m. !P Q. ALL P (l:A list) /\ ALL Q (m:B list) /\
               (!p q. P p /\ Q q ==> (R p q <=> R' p q))
               ==> (ALLPAIRS R l m <=> ALLPAIRS R' l m)"
   (REWRITE_TAC [← GSYM ALLPAIRS_MEM, ← GSYM ALL_MEM] THEN MESON_TAC [])

  let ALL2_ALL ← prove
   r"!P (l:A list). ALL2 P l l <=> ALL (\x. P x x) l"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [ALL2, ALL])

  let APPEND_EQ_NIL ← prove
   r"!l m:A list. (APPEND l m = []) <=> (l = []) /\ (m = [])"
   (REWRITE_TAC [← GSYM LENGTH_EQ_NIL, LENGTH_APPEND, ADD_EQ_0])

  let APPEND_LCANCEL ← prove
   r"!l1 l2 l3:A list. APPEND l1 l2 = APPEND l1 l3 <=> l2 = l3"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND, CONS_11])

  let APPEND_RCANCEL ← prove
   r"!l1 l2 l3:A list. APPEND l1 l3 = APPEND l2 l3 <=> l1 = l2"
   (ONCE_REWRITE_TAC [← MESON [REVERSE_REVERSE]
     (← q r"l = l' <=> REVERSE l = REVERSE l'")] THEN
    REWRITE_TAC [REVERSE_APPEND, APPEND_LCANCEL])

  let LENGTH_MAP2 ← prove
   r"!(f:A->B->C) l m. LENGTH l = LENGTH m ==> LENGTH(MAP2 f l m) = LENGTH m"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC [LENGTH, NOT_CONS_NIL, NOT_SUC, MAP2, SUC_INJ])

  let EL_MAP2 ← prove
   r"!(f:A->B->C) l m k.
        k < LENGTH l /\ k < LENGTH m
        ==> EL k (MAP2 f l m) = f (EL k l) (EL k m)"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC [LENGTH, ← CONJUNCT1 LT] THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [LENGTH, MAP2, EL, HD, TL, LT_SUC])

  let MAP_EQ_NIL ← prove
   r"!(f:A->B) l. MAP f l = [] <=> l = []"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, NOT_CONS_NIL])

  let INJECTIVE_MAP ← prove
   r"!f:A->B. (!l m. MAP f l = MAP f m ==> l = m) <=>
            (!x y. f x = f y ==> x = y)"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"[x:A]", ← q r"[y:A]"]) THEN
      ASM_REWRITE_TAC [MAP, CONS_11],
      REPEAT LIST_INDUCT_TAC THEN ASM_SIMP_TAC [MAP, NOT_CONS_NIL, CONS_11] THEN
      ASM_MESON_TAC []])

  let SURJECTIVE_MAP ← prove
   r"!f:A->B. (!m. ?l. MAP f l = m) <=> (!y. ?x. f x = y)"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC (← q r"y:B") THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"[y:B]")) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, CONS_11, NOT_CONS_NIL, MAP_EQ_NIL],
      MATCH_MP_TAC list_INDUCT] THEN
    ASM_MESON_TAC [MAP])

  let MAP_ID ← prove
   r"!l. MAP (\x:A. x) l = l"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP])

  let MAP_I ← prove
   r"MAP (I:A->A) = I"
   (REWRITE_TAC [FUN_EQ_THM, I_DEF, MAP_ID])

  let BUTLAST_CLAUSES ← prove
   r"BUTLAST([]:A list) = [] /\
   (!a:A. BUTLAST [a] = []) /\
   (!(a:A) h t. BUTLAST(CONS a (CONS h t)) = CONS a (BUTLAST(CONS h t)))"
   (REWRITE_TAC [BUTLAST, NOT_CONS_NIL])

  let BUTLAST_APPEND ← prove
   r"!l m:A list. BUTLAST(APPEND l m) =
                if m = [] then BUTLAST l else APPEND l (BUTLAST m)"
   (SIMP_TAC [COND_RAND, APPEND_NIL, ← MESON []
     (← q r"(if p then T else q) <=> ~p ==> q")] THEN
    LIST_INDUCT_TAC THEN ASM_SIMP_TAC [APPEND, BUTLAST, APPEND_EQ_NIL])

  let APPEND_BUTLAST_LAST ← prove
   r"!l:A list. ~(l = []) ==> APPEND (BUTLAST l) [LAST l] = l"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [LAST, BUTLAST, NOT_CONS_NIL] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [APPEND])

  let LAST_APPEND ← prove
   r"!p q:A list. LAST(APPEND p q) = if q = [] then LAST p else LAST q"
   (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND, LAST, APPEND_EQ_NIL] THEN
    MESON_TAC [])

  let LENGTH_TL ← prove
   r"!l:A list. ~(l = []) ==> LENGTH(TL l) = LENGTH l - 1"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH, TL, ARITH, SUC_SUB1])

  let LAST_REVERSE ← prove
   r"!l:A list. ~(l = []) ==> LAST(REVERSE l) = HD l"
   (LIST_INDUCT_TAC THEN
    REWRITE_TAC [HD, REVERSE, LAST, LAST_APPEND, NOT_CONS_NIL])

  let HD_REVERSE ← prove
   r"!l:A list. ~(l = []) ==> HD(REVERSE l) = LAST l"
   (MESON_TAC [LAST_REVERSE, REVERSE_REVERSE, REVERSE_EQ_EMPTY])

  let EL_APPEND ← prove
   r"!k l m:A list.
        EL k (APPEND l m) = if k < LENGTH l then EL k l
                            else EL (k - LENGTH l) m"
   (INDUCT_TAC THEN REWRITE_TAC [EL] THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [HD, APPEND, LENGTH, SUB_0, EL, LT_0, ← CONJUNCT1 LT] THEN
    ASM_REWRITE_TAC [TL, LT_SUC, SUB_SUC])

  let EL_TL ← prove
   r"!n. EL n (TL l):A = EL (n + 1) l"
   (REWRITE_TAC [← GSYM ADD1, EL])

  let EL_CONS ← prove
   r"!n (h:A) t. EL n (CONS h t) = if n = 0 then h else EL (n - 1) t"
   (INDUCT_TAC THEN REWRITE_TAC [EL, HD, TL, NOT_SUC, SUC_SUB1])

  let LAST_EL ← prove
   r"!l:A list. ~(l = []) ==> LAST l = EL (LENGTH l - 1) l"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [LAST, LENGTH, SUC_SUB1] THEN
    DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [LENGTH, EL, HD, EL_CONS, LENGTH_EQ_NIL])

  let HD_APPEND ← prove
   r"!l m:A list. HD(APPEND l m) = if l = [] then HD m else HD l"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [HD, APPEND, NOT_CONS_NIL])

  let CONS_HD_TL ← prove
   r"!l:A list. ~(l = []) ==> l = CONS (HD l) (TL l)"
   (LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL, HD, TL])

  let EL_MAP ← prove
   r"!(f:A->B) n l. n < LENGTH l ==> EL n (MAP f l) = f(EL n l)"
   (GEN_TAC THEN INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [LENGTH, ← CONJUNCT1 LT, LT_0, EL, HD, TL, MAP, LT_SUC])

  let MAP_REVERSE ← prove
   r"!(f:A->B) l. REVERSE(MAP f l) = MAP f (REVERSE l)"
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP, REVERSE, MAP_APPEND])

  let ALL_FILTER ← prove
   r"!P Q l:A list. ALL P (FILTER Q l) <=> ALL (\x. Q x ==> P x) l"
   (GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, FILTER] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ALL])

  let APPEND_SING ← prove
   r"!(h:A) t. APPEND [h] t = CONS h t"
   (REWRITE_TAC [APPEND])

  let MEM_APPEND_DECOMPOSE_LEFT ← prove
   r"!x:A l. MEM x l <=> ?l1 l2. ~(MEM x l1) /\ l = APPEND l1 (CONS x l2)"
   (REWRITE_TAC [← TAUT (← q r"(p <=> q) <=> (p ==> q) /\ (q ==> p)")] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, MEM_APPEND, MEM] THEN X_GEN_TAC (← q r"x:A") THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [MEM] THEN
    MAP_EVERY X_GEN_TAC [← q r"y:A", ← q r"l:A list"] THEN
    ASM_CASES_TAC (← q r"x:A = y") THEN ASM_MESON_TAC [MEM, APPEND])

  let MEM_APPEND_DECOMPOSE ← prove
   r"!x:A l. MEM x l <=> ?l1 l2. l = APPEND l1 (CONS x l2)"
   (REWRITE_TAC [← TAUT (← q r"(p <=> q) <=> (p ==> q) /\ (q ==> p)")] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, MEM_APPEND, MEM] THEN
    ONCE_REWRITE_TAC [MEM_APPEND_DECOMPOSE_LEFT] THEN MESON_TAC [])

  let PAIRWISE_APPEND ← prove
   r"!R:A->A->bool l m.
        PAIRWISE R (APPEND l m) <=>
        PAIRWISE R l /\ PAIRWISE R m /\ (!x y. MEM x l /\ MEM y m ==> R x y)"
   (GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [APPEND, PAIRWISE, MEM, ALL_APPEND, ← GSYM ALL_MEM] THEN
    MESON_TAC [])

  let PAIRWISE_MAP ← prove
   r"!R f:A->B l.
        PAIRWISE R (MAP f l) <=> PAIRWISE (\x y. R (f x) (f y)) l"
   (GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [PAIRWISE, MAP, ALL_MAP, o_DEF])

  let PAIRWISE_IMPLIES ← prove
   r"!R:A->A->bool R' l.
        PAIRWISE R l /\ (!x y. MEM x l /\ MEM y l /\ R x y ==> R' x y)
        ==> PAIRWISE R' l"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC [PAIRWISE, ← GSYM ALL_MEM, MEM] THEN MESON_TAC [])

  let PAIRWISE_TRANSITIVE ← prove
   r"!R x y:A l.
      (!x y z. R x y /\ R y z ==> R x z)
      ==> (PAIRWISE R (CONS x (CONS y l)) <=> R x y /\ PAIRWISE R (CONS y l))"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [PAIRWISE, ALL, ← GSYM CONJ_ASSOC,
                 ← TAUT (← q r"(p /\ q /\ r /\ s <=> p /\ r /\ s) <=>
                      p /\ s ==> r ==> q")] THEN
    STRIP_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] ALL_IMP) THEN
    ASM_MESON_TAC [])

  let LENGTH_LIST_OF_SEQ ← prove
   r"!s:num->A n. LENGTH(list_of_seq s n) = n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [list_of_seq, LENGTH, LENGTH_APPEND, ADD_CLAUSES])

  let EL_LIST_OF_SEQ ← prove
   r"!s:num->A m n. m < n ==> EL m (list_of_seq s n) = s m"
   (GEN_TAC THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    INDUCT_TAC THEN
    REWRITE_TAC [list_of_seq, LT, EL_APPEND, LENGTH_LIST_OF_SEQ] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SUB_REFL, EL, HD, LT_REFL])

  let LIST_OF_SEQ_EQ_NIL ← prove
   r"!s:num->A n. list_of_seq s n = [] <=> n = 0"
   (REWRITE_TAC [← GSYM LENGTH_EQ_NIL, LENGTH_LIST_OF_SEQ, LENGTH])

  let LIST_OF_SEQ_EQ_SELF ← prove
   r"!l:A list. list_of_seq (\i. EL i l) (LENGTH l) = l"
   (SIMP_TAC [LIST_EQ, LENGTH_LIST_OF_SEQ, EL_LIST_OF_SEQ])

  let LENGTH_EQ_LIST_OF_SEQ ← prove
   r"!(l:A list) n. LENGTH l = n <=> l = list_of_seq (\i. EL i l) n"
   (MESON_TAC [LIST_OF_SEQ_EQ_SELF, LENGTH_LIST_OF_SEQ])

  let MAP_LIST_OF_SEQ ← prove
   r"!f (g:A->B) n. MAP g (list_of_seq f n) = list_of_seq (g o f) n"
   (GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, list_of_seq, MAP_APPEND, o_THM])

  let LIST_OF_SEQ ← prove
   r"(!(f:num->A). list_of_seq f 0 = []) /\
   (!(f:num->A) n.
        list_of_seq f (SUC n) = CONS (f 0) (list_of_seq (f o SUC) n))"
   (REWRITE_TAC [← CONJUNCT1 list_of_seq] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [LIST_EQ, LENGTH_LIST_OF_SEQ, LENGTH, EL_CONS] THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [NOT_SUC, EL_LIST_OF_SEQ] THEN
    ASM_SIMP_TAC [LT_SUC, SUC_SUB1, EL_LIST_OF_SEQ, o_THM])

  return {
    ALL_APPEND, MEM_EL, MEM_EXISTS_EL, ALL_EL, ALL2_MAP2, AND_ALL2,
    ALLPAIRS_SYM, ALLPAIRS_MEM, ALLPAIRS_MAP, ALLPAIRS_EQ, ALL2_ALL,
    APPEND_EQ_NIL, APPEND_LCANCEL, APPEND_RCANCEL, LENGTH_MAP2, EL_MAP2,
    MAP_EQ_NIL, INJECTIVE_MAP, SURJECTIVE_MAP, MAP_ID, MAP_I, BUTLAST_CLAUSES,
    BUTLAST_APPEND, APPEND_BUTLAST_LAST, LAST_APPEND, LENGTH_TL, LAST_REVERSE,
    HD_REVERSE, EL_APPEND, EL_TL, EL_CONS, LAST_EL, HD_APPEND, CONS_HD_TL,
    EL_MAP, MAP_REVERSE, ALL_FILTER, APPEND_SING, MEM_APPEND_DECOMPOSE_LEFT,
    MEM_APPEND_DECOMPOSE, PAIRWISE_APPEND, PAIRWISE_MAP, PAIRWISE_IMPLIES,
    PAIRWISE_TRANSITIVE, LENGTH_LIST_OF_SEQ, EL_LIST_OF_SEQ,
    LIST_OF_SEQ_EQ_NIL, LIST_OF_SEQ_EQ_SELF, LENGTH_EQ_LIST_OF_SEQ,
    MAP_LIST_OF_SEQ, LIST_OF_SEQ }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- `mk_cons h t` (lists.ml 702-705). -/
def mk_cons (h t : term) : IO (Except String term) := ExceptT.run do
  tryWith (do
      let cons ← ExceptT.mk (mk_const "CONS" [(type_of h, aty)])
      liftExcept (do mk_comb (← mk_comb cons h) t))
    (throw "mk_cons")

/-- `mk_list (tms,ty)` (lists.ml 707-712). -/
def mk_list (tms : List term) (ty : hol_type) : IO (Except String term) := ExceptT.run do
  tryWith (do
      let nil ← ExceptT.mk (mk_const "NIL" [(ty, aty)])
      if tms == [] then return nil
      let cons ← ExceptT.mk (mk_const "CONS" [(ty, aty)])
      liftExcept (tms.foldrM (fun tm acc => do (← mk_binop cons tm) acc) nil))
    (throw "mk_list")

/-- `mk_flist tms` (lists.ml 714-716). -/
def mk_flist (tms : List term) : IO (Except String term) := ExceptT.run do
  tryWith (do ExceptT.mk (mk_list tms (type_of (← liftExcept (hd tms))))) (throw "mk_flist")

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The two extra monotonicity theorems of `lists.ml` lines 722-731, proved
    here (in the pure library) so that SESSION can PREPEND them to
    `monotonicity_theorems` in OCaml order.  They are returned rather than
    captured in a value: the registration must be an IO ref update on Session's
    live `theMonotonicityTheorems`, never a frozen snapshot. -/
structure MonoAllThms where
  MONO_ALL  : thm
  MONO_ALL2 : thm
  deriving Inhabited

@[nospecialize]
def setupMonoAll [HolBase] (D : ListDefs) (list_INDUCT' : thm)
    (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO MonoAllThms := do
  let LIST_INDUCT_TAC := LIST_INDUCT_TAC list_INDUCT'
  let { ALL, ALL2_DEF, .. } := D

  let MONO_ALL ← prove
   r"(!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l"
   (DISCH_TAC THEN SPEC_TAC (← q r"l:A list", ← q r"l:A list") THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL] THEN ASM_MESON_TAC [])

  let MONO_ALL2 ← prove
   r"(!x y. (P:A->B->bool) x y ==> Q x y) ==> ALL2 P l l' ==> ALL2 Q l l'"
   (DISCH_TAC THEN
    SPEC_TAC (← q r"l':B list", ← q r"l':B list") THEN SPEC_TAC (← q r"l:A list", ← q r"l:A list") THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ALL2_DEF] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [])

  return {
    MONO_ALL, MONO_ALL2 }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- `LIST_CONV conv tm` (lists.ml 740-746), for a pure conversion. -/
partial def LIST_CONV (cnv : Equal.conv) : Equal.conv := fun tm =>
  if is_cons tm then Equal.COMB2_CONV (Equal.RAND_CONV cnv) (LIST_CONV cnv) tm
  else match dest_const tm with
    | .error e => .error e
    | .ok (name, _) => if name == "NIL" then .ok (REFL tm) else failwith "LIST_CONV"

/-- `LIST_CONV conv tm` (lists.ml 740-746), for a conversion in `IO`
    (`LIST_CONV num_CONV`). -/
partial def LIST_CONV_IO [HolBase] (cnv : ioconv) : ioconv := fun tm =>
  if is_cons tm then COMB2_CONV (RAND_CONV cnv) (LIST_CONV_IO cnv) tm
  else pure (match dest_const tm with
    | .error e => .error e
    | .ok (name, _) => if name == "NIL" then .ok (REFL tm) else failwith "LIST_CONV")

/-- The evaluation conversions of lists.ml 751-876. -/
structure ListEvalConvs where
  LENGTH_CONV : ioconv
  EL_CONV : ioconv
  REVERSE_CONV : ioconv
  LIST_OF_SEQ_CONV : ioconv

instance : Inhabited ListEvalConvs :=
  ⟨⟨fun _ => pure (.error ""), fun _ => pure (.error ""), fun _ => pure (.error ""),
    fun _ => pure (.error "")⟩⟩

/-- OCaml's `sort (<)` on terms. -/
private def sortTerms (l : List term) : List term := sort (fun x y => compare x y == .lt) l

/-- `LENGTH_CONV`, `EL_CONV`, `REVERSE_CONV` and `LIST_OF_SEQ_CONV`
    (lists.ml 751-876): each proves its `pthc` once and returns the
    conversion. -/
@[nospecialize]
partial def setupListEvalConvs [HolBase] (D : ListDefs) (T1 : ListThms1)
    (A1 : HolMath.Arith.ArithThms1) (NUM_SUC_CONV num_CONV : ioconv) :
    ExceptT String IO ListEvalConvs := do
  let elemTy (ltm : term) : ExceptT String IO hol_type :=
    liftExcept (do hd (← dest_type (type_of ltm)).2)

  -- LENGTH_CONV (lists.ml 751-778).
  let len_pthc ← prove
   r"LENGTH(t:A list) = LENGTH t + 0 /\
     LENGTH([]:A list) + n = n /\
     LENGTH(CONS (h:A) t) + n = LENGTH t + SUC n"
   (REWRITE_TAC [D.LENGTH, A1.ADD_CLAUSES])
  let len_pths := CONJUNCTS len_pthc
  let len_avars := sortTerms (frees (concl len_pthc))
  let LENGTH_CONV : ioconv := fun tm => ExceptT.run do
    match tm with
    | .Comb (.Const "LENGTH" _) ltm =>
      if !(is_list ltm) then throw "LENGTH_CONV"
      let tyin := [(← elemTy ltm, aty)]
      let [h_tm, n_tm, t_tm] := len_avars.map (inst tyin) | throw "LENGTH_CONV"
      let [pth_init, pth_base, pth_step] ← len_pths.mapM (INST_TYPE tyin) | throw "LENGTH_CONV"
      let rec lconv (th : thm) : ExceptT String IO thm := do
        let (altm, ntm) ← liftExcept (do dest_comb (← rand (concl th)))
        let ltm ← liftExcept (do rand (← rand altm))
        if is_cons ltm then
          let (htm, ttm) ← liftExcept (dest_cons ltm)
          let th1 ← INST [(htm, h_tm), (ttm, t_tm), (ntm, n_tm)] pth_step
          let (ftm, stm) ← liftExcept (do dest_comb (← rand (concl th1)))
          let th2 ← TRANS th1 (← AP_TERM ftm (← ExceptT.mk (NUM_SUC_CONV stm)))
          lconv (← TRANS th th2)
        else TRANS th (← INST [(ntm, n_tm)] pth_base)
      tryWith (do lconv (← INST [(← liftExcept (rand tm), t_tm)] pth_init)) (throw "LENGTH_CONV")
    | _ => throw "LENGTH_CONV"

  -- EL_CONV (lists.ml 780-807).
  let el_pthc ← prove
    r"EL 0 (CONS (h:A) t) = h /\
      (n = SUC m ==> EL n (CONS h t) = EL m t)"
    (SIMP_TAC [D.EL, D.HD, D.TL])
  let el_pths ← (CONJUNCTS el_pthc).mapM UNDISCH_ALL
  let el_avars := sortTerms (frees (concl el_pthc))
  let EL_CONV : ioconv := fun tm => ExceptT.run do
    match tm with
    | .Comb (.Comb (.Const "EL" _) _) ltm =>
      if !(is_list ltm) then throw "EL_CONV"
      let tyin := [(← elemTy ltm, aty)]
      let [h_tm, m_tm, n_tm, t_tm] := el_avars.map (inst tyin) | throw "EL_CONV"
      let [pth_base, pth_step] ← el_pths.mapM (INST_TYPE tyin) | throw "EL_CONV"
      let rec econv (th : thm) : ExceptT String IO thm := do
        let (entm, ltm) ← liftExcept (do dest_comb (← rand (concl th)))
        let (htm, ttm) ← liftExcept (dest_cons ltm)
        let (_etm, ntm) ← liftExcept (dest_comb entm)
        let n ← liftExcept (dest_numeral ntm)
        if n == num_0 then TRANS th (← INST [(htm, h_tm), (ttm, t_tm)] pth_base)
        else
          let th1 ← ExceptT.mk (num_CONV ntm)
          let th2 ← INST [(ntm, n_tm), (← liftExcept (do rand (← rand (concl th1))), m_tm),
                          (htm, h_tm), (ttm, t_tm)] pth_step
          let th3 ← TRANS th (← PROVE_HYP th1 th2)
          econv th3
      tryWith (econv (REFL tm)) (throw "EL_CONV")
    | _ => throw "EL_CONV"

  -- REVERSE_CONV (lists.ml 809-834).
  let rev_pthc ← prove
   r"l:A list = APPEND l [] /\
     APPEND (REVERSE []) l:A list = l /\
     APPEND (REVERSE (CONS h t)) l = APPEND (REVERSE t) (CONS h l)"
   (SIMP_TAC [D.APPEND, T1.APPEND_NIL, D.REVERSE, ← GSYM T1.APPEND_ASSOC])
  let rev_pths ← (CONJUNCTS rev_pthc).mapM UNDISCH_ALL
  let rev_avars := sortTerms (frees (concl rev_pthc))
  let REVERSE_CONV : ioconv := fun tm => ExceptT.run do
    match tm with
    | .Comb (.Const "REVERSE" _) ltm =>
      let tyin := [(← elemTy ltm, aty)]
      let [h_tm, l_tm, t_tm] := rev_avars.map (inst tyin) | throw "REVERSE_CONV"
      let [pth_init, pth_base, pth_step] ← rev_pths.mapM (INST_TYPE tyin) | throw "REVERSE_CONV"
      let rec rconv (th : thm) : ExceptT String IO thm := do
        let (ahtm, ltm) ← liftExcept (do dest_comb (← rand (concl th)))
        let httm ← liftExcept (do rand (← rand ahtm))
        if is_cons httm then
          let (htm, ttm) ← liftExcept (dest_cons httm)
          let th1 ← INST [(htm, h_tm), (ltm, l_tm), (ttm, t_tm)] pth_step
          rconv (← TRANS th th1)
        else TRANS th (← INST [(ltm, l_tm)] pth_base)
      tryWith (do rconv (← INST [(tm, l_tm)] pth_init)) (throw "REVERSE_CONV")
    | _ => throw "REVERSE_CONV"

  -- LIST_OF_SEQ_CONV (lists.ml 836-876).
  let los_pthc ← prove
   r"l:A list = APPEND l [] /\
     APPEND (list_of_seq f 0) l:A list = l /\
     (n = SUC m
      ==> APPEND (list_of_seq f n) l =
          APPEND (list_of_seq f m) (CONS (f m) l))"
   (SIMP_TAC [D.APPEND, T1.APPEND_NIL, D.list_of_seq, ← GSYM T1.APPEND_ASSOC])
  let los_pths ← (CONJUNCTS los_pthc).mapM UNDISCH_ALL
  let los_avars := sortTerms (frees (concl los_pthc))
  let LIST_OF_SEQ_CONV : ioconv := fun tm => ExceptT.run do
    match tm with
    | .Comb (.Comb (.Const "list_of_seq" _) ftm) _ntm =>
      let tyin := [((← liftExcept (dest_fun_ty (type_of ftm))).2, aty)]
      let [f_tm, l_tm, m_tm, n_tm] := los_avars.map (inst tyin) | throw "LIST_OF_SEQ_CONV"
      let [pth_init, pth_base, pth_step] ← los_pths.mapM (INST_TYPE tyin)
        | throw "LIST_OF_SEQ_CONV"
      let bflag := is_abs ftm
      let rec sconv (th : thm) : ExceptT String IO thm := do
        let (nftm, ltm) ← liftExcept (do dest_comb (← rand (concl th)))
        let (lftm, ntm) ← liftExcept (do dest_comb (← rand nftm))
        let ftm ← liftExcept (rand lftm)
        let n ← liftExcept (dest_numeral ntm)
        if n == num_0 then TRANS th (← INST [(ftm, f_tm), (ltm, l_tm)] pth_base)
        else
          let th1 ← ExceptT.mk (num_CONV ntm)
          let th2 ← INST [(ntm, n_tm), (← liftExcept (do rand (← rand (concl th1))), m_tm),
                          (ftm, f_tm), (ltm, l_tm)] pth_step
          let th3 ← TRANS th (← PROVE_HYP th1 th2)
          let th4 ← if !bflag then pure th3 else do
            let (jtm, ctxtm) ← liftExcept (do dest_comb (← rand (concl th3)))
            let (cttm, xtm) ← liftExcept (dest_comb ctxtm)
            let (ctm, ttm) ← liftExcept (dest_comb cttm)
            TRANS th3 (← AP_TERM jtm (← AP_THM (← AP_TERM ctm
              (← liftExcept (Equal.BETA_CONV ttm))) xtm))
          sconv th4
      tryWith (do sconv (← INST [(tm, l_tm)] pth_init)) (throw "LIST_OF_SEQ_CONV")
    | _ => throw "LIST_OF_SEQ_CONV"

  return { LENGTH_CONV, EL_CONV, REVERSE_CONV, LIST_OF_SEQ_CONV }

/-- `bool_of_term t` (lists.ml 887-891): the truth value denoted by a `T`/`F`
    constant.

    OCaml:
      `match t with
         Const("T",_) -> true
       | Const("F",_) -> false
       | _ -> failwith "bool_of_term"`
    Any other term (including a boolean variable) fails - this is control flow,
    so it is a `.error`, not a partial match. -/
def bool_of_term (t : term) : Except String Bool :=
  match t with
  | .Const "T" _ => .ok true
  | .Const "F" _ => .ok false
  | _ => failwith "bool_of_term"

/-- `code_of_term t` (lists.ml 892-899): the ASCII code (0-255) of an
    `ASCII b0 ... b7` term.

    OCaml:
      `let f,tms = strip_comb t in
       if not(is_const f && fst(dest_const f) = "ASCII")
          || not(length tms = 8) then failwith "code_of_term"
       else
          itlist (fun b f -> if b then 1 + 2 * f else 2 * f)
                 (map bool_of_term (rev tms)) 0`
    The head must be exactly the constant `ASCII` with EXACTLY 8 arguments.
    BIT ORDER (load-bearing): `rev tms` reverses the 8 arguments, then the
    `itlist` folds RIGHT with `\b f. if b then 1+2*f else 2*f` from `0`.  With
    `tms = [a0;...;a7]` the head argument `a0` carries weight `128` and the
    last `a7` weight `1`.  `mk_code` places the bits in the same order, so the
    round-trip is self-consistent and `code_of_term(mk_code 65)` is `65`. -/
def code_of_term (t : term) : Except String Nat := do
  let (f, tms) := strip_comb t
  let headOk : Bool :=
    match dest_const f with
    | .ok (name, _) => is_const f && name == "ASCII"
    | .error _ => false
  if !headOk || !(tms.length == 8) then failwith "code_of_term"
  else do
    -- `map bool_of_term (rev tms)`: reverse first, then read each bit.
    let bs ← tms.reverse.mapM bool_of_term
    -- `itlist (fun b f -> if b then 1 + 2 * f else 2 * f) bs 0`.
    pure (itlist (fun (b : Bool) (acc : Nat) => if b then 1 + 2 * acc else 2 * acc) bs 0)

/-- `char_of_term = Char.chr o code_of_term` (lists.ml 899).

    `o` is the OCaml composition operator; `Char.chr` is Lean `Char.ofNat`.
    This is BOTH the local `char_of_term` AND (per the returned tuple, whose
    first component is `char_of_term`, not `dest_char`) the exported
    `dest_char`. -/
def char_of_term (t : term) : Except String Char := do return Char.ofNat (← code_of_term t)

/-- OCaml `String.escaped`: escape a string using OCaml lexical conventions.
    Printable ASCII (32-126) passes through except `\` and `"`; the control
    chars `\n \t \r \b` use their letter escapes; anything else becomes the
    3-digit decimal escape `\ddd`.  Used by `dest_string`. -/
def stringEscaped (s : String) : String :=
  let esc (c : Char) : String :=
    let n := c.toNat
    if c == '\\' then "\\\\"
    else if c == '"' then "\\\""
    else if c == '\n' then "\\n"
    else if c == '\t' then "\\t"
    else if c == '\r' then "\\r"
    else if n == 8 then "\\b"
    else if n ≥ 32 && n ≤ 126 then String.singleton c
    else
      let d := toString n
      -- pad to three decimal digits, as OCaml's `\ddd`.
      let d := (String.ofList (List.replicate (3 - d.length) '0')) ++ d
      "\\" ++ d
  String.join (s.toList.map esc)

/-- `dest_string tm` (lists.ml 901-908): the string denoted by a `char list`
    term, escaped as OCaml `String.escaped` does.

    OCaml:
      `try let tms = dest_list tm in
           if fst(dest_type(hd(snd(dest_type(type_of tm))))) <> "char"
           then fail() else
           let ccs = map (String.make 1 o char_of_term) tms in
           String.escaped (implode ccs)
       with Failure _ -> failwith "dest_string"`
    `type_of tm` is `char list`, whose sole type argument must be `char`.  The
    `try ... with Failure _` is control flow: EVERY inner failure (a non-list
    term, a wrong element type, a non-`ASCII` element) is normalised to the
    single message `"dest_string"`. -/
def dest_string (tm : term) : Except String String :=
  match (do
      let tms ← dest_list tm
      let (_, tyargs) ← dest_type (type_of tm)
      let elemTy ← hd tyargs
      let (elemName, _) ← dest_type elemTy
      if elemName != "char" then failwith "dest_string"
      else do
        -- `map (String.make 1 o char_of_term) tms`: each element becomes a
        -- one-character string, then `implode` concatenates.
        let ccs ← tms.mapM (fun t => do return String.singleton (← char_of_term t))
        pure (stringEscaped (HolCore.Lib.implode ccs)) : Except String String) with
  | .ok s => .ok s
  | .error _ => failwith "dest_string"

/-- What the `dest_char,mk_char,...,STRING_EQ_CONV` closure (lists.ml
    886-998) builds before returning: `mk_code`'s 256 `ASCII` terms,
    `CHAR_DISTINCTNESS`'s variables and inequality families,
    `STRING_DISTINCTNESS`'s variables and lemmas, and `:char`. -/
structure CharStringMachinery where
  codes       : Array term
  char_ty     : hol_type
  avars       : List term
  bvars       : List term
  cvars       : List term
  asciiNeqsFT : List thm
  asciiNeqsTF : List thm
  xtm         : term
  xstm        : term
  ytm         : term
  ystm        : term
  niltm       : term
  nilEqThm    : thm
  consEqThm   : thm
  consNeqThm  : thm
  nilNeqCons  : thm
  consNeqNil  : thm
  deriving Inhabited

/-- Build the `CharStringMachinery` (lists.ml 909-978).  `injectivity_char`
    is `injectivity "char"`. -/
@[nospecialize]
def setupCharStringMachinery [HolBase] (injectivity_char CONS_11 NOT_CONS_NIL : thm)
    (MESON_TAC : List thm → tactic) : ExceptT String IO CharStringMachinery := do
  let true_tm ← q r"T"
  let false_tm ← q r"F"
  let mk_bool (b : Bool) : term := if b then true_tm else false_tm
  let ascii_tm ← q r"ASCII"
  let mk_code (c : Nat) : Except String term :=
    let lis := (List.range 8).map (fun i => mk_bool ((c / 2 ^ i) % 2 == 1))
    lis.foldrM (fun x y => mk_comb y x) ascii_tm
  let codes := (← liftExcept ((List.range 256).mapM mk_code)).toArray
  let char_ty ← qty r"char"
  let avars ← [r"a0:bool", r"a1:bool", r"a2:bool", r"a3:bool", r"a4:bool", r"a5:bool",
               r"a6:bool"].mapM q
  let bvars ← [r"b1:bool", r"b2:bool", r"b3:bool", r"b4:bool", r"b5:bool", r"b6:bool",
               r"b7:bool"].mapM q
  let cvars ← [r"c1:bool", r"c2:bool", r"c3:bool", r"c4:bool", r"c5:bool", r"c6:bool",
               r"c7:bool"].mapM q
  let asciiNeqsFT ← (CONJUNCTS (← prove
     r"~(ASCII F b1 b2 b3 b4 b5 b6 b7 = ASCII T c1 c2 c3 c4 c5 c6 c7) /\
       ~(ASCII a0 F b2 b3 b4 b5 b6 b7 = ASCII a0 T c2 c3 c4 c5 c6 c7) /\
       ~(ASCII a0 a1 F b3 b4 b5 b6 b7 = ASCII a0 a1 T c3 c4 c5 c6 c7) /\
       ~(ASCII a0 a1 a2 F b4 b5 b6 b7 = ASCII a0 a1 a2 T c4 c5 c6 c7) /\
       ~(ASCII a0 a1 a2 a3 F b5 b6 b7 = ASCII a0 a1 a2 a3 T c5 c6 c7) /\
       ~(ASCII a0 a1 a2 a3 a4 F b6 b7 = ASCII a0 a1 a2 a3 a4 T c6 c7) /\
       ~(ASCII a0 a1 a2 a3 a4 a5 F b7 = ASCII a0 a1 a2 a3 a4 a5 T c7) /\
       ~(ASCII a0 a1 a2 a3 a4 a5 a6 F = ASCII a0 a1 a2 a3 a4 a5 a6 T)"
     (REWRITE_TAC [injectivity_char]))).mapM EQF_INTRO
  let ilist := List.zip bvars cvars ++ List.zip cvars bvars
  let asciiNeqsTF ← asciiNeqsFT.mapM (fun th => do
    EQF_INTRO (← INST ilist (← GSYM (← EQF_ELIM th))))
  let xtm ← q r"x:char"
  let xstm ← q r"xs:string"
  let ytm ← q r"y:char"
  let ystm ← q r"ys:string"
  let niltm ← q r"[]:string"
  let nilEqThm ← EQT_INTRO (REFL niltm)
  let (consEqThm, consNeqThm) ← CONJ_PAIR (← prove
   r"(CONS x xs:string = CONS x ys <=> xs = ys) /\
     ((x = y <=> F) ==> (CONS x xs:string = CONS y ys <=> F))"
   (REWRITE_TAC [CONS_11] THEN MESON_TAC []))
  let (nilNeqCons, consNeqNil) ← CONJ_PAIR (← prove
   r"(NIL:string = CONS x xs <=> F) /\
     (CONS x xs:string = NIL <=> F)"
   (REWRITE_TAC [NOT_CONS_NIL]))
  return { codes, char_ty, avars, bvars, cvars, asciiNeqsFT, asciiNeqsTF,
           xtm, xstm, ytm, ystm, niltm,
           nilEqThm, consEqThm, consNeqThm, nilNeqCons, consNeqNil }

/-- `dest_char` is the closure's `char_of_term` (lists.ml 899, 998). -/
def dest_char : term → Except String Char := char_of_term

/-- `mk_char = mk_code o Char.code` (lists.ml 919). -/
def mk_char (M : CharStringMachinery) (c : Char) : Except String term :=
  match M.codes[c.toNat]? with
  | some t => .ok t
  | none => failwith "mk_char"

/-- `mk_string s` (lists.ml 920-923). -/
def mk_string (M : CharStringMachinery) (s : String) : IO (Except String term) := do
  match s.toList.mapM (mk_char M) with
  | .error e => return .error e
  | .ok tms => mk_list tms M.char_ty

/-- The `findneq` of `CHAR_DISTINCTNESS` (lists.ml 949-953). -/
private def findneq : Nat → List term → List term → List term →
    Except String (Nat × List term × Bool × List term × List term)
  | n, pfx, b1 :: a, b2 :: b =>
    if b1 != b2 then do return (n, pfx.reverse, ← bool_of_term b2, a, b)
    else findneq (n + 1) (b1 :: pfx) a b
  | _, _, _, _ => failwith "findneq"

/-- `CHAR_DISTINCTNESS c1 c2` (lists.ml 954-956). -/
def CHAR_DISTINCTNESS (M : CharStringMachinery) (c1 c2 : term) : Except String thm := do
  let (_, a) := strip_comb c1
  let (_, b) := strip_comb c2
  let (n, p, b, s1, s2) ← findneq 0 [] a b
  let ss1 := M.bvars.drop n
  let ss2 := M.cvars.drop n
  let pp := M.avars.take n
  let pth := if b then M.asciiNeqsFT else M.asciiNeqsTF
  Kernel.INST (List.zip p pp ++ List.zip s1 ss1 ++ List.zip s2 ss2) (← el n pth)

/-- `STRING_DISTINCTNESS s1 s2` (lists.ml 970-978). -/
partial def STRING_DISTINCTNESS [HolBase] (M : CharStringMachinery) (s1 s2 : term) :
    Except String thm := do
  if s1 == M.niltm then
    if s2 == M.niltm then return M.nilEqThm
    let (c2, s2) := (← rand (← rator s2), ← rand s2)
    Kernel.INST [(c2, M.xtm), (s2, M.xstm)] M.nilNeqCons
  else
    let (c1, s1) := (← rand (← rator s1), ← rand s1)
    if s2 == M.niltm then return ← Kernel.INST [(c1, M.xtm), (s1, M.xstm)] M.consNeqNil
    let (c2, s2) := (← rand (← rator s2), ← rand s2)
    if c1 == c2 then
      let th1 ← Kernel.INST [(c1, M.xtm), (s1, M.xstm), (s2, M.ystm)] M.consEqThm
      let th2 ← STRING_DISTINCTNESS M s1 s2
      Kernel.TRANS th1 th2
    else
      let itm ← Kernel.INST [(c1, M.xtm), (c2, M.ytm), (s1, M.xstm), (s2, M.ystm)] M.consNeqThm
      HolBase.B.MP itm (← CHAR_DISTINCTNESS M c1 c2)

/-- `CHAR_EQ_CONV` (lists.ml 980-984). -/
def CHAR_EQ_CONV [HolBase] (M : CharStringMachinery) : Equal.conv := fun tm => do
  let (c1, c2) ← dest_eq tm
  if compare c1 c2 == Ordering.eq then HolBase.B.EQT_INTRO (REFL c1) else CHAR_DISTINCTNESS M c1 c2

/-- `STRING_EQ_CONV` (lists.ml 985-988). -/
def STRING_EQ_CONV [HolBase] (M : CharStringMachinery) : Equal.conv := fun tm => do
  let (ltm, rtm) ← dest_eq tm
  if compare ltm rtm == Ordering.eq then HolBase.B.EQT_INTRO (REFL ltm) else STRING_DISTINCTNESS M ltm rtm

end

end HolMath.Lists
