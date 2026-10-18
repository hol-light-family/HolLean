/- File: HolExamples/BitBlastGeneric.lean
Translation of HOL Light's Examples/bitblast_generic.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.WordAutomata

namespace HolExamples.BitBlastGeneric

-- (* ========================================================================= *)
-- (* Examples of automata-based generic bitblasting                            *)
-- (* ========================================================================= *)

#eval phrase 1
-- needs "Library/word_automata.ml";;
#eval SessionLibrary.WordAutomata.ensureWordAutomata

-- (* ------------------------------------------------------------------------- *)
-- (* Misc examples, many originating in LLVM optimization.                     *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 2
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!(z:(N)word) (c:(N)word).
      word_and c (word 1) = word 0
      ==> word_xor (word_and z c) (word_or c (word 1)) =
          word_neg (word_or z (word_not c))]] : IO (Except String thm))

#eval phrase 3
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!(z:(N)word) (c:(N)word).
          word_xor (word_and z c) (word_or c (word 1)) =
          word_neg (word_or z (word_not c)) <=>
          word_and c (word 1) = word 0]] : IO (Except String thm))

#eval phrase 4
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!(z:(N)word) (c:(N)word).
      (word_add (word_xor (word_or z (word_not c)) c) (word 1)) =
      (word_neg (word_and z c))]] : IO (Except String thm))

#eval phrase 5
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!(z:(N)word) (c:(N)word).
      word_add (word_xor (word_and z c) c) (word 1) =
      word_neg (word_or z (word_not c))]] : IO (Except String thm))

#eval phrase 6
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!(x:(N)word) (y:(N)word).
      word_add (word_add x (word 1)) (word_not y) =
      word_sub x y]] : IO (Except String thm))

#eval phrase 7
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!(x:(N) word) (y:(N)word).
      word_add (word_not x) (word_not y) =
      word_sub (word_sub (word 0) (word 2)) (word_add x y)]] : IO (Except String thm))

#eval phrase 8
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!(x:(N)word) (c1:(N)word) (c2:(N)word).
    (c2 = (word_neg c1))
    ==> (word_add (word_or x (c2)) (c1)) = (word_xor (word_or x (c2)) (c2))]] : IO (Except String thm))

#eval phrase 9
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!(x:N word) c1 c2.
      word_and c2 (word_sub c2 (word 1)) = word 0 /\
      word_and c1 (word_sub c2 (word 1)) = word 0 /\
      ~(word_and c1 c2 = word 0)
      ==> word_and (word_add x c1) c2 = word_xor (word_and x c2) c2]] : IO (Except String thm))

#eval phrase 10
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word.
       word_and (word_not x) (word_sub x (word 1)) =
       word_not (word_or x (word_neg x))]] : IO (Except String thm))

#eval phrase 11
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. word_and x (word_not(word 1)) = word 0 <=>
               x = word 0 \/ x = word 1]] : IO (Except String thm))

#eval phrase 12
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[word_xor x y:S word  = word_sub (word_or x y) (word_and x y)]] : IO (Except String thm))

#eval phrase 13
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[word_add x y:M word = word_sub (word_shl (word_or x y) 1) (word_xor x y)]] : IO (Except String thm))

#eval phrase 14
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:R word. word_and x (word_sub x (word 1)) = word 0 /\
                word_and x (word_not(word 1)) = word 0
                <=> x = word 0 \/ x = word 1]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Characterizing the top bit                                                *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 15
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!b x:N word. ~(b = word 0) /\ word_shl b 1 = word 0
                  ==> (~(x = word 0) <=>
                       word_and b (word_or x (word_neg x)) = b)]] : IO (Except String thm))

#eval phrase 16
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!b x:N word. ~(b = word 0) /\ word_shl b 1 = word 0
                  ==> (x = word 0 <=>
                       word_and b (word_or x (word_neg x)) = word 0)]] : IO (Except String thm))

#eval phrase 17
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!b c:N word. ~(b = word 0) /\ word_shl b 1 = word 0 /\
                 word_add c (word 1) = word_not c /\ ~(c = word_not(word 0))
                 ==> b = word_not c]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Sign swaps.                                                               *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 18
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!m x:N word. m = word_neg(word_and b (word 1))
                 ==> word_sub (word_xor x m) m = word_xor (word_add x m) m]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Trivial example with multiple shifts.                                     *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 19
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. word_and (word 3) (word_shl x 2) = word 0]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Trivial example with constant multiplication.                             *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 20
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. word_and (word 3) (word_mul (word 5) x) =
                word_and x (word 3)]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Simple examples with right shifts.                                        *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 21
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:R word. word_xor x (word_ushr x 1) = word_xor y (word_ushr y 1) <=>
                 x = y]] : IO (Except String thm))

#eval phrase 22
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:M word. word_and (word_xor (word_add (word_ushr x 2) (word_ushr x 2))
                                  (word_ushr x 1))
                        (word_not(word 1)) = word 0]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Two versions of non-overflowing average                                   *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 23
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word. word_add (word_and x y) (word_ushr (word_xor x y) 1) =
                 word_add (word_add (word_ushr x 1) (word_ushr y 1))
                          (word_and (word 1) (word_and x y))]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Trivial things with orderings.                                            *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 24
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y z:N word.
          word_ule x y /\ word_ule y z ==> word_ule x z]] : IO (Except String thm))

#eval phrase 25
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y z:N word.
          word_ule x y /\ word_ult y z ==> word_ugt z x]] : IO (Except String thm))

#eval phrase 26
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y z:N word.
          word_ile x y /\ word_ile y z ==> word_ile x z]] : IO (Except String thm))

#eval phrase 27
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y z:N word.
          word_ile x y /\ word_ilt y z ==> word_igt z x]] : IO (Except String thm))

#eval phrase 28
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word.
          word_ushr (word_shl x 1) 1 = x /\
          word_ushr (word_shl y 1) 1 = y
          ==> (word_ule x y <=> word_ile x y)]] : IO (Except String thm))

#eval phrase 29
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word. word_ule (word_and x y) x]] : IO (Except String thm))

#eval phrase 30
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word. word_ule (word_xor x y) (word_or x y)]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Random things from Hacker's Delight.                                      *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 31
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. word_not(word_or x (word_neg x)) =
               word_sub (word_and x (word_neg x)) (word 1)]] : IO (Except String thm))

#eval phrase 32
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. word_and (word_add (word_or x (word_sub x (word 1))) (word 1)) x =
               word_and (word_add (word_and x (word_neg x)) x) x]] : IO (Except String thm))

#eval phrase 33
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. word_not(word_add x y) = word_sub (word_not x) y]] : IO (Except String thm))

#eval phrase 34
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word. word_or x y = word_add (word_and x (word_not y)) y]] : IO (Except String thm))

#eval phrase 35
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word. word_sub x y =
                 word_sub (word_mul (word 2) (word_and x (word_not y)))
                          (word_xor x y)]] : IO (Except String thm))

#eval phrase 36
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word.
          word_ilt x y <=>
          ~(word_and word_INT_MIN
             (word_sub (word_sub (word_ishr x 1) (word_ishr y 1))
                       (word_and (word_and (word_not x) y) (word 1))) =
            word 0)]] : IO (Except String thm))

#eval phrase 37
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word.
          word_ult x y <=>
          ~(word_and word_INT_MIN
             (word_sub (word_sub (word_ushr x 1) (word_ushr y 1))
                       (word_and (word_and (word_not x) y) (word 1))) =
            word 0)]] : IO (Except String thm))

#eval phrase 38
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. ~(x = word 0) <=> ival(word_or x (word_neg x)) < &0]] : IO (Except String thm))

#eval phrase 39
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x y:N word. x = y <=> ival(word_or (word_sub x y) (word_sub y x)) >= &0]] : IO (Except String thm))

#eval phrase 40
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. word_igt x (word 0) <=>
               ival (word_sub (word_ishr x 1) x) < &0]] : IO (Except String thm))

#eval phrase 41
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!x:N word. word_igt x (word 0) <=>
               ival (word_and (word_neg x) (word_not x)) < &0]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Bounds checking.                                                          *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 42
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!a b x:N word.
          word_ile a b
          ==> (word_ile a x /\ word_ile x b <=>
               word_ule (word_sub x a) (word_sub b a))]] : IO (Except String thm))

#eval phrase 43
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[!a b x:N word.
          word_ile a b
          ==> (word_ile a x /\ word_ilt x b <=>
               word_ult (word_sub x a) (word_sub b a))]] : IO (Except String thm))

-- (* ------------------------------------------------------------------------- *)
-- (* Using xor as alternative to subtraction.                                  *)
-- (* ------------------------------------------------------------------------- *)

#eval phrase 44
#eval (HolCore.Lib.time WORD_AUTO_RULE
  [[val(x:N word) < val(word 64:N word)
     ==> word_sub (word 63) x = word_xor x (word 63)]] : IO (Except String thm))

end HolExamples.BitBlastGeneric
