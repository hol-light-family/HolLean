/- File: HolExamples/RecTypes.lean
Translation of HOL Light's Examples/rectypes.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace HolExamples.RecTypes

/- `time define_type s`: as the OCaml toplevel runs it.  `define_type` is
   IO-valued (`IO (Except String (thm × thm))`); `time` reports the CPU time
   (masked by compare.py) and the (coerced) call fails loudly on an error. -/
private unsafe def timeDefineType (s : String) : IO (thm × thm) :=
  HolCore.Lib.time (fun _ => do
    match ← define_type s with
    | .ok v => pure v
    | .error e => throw (IO.userError e)) ()

/- A print-only `time define_type` phrase prints `val it : thm * thm = (...)`;
   compare.py strips the `val it : thm * thm =` prefix and all whitespace, so
   we print the OCaml pair layout `(|- ...,\n   |- ...)`. -/
private unsafe def printPair (p : thm × thm) : IO Unit := do
  IO.println s!"({← HolCore.Printer.string_of_thm p.1},\n   {← HolCore.Printer.string_of_thm p.2})"

/- A named `let x_INDUCTION,x_RECURSION = time define_type` phrase prints
   `val x_INDUCTION : thm = |- ...` and `val x_RECURSION : thm = |- ...`;
   compare.py strips the `val x : thm =` prefixes. -/
private unsafe def printTwo (p : thm × thm) : IO Unit := do
  IO.println (← HolCore.Printer.string_of_thm p.1)
  IO.println (← HolCore.Printer.string_of_thm p.2)

-- ========================================================================= --
-- Some (mutually, nested) recursive types from various sources.             --
-- ========================================================================= --

#eval phrase 1
#eval (do printPair (← timeDefineType
  "Term = Var A B | App bool Termlist;
              Termlist = Empty | Consp Term Termlist") : IO Unit)

#eval phrase 2
#eval (do printPair (← timeDefineType "List = Nil | Cons A List") : IO Unit)

#eval phrase 3
#eval (do printPair (← timeDefineType "Btree = Leaf A | Node B Btree Btree") : IO Unit)

#eval phrase 4
#eval (do printPair (← timeDefineType
  "Command = Assign ind Expression
                    | If Expression Command
                    | Ite Expression Command Command
                    | While Expression Command
                    | Do Command Expression;
            Expression = Constant num
                       | Variable ind
                       | Summ Expression Expression
                       | Product Expression Expression") : IO Unit)

#eval phrase 5
#eval (do printPair (← timeDefineType
  "testa = empty_testa | cons_testa testa testb;
            testb = contentb L testc;
            testc = connection M testa") : IO Unit)

#eval phrase 6
#eval (do printPair (← timeDefineType
  "atexp = Varb ind | Let dec exp;
            exp   = Exp1 atexp | Exp2 exp atexp | Exp3 matching;
            matching = Match1 rule | Matches rule matching;
            rule  = Rule pat exp;
            dec   = Val valbind | Local dec dec | Decs dec dec;
            valbind = Single pat exp | Multi pat exp valbind | Rec valbind;
            pat = Wild | Varpat ind") : IO Unit)

#eval phrase 7
#eval (do printPair (← timeDefineType "tri = ONE | TWO | THREE") : IO Unit)

-- ------------------------------------------------------------------------- --
-- A couple from Steve Brackin's work.                                       --
-- ------------------------------------------------------------------------- --

#eval phrase 8
#eval (do printPair (← timeDefineType
  "T = X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 |
                X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 | X21 |
                X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | X31 |
                X32 | X33 | X34") : IO Unit)

#eval phrase 9
#eval (do printPair (← timeDefineType
  "TY1 = NoF__ | Fk__ A TY2;
            TY2 = Ta__ bool | Td__ bool | Tf__ TY1 | Tk__ bool | Tp__ bool
                | App__ A TY1 TY2 TY3 | Pair__ TY2 TY2;
            TY3 = NoS__ | Fresh__ TY2 | Trustworthy__ A
                | PrivateKey__ A B C | PublicKey__ A B C
                | Conveyed__ A TY2 | Possesses__ A TY2 | Received__ A TY2
                | Recognizes__ A TY2 | NeverMalFromSelf__ A B TY2
                | Sends__ A TY2 B | SharedSecret__ A TY2 B
                | Believes__ A TY3 | And__ TY3 TY3") : IO Unit)

-- ------------------------------------------------------------------------- --
-- Some with nesting of various kinds, plus required auxiliaries.            --
-- ------------------------------------------------------------------------- --

#eval phrase 10
unsafe def term_INDUCTION_term_RECURSION : thm × thm := keep "term_types" fun _ =>
  match unsafeIO (timeDefineType
    "term = Vari int | Fni int (term list)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def term_INDUCTION : thm := term_INDUCTION_term_RECURSION.1
unsafe def term_RECURSION : thm := term_INDUCTION_term_RECURSION.2
#eval (printTwo term_INDUCTION_term_RECURSION : IO Unit)

#eval phrase 11
unsafe def bintree_INDUCTION_bintree_RECURSION : thm × thm := keep "bintree_types" fun _ =>
  match unsafeIO (timeDefineType
    "bintree = Leafb | Branchb (bintree # bintree)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def bintree_INDUCTION : thm := bintree_INDUCTION_bintree_RECURSION.1
unsafe def bintree_RECURSION : thm := bintree_INDUCTION_bintree_RECURSION.2
#eval (printTwo bintree_INDUCTION_bintree_RECURSION : IO Unit)

#eval phrase 12
unsafe def etree_INDUCTION_etree_RECURSION : thm × thm := keep "etree_types" fun _ =>
  match unsafeIO (timeDefineType
    "etree = Terminal | Nonterminal (num + etree)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def etree_INDUCTION : thm := etree_INDUCTION_etree_RECURSION.1
unsafe def etree_RECURSION : thm := etree_INDUCTION_etree_RECURSION.2
#eval (printTwo etree_INDUCTION_etree_RECURSION : IO Unit)

#eval phrase 13
unsafe def ptree_INDUCTION_ptree_RECURSION : thm × thm := keep "ptree_types" fun _ =>
  match unsafeIO (timeDefineType
    "ptree = Only (ptree option)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def ptree_INDUCTION : thm := ptree_INDUCTION_ptree_RECURSION.1
unsafe def ptree_RECURSION : thm := ptree_INDUCTION_ptree_RECURSION.2
#eval (printTwo ptree_INDUCTION_ptree_RECURSION : IO Unit)

#eval phrase 14
unsafe def mut_INDUCTION_mut_RECURSION : thm × thm := keep "mut_types" fun _ =>
  match unsafeIO (timeDefineType
    "mutual = Mutual A mutual D otherone | Friend D otherone;
   otherone = Great C | Expectations mutual otherone") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def mut_INDUCTION : thm := mut_INDUCTION_mut_RECURSION.1
unsafe def mut_RECURSION : thm := mut_INDUCTION_mut_RECURSION.2
#eval (printTwo mut_INDUCTION_mut_RECURSION : IO Unit)

#eval phrase 15
unsafe def groof_INDUCTION_groof_RECURSION : thm × thm := keep "groof_types" fun _ =>
  match unsafeIO (timeDefineType
    "groof = Wu bool
         | Wibble (A,groof,L)mutual
         | Wobble groof groof") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def groof_INDUCTION : thm := groof_INDUCTION_groof_RECURSION.1
unsafe def groof_RECURSION : thm := groof_INDUCTION_groof_RECURSION.2
#eval (printTwo groof_INDUCTION_groof_RECURSION : IO Unit)

#eval phrase 16
unsafe def biterm_INDUCTION_biterm_RECURSION : thm × thm := keep "biterm_types" fun _ =>
  match unsafeIO (timeDefineType
    "biterm = Variab int
          | Fnapp (biterm list + biterm list)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def biterm_INDUCTION : thm := biterm_INDUCTION_biterm_RECURSION.1
unsafe def biterm_RECURSION : thm := biterm_INDUCTION_biterm_RECURSION.2
#eval (printTwo biterm_INDUCTION_biterm_RECURSION : IO Unit)

#eval phrase 17
unsafe def triterm_INDUCTION_triterm_RECURSION : thm × thm := keep "triterm_types" fun _ =>
  match unsafeIO (timeDefineType
    "triterm = Var0 int
          | Fun2 (triterm list + triterm list)
          | Fun1 (triterm list)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def triterm_INDUCTION : thm := triterm_INDUCTION_triterm_RECURSION.1
unsafe def triterm_RECURSION : thm := triterm_INDUCTION_triterm_RECURSION.2
#eval (printTwo triterm_INDUCTION_triterm_RECURSION : IO Unit)

#eval phrase 18
unsafe def xtree_INDUCTION_xtree_RECURSION : thm × thm := keep "xtree_types" fun _ =>
  match unsafeIO (timeDefineType
    "xtree = Leafx A
           | Branchx (xtree list)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def xtree_INDUCTION : thm := xtree_INDUCTION_xtree_RECURSION.1
unsafe def xtree_RECURSION : thm := xtree_INDUCTION_xtree_RECURSION.2
#eval (printTwo xtree_INDUCTION_xtree_RECURSION : IO Unit)

#eval phrase 19
unsafe def simper_INDUCTION_simper_RECURSION : thm × thm := keep "simper_types" fun _ =>
  match unsafeIO (timeDefineType
    "simper = Leaves A B
          | Bough (simper xtree)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def simper_INDUCTION : thm := simper_INDUCTION_simper_RECURSION.1
unsafe def simper_RECURSION : thm := simper_INDUCTION_simper_RECURSION.2
#eval (printTwo simper_INDUCTION_simper_RECURSION : IO Unit)

#eval phrase 20
unsafe def array_INDUCTION_array_RECURSION : thm × thm := keep "array_types" fun _ =>
  match unsafeIO (timeDefineType
    "array = Array num (A list)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def array_INDUCTION : thm := array_INDUCTION_array_RECURSION.1
unsafe def array_RECURSION : thm := array_INDUCTION_array_RECURSION.2
#eval (printTwo array_INDUCTION_array_RECURSION : IO Unit)

#eval phrase 21
unsafe def value_INDUCTION_value_RECURSION : thm × thm := keep "value_types" fun _ =>
  match unsafeIO (timeDefineType
    "value = Integer num
         | Boolean bool
         | List_of (value list)
         | Tree_of (value xtree)
         | Array_of (value array)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def value_INDUCTION : thm := value_INDUCTION_value_RECURSION.1
unsafe def value_RECURSION : thm := value_INDUCTION_value_RECURSION.2
#eval (printTwo value_INDUCTION_value_RECURSION : IO Unit)

#eval phrase 22
unsafe def example_INDUCTION_example_RECURSION : thm × thm := keep "example_types" fun _ =>
  match unsafeIO (timeDefineType
    "command = Assignment (num list # expression list)
           | Sequence (command list);
   expression = Numeral num
              | Plus (expression # expression)
              | Valof command") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def example_INDUCTION : thm := example_INDUCTION_example_RECURSION.1
unsafe def example_RECURSION : thm := example_INDUCTION_example_RECURSION.2
#eval (printTwo example_INDUCTION_example_RECURSION : IO Unit)

#eval phrase 23
unsafe def zonk_INDUCTION_zonk_RECURSION : thm × thm := keep "zonk_types" fun _ =>
  match unsafeIO (timeDefineType
    "zonk = Stonk ((zonk,pink,A)mutual)list # expression
        | Tonk zonk (pink list)
        | Honk num;
   pink = Floyd (zonk # pink)
        | Purple num
        | Rain (A # pink)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def zonk_INDUCTION : thm := zonk_INDUCTION_zonk_RECURSION.1
unsafe def zonk_RECURSION : thm := zonk_INDUCTION_zonk_RECURSION.2
#eval (printTwo zonk_INDUCTION_zonk_RECURSION : IO Unit)

-- ------------------------------------------------------------------------- --
-- Example from Konrad Slind: 68000 instruction set.                         --
-- ------------------------------------------------------------------------- --

#eval phrase 24
#eval (do printPair (← timeDefineType "Size = Byte | Word | Long") : IO Unit)

#eval phrase 25
#eval (do printPair (← timeDefineType
  "DataRegister
              = RegD0
              | RegD1
              | RegD2
              | RegD3
              | RegD4
              | RegD5
              | RegD6
              | RegD7") : IO Unit)

#eval phrase 26
#eval (do printPair (← timeDefineType
  "AddressRegister
              = RegA0
              | RegA1
              | RegA2
              | RegA3
              | RegA4
              | RegA5
              | RegA6
              | RegA7") : IO Unit)

#eval phrase 27
#eval (do printPair (← timeDefineType
  "DataOrAddressRegister
              = data DataRegister
              | address AddressRegister") : IO Unit)

#eval phrase 28
#eval (do printPair (← timeDefineType
  "Condition
              = Hi
              | Ls
              | Cc
              | Cs
              | Ne
              | Eq
              | Vc
              | Vs
              | Pl
              | Mi
              | Ge
              | Lt
              | Gt
              | Le") : IO Unit)

#eval phrase 29
#eval (do printPair (← timeDefineType
  "AddressingMode
        = immediate num
        | direct DataOrAddressRegister
        | indirect AddressRegister
        | postinc AddressRegister
        | predec AddressRegister
        | indirectdisp num AddressRegister
        | indirectindex num AddressRegister DataOrAddressRegister Size
        | absolute num
        | pcdisp num
        | pcindex num DataOrAddressRegister Size") : IO Unit)

#eval phrase 30
#eval (do printPair (← timeDefineType
  "M68kInstruction
    = ABCD AddressingMode AddressingMode
    | ADD Size AddressingMode AddressingMode
    | ADDA Size AddressingMode AddressRegister
    | ADDI Size num AddressingMode
    | ADDQ Size num AddressingMode
    | ADDX Size AddressingMode AddressingMode
    | AND Size AddressingMode AddressingMode
    | ANDI Size num AddressingMode
    | ANDItoCCR num
    | ANDItoSR num
    | ASL Size AddressingMode DataRegister
    | ASLW AddressingMode
    | ASR Size AddressingMode DataRegister
    | ASRW AddressingMode
    | Bcc Condition Size num
    | BTST Size AddressingMode AddressingMode
    | BCHG Size AddressingMode AddressingMode
    | BCLR Size AddressingMode AddressingMode
    | BSET Size AddressingMode AddressingMode
    | BRA Size num
    | BSR Size num
    | CHK AddressingMode DataRegister
    | CLR Size AddressingMode
    | CMP Size AddressingMode DataRegister
    | CMPA Size AddressingMode AddressRegister
    | CMPI Size num AddressingMode
    | CMPM Size AddressRegister AddressRegister
    | DBT DataRegister num
    | DBF DataRegister num
    | DBcc Condition DataRegister num
    | DIVS AddressingMode DataRegister
    | DIVU AddressingMode DataRegister
    | EOR Size DataRegister AddressingMode
    | EORI Size num AddressingMode
    | EORItoCCR num
    | EORItoSR num
    | EXG DataOrAddressRegister DataOrAddressRegister
    | EXT Size DataRegister
    | ILLEGAL
    | JMP AddressingMode
    | JSR AddressingMode
    | LEA AddressingMode AddressRegister
    | LINK AddressRegister num
    | LSL Size AddressingMode DataRegister
    | LSLW AddressingMode
    | LSR Size AddressingMode DataRegister
    | LSRW AddressingMode
    | MOVE Size AddressingMode AddressingMode
    | MOVEtoCCR AddressingMode
    | MOVEtoSR AddressingMode
    | MOVEfromSR AddressingMode
    | MOVEtoUSP AddressingMode
    | MOVEfromUSP AddressingMode
    | MOVEA Size AddressingMode AddressRegister
    | MOVEMto Size AddressingMode DataOrAddressRegister list
    | MOVEMfrom Size DataOrAddressRegister list AddressingMode
    | MOVEP Size AddressingMode AddressingMode
    | MOVEQ num DataRegister
    | MULS AddressingMode DataRegister
    | MULU AddressingMode DataRegister
    | NBCD AddressingMode
    | NEG Size AddressingMode
    | NEGX Size AddressingMode
    | NOP
    | NOT Size AddressingMode
    | OR Size AddressingMode AddressingMode
    | ORI Size num AddressingMode
    | ORItoCCR num
    | ORItoSR num
    | PEA AddressingMode
    | RESET
    | ROL Size AddressingMode DataRegister
    | ROLW AddressingMode
    | ROR Size AddressingMode DataRegister
    | RORW AddressingMode
    | ROXL Size AddressingMode DataRegister
    | ROXLW AddressingMode
    | ROXR Size AddressingMode DataRegister
    | ROXRW AddressingMode
    | RTE
    | RTR
    | RTS
    | SBCD AddressingMode AddressingMode
    | ST AddressingMode
    | SF AddressingMode
    | Scc Condition AddressingMode
    | STOP num
    | SUB Size AddressingMode AddressingMode
    | SUBA Size AddressingMode AddressingMode
    | SUBI Size num AddressingMode
    | SUBQ Size num AddressingMode
    | SUBX Size AddressingMode AddressingMode
    | SWAP DataRegister
    | TAS AddressingMode
    | TRAP num
    | TRAPV
    | TST Size AddressingMode
    | UNLK AddressRegister") : IO Unit)

-- ------------------------------------------------------------------------- --
-- Example from Myra VanInwegen: part of the syntax of SML.                  --
-- ------------------------------------------------------------------------- --

#eval phrase 31
unsafe def string_INDUCTION_string_RECURSION : thm × thm := keep "string_types" fun _ =>
  match unsafeIO (timeDefineType
    "string = EMPTY_STRING | CONS_STRING num string") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def string_INDUCTION : thm := string_INDUCTION_string_RECURSION.1
unsafe def string_RECURSION : thm := string_INDUCTION_string_RECURSION.2
#eval (printTwo string_INDUCTION_string_RECURSION : IO Unit)

#eval phrase 32
unsafe def strid_INDUCTION_strid_RECURSION : thm × thm := keep "strid_types" fun _ =>
  match unsafeIO (timeDefineType
    "strid = STRID string;
   var = VAR string;
   con = CON string;
   scon = SCINT int | SCSTR string;
   excon = EXCON string;
   label = LABEL string") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def strid_INDUCTION : thm := strid_INDUCTION_strid_RECURSION.1
unsafe def strid_RECURSION : thm := strid_INDUCTION_strid_RECURSION.2
#eval (printTwo strid_INDUCTION_strid_RECURSION : IO Unit)

#eval phrase 33
unsafe def nonemptylist_INDUCTION_nonemptylist_RECURSION : thm × thm := keep "nonemptylist_types" fun _ =>
  match unsafeIO (timeDefineType
    "nonemptylist = Head_and_tail A (A list)") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def nonemptylist_INDUCTION : thm := nonemptylist_INDUCTION_nonemptylist_RECURSION.1
unsafe def nonemptylist_RECURSION : thm := nonemptylist_INDUCTION_nonemptylist_RECURSION.2
#eval (printTwo nonemptylist_INDUCTION_nonemptylist_RECURSION : IO Unit)

#eval phrase 34
unsafe def long_INDUCTION_long_RECURSION : thm × thm := keep "long_types" fun _ =>
  match unsafeIO (timeDefineType
    "long = BASE A | QUALIFIED strid long") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def long_INDUCTION : thm := long_INDUCTION_long_RECURSION.1
unsafe def long_RECURSION : thm := long_INDUCTION_long_RECURSION.2
#eval (printTwo long_INDUCTION_long_RECURSION : IO Unit)

#eval phrase 35
unsafe def myra_INDUCTION_myra_RECURSION : thm × thm := keep "myra_types" fun _ =>
  match unsafeIO (timeDefineType
    "atpat_e = WILDCARDatpat_e
           | SCONatpat_e scon
           | VARatpat_e var
           | CONatpat_e (con long)
           | EXCONatpat_e (excon long)
           | RECORDatpat_e (patrow_e option)
           | PARatpat_e pat_e;

   patrow_e = DOTDOTDOT_e
            | PATROW_e label pat_e (patrow_e option);

   pat_e = ATPATpat_e atpat_e
         | CONpat_e (con long) atpat_e
         | EXCONpat_e (excon long) atpat_e
         | LAYEREDpat_e var pat_e;

   conbind_e = CONBIND_e con (conbind_e option);

   datbind_e = DATBIND_e conbind_e (datbind_e option);

   exbind_e = EXBIND1_e excon (exbind_e option)
            | EXBIND2_e excon (excon long) (exbind_e option);

   atexp_e = SCONatexp_e scon
           | VARatexp_e (var long)
           | CONatexp_e (con long)
           | EXCONatexp_e (excon long)
           | RECORDatexp_e (exprow_e option)
           | LETatexp_e dec_e exp_e
           | PARatexp_e exp_e;

   exprow_e = EXPROW_e label exp_e (exprow_e option);

   exp_e = ATEXPexp_e atexp_e
         | APPexp_e exp_e atexp_e
         | HANDLEexp_e exp_e match_e
         | RAISEexp_e exp_e
         | FNexp_e match_e;

   match_e = MATCH_e mrule_e (match_e option);

   mrule_e = MRULE_e pat_e exp_e;

   dec_e = VALdec_e valbind_e
         | DATATYPEdec_e datbind_e
         | ABSTYPEdec_e datbind_e dec_e
         | EXCEPTdec_e exbind_e
         | LOCALdec_e dec_e dec_e
         | OPENdec_e ((strid long) nonemptylist)
         | EMPTYdec_e
         | SEQdec_e dec_e dec_e;

   valbind_e = PLAINvalbind_e pat_e exp_e (valbind_e option)
             | RECvalbind_e valbind_e") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def myra_INDUCTION : thm := myra_INDUCTION_myra_RECURSION.1
unsafe def myra_RECURSION : thm := myra_INDUCTION_myra_RECURSION.2
#eval (printTwo myra_INDUCTION_myra_RECURSION : IO Unit)

-- ------------------------------------------------------------------------- --
-- Example from Daryl Stewart: a Verilog grammar.                            --
-- ------------------------------------------------------------------------- --

#eval phrase 36
unsafe def daryl_INDUCTION_daryl_RECURSION : thm × thm := keep "daryl_types" fun _ =>
  match unsafeIO (timeDefineType
    "Source_text
     = module string (string list) (Module_item list)
     | Source_textMeta string;
  Module_item
     = declaration Declaration
     | initial Statement
     | always Statement
     | assign Lvalue Exprn
     | Module_itemMeta string;
  Declaration
     = reg_declaration (Range option) (string list)
     | net_declaration (Range option) (string list)
     | input_declaration (Range option) (string list)
     | output_declaration (Range option) (string list)
     | DeclarationMeta string;
  Range = range Exprn Exprn | RangeMeta string;
  Statement
     = clock_statement Clock Statement_or_null
     | blocking_assignment Lvalue Exprn
     | non_blocking_assignment Lvalue Exprn
     | conditional_statement
          Exprn Statement_or_null (Statement_or_null option)
     | case_statement Exprn (Case_item list)
     | while_loop Exprn Statement
     | repeat_loop Exprn Statement
     | for_loop
          Lvalue Exprn Exprn Lvalue Exprn Statement
     | forever_loop Statement
     | disable string
     | seq_block (string option) (Statement list)
     | StatementMeta string;
  Statement_or_null
     = statement Statement | null_statement | Statement_or_nullMeta string;
  Clock
     = posedge string
     | negedge string
     | clock string
     | ClockMeta string;
  Case_item
     = case_item (Exprn list) Statement_or_null
     | default_case_item Statement_or_null
     | Case_itemMeta string;
  Exprn
     = plus Exprn Exprn
     | minus Exprn Exprn
     | lshift Exprn Exprn
     | rshift Exprn Exprn
     | lt Exprn Exprn
     | leq Exprn Exprn
     | gt Exprn Exprn
     | geq Exprn Exprn
     | logeq Exprn Exprn
     | logneq Exprn Exprn
     | caseeq Exprn Exprn
     | caseneq Exprn Exprn
     | bitand Exprn Exprn
     | bitxor Exprn Exprn
     | bitor Exprn Exprn
     | logand Exprn Exprn
     | logor Exprn Exprn
     | conditional Exprn Exprn Exprn
     | positive Primary
     | negative Primary
     | lognot Primary
     | bitnot Primary
     | reducand Primary
     | reducxor Primary
     | reducor Primary
     | reducnand Primary
     | reducxnor Primary
     | reducnor Primary
     | primary Primary
     | ExpressionMeta string;
  Primary
     = primary_number Number
     | primary_IDENTIFIER string
     | primary_bit_select string Exprn
     | primary_part_select string Exprn Exprn
     | primary_gen_bit_select Exprn Exprn
     | primary_gen_part_select Exprn Exprn Exprn
     | primary_concatenation Concatenation
     | primary_multiple_concatenation Multiple_concatenation
     | brackets Exprn
     | PrimaryMeta string;
  Lvalue
     = lvalue string
     | lvalue_bit_select string Exprn
     | lvalue_part_select string Exprn Exprn
     | lvalue_concatenation Concatenation
     | LvalueMeta string;
  Number
     = decimal string
     | based string option string
     | NumberMeta string;
  Concatenation
     = concatenation (Exprn list) | ConcatenationMeta string;
  Multiple_concatenation
     = multiple_concatenation Exprn (Exprn list)
     | Multiple_concatenationMeta string;
  meta
     = Meta_Source_text Source_text
     | Meta_Module_item Module_item
     | Meta_Declaration Declaration
     | Meta_Range Range
     | Meta_Statement Statement
     | Meta_Statement_or_null Statement_or_null
     | Meta_Clock Clock
     | Meta_Case_item Case_item
     | Meta_Expression Exprn
     | Meta_Primary Primary
     | Meta_Lvalue Lvalue
     | Meta_Number Number
     | Meta_Concatenation Concatenation
     | Meta_Multiple_concatenation Multiple_concatenation") with
  | .ok p => p | .error e => panic! (toString e)
unsafe def daryl_INDUCTION : thm := daryl_INDUCTION_daryl_RECURSION.1
unsafe def daryl_RECURSION : thm := daryl_INDUCTION_daryl_RECURSION.2
#eval (printTwo daryl_INDUCTION_daryl_RECURSION : IO Unit)

end HolExamples.RecTypes
